/* manyan: a TLA+ model checker, with TLC as its oracle.

   The language and the results it must produce are defined by
   docs/standards/tla2.md; section numbers below (§) refer to it.

   A run reads the root module and the modules it uses (lexer, parser),
   resolves names (resolver), binds the constants from the configuration,
   and explores the state graph breadth first (checker), evaluating
   expressions (evaluator) and enumerating the states an initial predicate
   or an action allows (generator). Worker processes may expand the
   states of a level in parallel; the search merges what they find in
   order, so the result is the same with any number of them. */
#define _DEFAULT_SOURCE
#define _DARWIN_C_SOURCE
#include "manyan.h"

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <poll.h>
#include <sched.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <strings.h>
#include <time.h>
#include <stdatomic.h>
#include <sys/mman.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

typedef struct ManyanValue Value;
typedef struct Expr Expr;
typedef struct Def Def;
typedef struct Module Module;
typedef struct Env Env;
typedef struct Inst Inst;

/* ---------------------------------------------------------------- memory */

/* Values and expressions live in arenas. The permanent arena holds the
   modules and everything computed before the search; the scratch arena
   holds what the search computes for one state and is reset after it. */
typedef struct Chunk { struct Chunk *next; size_t used, size; _Alignas(16) char data[]; } Chunk;   /* data as aligned as an __int128 */
typedef struct { Chunk *head, *spare; } Arena;   /* spare: a chunk a region dropped, for the next */

static Arena perm_arena, scratch_arena;
static Arena *arena = &perm_arena;

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fputs("manyan: out of memory\n", stderr); exit(MANYAN_ERROR); }
    return p;
}

static void *xrealloc(void *p, size_t n) {
    p = realloc(p, n ? n : 1);
    if (!p) { fputs("manyan: out of memory\n", stderr); exit(MANYAN_ERROR); }
    return p;
}

static void *xcalloc(size_t n, size_t size) {
    void *p = calloc(n ? n : 1, size);
    if (!p) { fputs("manyan: out of memory\n", stderr); exit(MANYAN_ERROR); }
    return p;
}

/* Memory the caller fills; alloc's is zeroed. */
static void *alloc_raw(size_t n) {
    n = (n + 15) & ~(size_t)15;
    Chunk *c = arena->head;
    if (!c || c->used + n > c->size) {
        size_t size = n > 1 << 20 ? n : 1 << 20;
        Chunk *fresh = size == 1 << 20 && arena->spare ? arena->spare : xmalloc(sizeof(Chunk) + size);
        if (fresh == arena->spare) arena->spare = NULL;

        fresh->next = c; fresh->used = 0; fresh->size = size;
        arena->head = c = fresh;
    }
    void *p = c->data + c->used;
    c->used += n;
    return p;
}

static void *alloc(size_t n) { return memset(alloc_raw(n), 0, n); }

#define NEW(T) ((T *)alloc(sizeof(T)))
#define NEWN(T, n) ((T *)alloc(sizeof(T) * (size_t)(n)))

/* v, of n elements of the size given, with room for one more: it holds 8,
   then doubles. */
static void *grow(void *v, int n, size_t size) {
    if (n && (n < 8 || n & (n - 1))) return v;
    void *g = alloc_raw(size * (n ? 2 * (size_t)n : 8));
    if (n) memcpy(g, v, size * (size_t)n);
    return g;
}
#define PUSH(v, n, x) ((v) = grow((v), (n), sizeof *(v)), (v)[(n)++] = (x))

static unsigned scratch_resets;   /* a value's address names it only between two */

static void arena_reset(Arena *a) {
    scratch_resets += a == &scratch_arena;
    Chunk *c = a->head;
    while (c && c->next) { Chunk *next = c->next; free(c); c = next; }
    if (c) c->used = 0;
    a->head = c;
}

static void arena_free(Arena *a) {
    arena_reset(a);
    free(a->head);
    free(a->spare);
    a->head = a->spare = NULL;
}

/* a takes b's chunks: what b made lives on in a. */
static void arena_join(Arena *a, Arena *b) {
    Chunk *last = b->head;
    while (last && last->next) last = last->next;
    if (last && a->head) last->next = a->head->next, a->head->next = b->head;
    else if (last) a->head = b->head;
    free(b->spare);
    b->head = b->spare = NULL;
}

static size_t arena_bytes(Arena *a) {
    size_t n = 0;
    for (Chunk *c = a->head; c; c = c->next) n += c->used;
    return n;
}

/* What one iteration of a loop made, a quantifier's body or a filter's
   test, from where its arena stood: dropped after it, unless a value made
   before it was given one it made. The permanent arena has none: it keeps
   what is computed once. */
typedef struct { Arena *a; Chunk *c; size_t used; int kept; } Region;
static Region regions[64];
static int nregions;

static int in_region(Region *r, void *p) {
    for (Chunk *c = r->a->head; c; c = c->next) {
        char *from = c->data + (c == r->c ? r->used : 0);
        if ((char *)p >= from && (char *)p < c->data + c->used) return 1;
        if (c == r->c) return 0;
    }
    return 0;
}

/* holder, a value or a binding, is given a value it keeps. */
static void held_by(void *holder) {
    for (int i = nregions - 1; i >= 0 && !in_region(&regions[i], holder); i--) regions[i].kept = 1;
}

static Region *region_open(void) {
    if (arena == &perm_arena || nregions == 64) return NULL;
    Region *r = &regions[nregions++];
    *r = (Region){arena, arena->head, arena->head ? arena->head->used : 0, 0};
    return r;
}

static void region_close(Region *r) {
    if (!r) return;
    nregions--;
    if (r->kept) return;
    while (r->a->head != r->c) {   /* one is kept: a loop crossing a chunk's end crosses it each time */
        Chunk *c = r->a->head;
        r->a->head = c->next;
        if (!r->a->spare && c->size == 1 << 20) r->a->spare = c;
        else free(c);
    }
    if (r->c) r->c->used = r->used;
}

/* A growable byte buffer. */
typedef struct { char *s; size_t n, cap; } Buf;

/* Room for n more bytes and the terminating 0. */
static inline void buf_room(Buf *b, size_t n) {
    if (b->n + n + 1 > b->cap) {
        b->cap = (b->n + n + 1) * 2;
        b->s = xrealloc(b->s, b->cap);
    }
}

static void buf_add(Buf *b, const char *s, size_t n) {
    buf_room(b, n);
    memcpy(b->s + b->n, s, n);
    b->n += n;
    b->s[b->n] = 0;
}

static void buf_puts(Buf *b, const char *s) { buf_add(b, s, strlen(s)); }

static void buf_printf(Buf *b, const char *fmt, ...) {
    char small[256];
    va_list ap;
    va_start(ap, fmt);
    int n = vsnprintf(small, sizeof small, fmt, ap);
    va_end(ap);
    if (n < (int)sizeof small) { buf_add(b, small, (size_t)n); return; }
    char *big = xmalloc((size_t)n + 1);
    va_start(ap, fmt);
    vsnprintf(big, (size_t)n + 1, fmt, ap);
    va_end(ap);
    buf_add(b, big, (size_t)n);
    free(big);
}

static char *buf_take(Buf *b) {
    char *s = alloc(b->n + 1);
    if (b->n) memcpy(s, b->s, b->n);
    free(b->s);
    b->s = NULL; b->n = b->cap = 0;
    return s;
}

/* ---------------------------------------------------------------- strings */

/* Every identifier and string is interned; strings compare by the order in
   which they were first interned (§7.5). */
typedef struct { char *s; int len; Value *value, *model; } Str;   /* its V_STR and V_MODEL, once made */

static Str *strs;
static int nstrs, capstrs;
static int *str_table;   /* open addressing: index + 1, 0 empty */
static int str_table_size;

static uint64_t hash_bytes(const void *p, size_t n, uint64_t h) {
    const unsigned char *s = p;
    for (size_t i = 0; i < n; i++) { h ^= s[i]; h *= 0x100000001b3ULL; }
    return h;
}

static int in_worker;   /* this process expands states for the search: it changes no shared data */
static int exit_requested;   /* TLCSet("exit", TRUE) */
static _Noreturn void worker_cannot(void);

static int intern_n(const char *s, int len) {
    if (nstrs * 2 >= str_table_size && !in_worker) {
        int size = str_table_size ? str_table_size * 2 : 1024;
        int *table = xcalloc((size_t)size, sizeof(int));
        for (int i = 0; i < nstrs; i++) {
            uint64_t h = hash_bytes(strs[i].s, (size_t)strs[i].len, 0xcbf29ce484222325ULL);
            int j = (int)(h & (uint64_t)(size - 1));
            while (table[j]) j = (j + 1) & (size - 1);
            table[j] = i + 1;
        }
        free(str_table);
        str_table = table;
        str_table_size = size;
    }
    uint64_t h = hash_bytes(s, (size_t)len, 0xcbf29ce484222325ULL);
    int j = (int)(h & (uint64_t)(str_table_size - 1));
    while (str_table[j]) {
        Str *t = &strs[str_table[j] - 1];
        if (t->len == len && memcmp(t->s, s, (size_t)len) == 0) return str_table[j] - 1;
        j = (j + 1) & (str_table_size - 1);
    }
    if (in_worker) worker_cannot();   /* a new string gets its number from the search */
    if (nstrs == capstrs) {
        capstrs = capstrs ? capstrs * 2 : 1024;
        strs = xrealloc(strs, sizeof(Str) * (size_t)capstrs);
    }
    char *copy = xmalloc((size_t)len + 1);
    memcpy(copy, s, (size_t)len);
    copy[len] = 0;
    strs[nstrs].s = copy;
    strs[nstrs].len = len;
    strs[nstrs].value = strs[nstrs].model = NULL;
    str_table[j] = nstrs + 1;
    return nstrs++;
}

static int intern(const char *s) { return intern_n(s, (int)strlen(s)); }
#define S(id) (strs[id].s)

/* Names TLC interns before it reads a module, in its order. */
static const char *builtin_names[] = {
    "'", "*", "-", "+", "=", "\\lnot", "~", "\\neg", "\\land", "/\\", "\\lor", "\\/", "~>", "=>",
    "[]", "<>", "ENABLED", "UNCHANGED", "SUBSET", "UNION", "DOMAIN", "\\cdot", "\\equiv", "<=>",
    "-+->", "/=", "#", "\\subseteq", "\\in", "\\notin", "\\times", "\\", "\\intersect", "\\cap",
    "\\union", "\\cup", "...", "..", "$", "@@", ":>", "\\o", "\\circ", "STRING", "FALSE", "TRUE",
    "BOOLEAN", "$AngleAct", "$BoundedChoose", "$BoundedExists", "$BoundedForall", "$CartesianProd",
    "$Case", "$ConjList", "$DisjList", "$Except", "$FcnApply", "$FcnConstructor", "$IfThenElse",
    "$NonRecursiveFcnSpec", "$Pair", "$RcdConstructor", "$RcdSelect", "$RecursiveFcnSpec", "$Seq",
    "$SetEnumerate", "$SetOfAll", "$SetOfFcns", "$SetOfRcds", "$SF", "$SquareAct", "$SubsetOf",
    "$TemporalExists", "$TemporalForall", "$TemporalWhile", "$Tuple", "$UnboundedChoose",
    "$UnboundedExists", "$UnboundedForall", "$WF", "$Nop", "$Qed", "$Pfcase", "$Have", "$Take",
    "$Pick", "$Witness", "$Suffices", "@", "VARIABLE", "<<", "SF_", "WF_", "LAMBDA", NULL};

/* ---------------------------------------------------------------- errors */

/* An error unwinds to the innermost handler with its message. */
typedef struct Expr Expr;
static sigjmp_buf *handler;
static Buf error_message;
static Expr *error_expr;   /* the expression an evaluation error names, if any */
static int error_status;   /* the exit status the error implies */
/* What TLC raises the error as: 0, its evaluator's RuntimeException; 1, an
   EvalException of a standard module's operator; 2, a TLCRuntimeException,
   with the exit status of its error code. */
static int error_module;
static const char *error_java;   /* the Java exception TLC throws instead, as java.util.IllegalFormatConversionException */
static int stackless;         /* TLC's error call stack is empty: 1, or 2 for its StackOverflowError */
/* The Java methods of the standard operators being applied, innermost last.
   TLC wraps any error inside one, but an EvalException, in a preamble. */
static const char *java_frames[64];
static int java_depth;
/* The values TLC made with a source being worked on, outermost first: the
   function constructors computed in full, and set operations it keeps as
   their definitions. An error raised inside one is one TLC cannot
   fingerprint (§11.3). */
static Expr *fp_trace[64];
static int fp_depth;
static int fp_frames[64];   /* the depth of TLC's call stack each was entered at */
static int nframes;

static void fp_enter(Expr *where) {
    if (!where) return;
    if (fp_depth < 64) fp_trace[fp_depth] = where, fp_frames[fp_depth] = nframes;
    fp_depth++;
}
static void fp_leave(Expr *where) { fp_depth -= where != NULL; }

/* TLC's call stack, as its CallStackTool keeps it replaying an error: the
   expressions being evaluated and generated, frozen at the first error.
   An error in a value's method reaches the innermost frame as TLC's
   FingerprintException, which adds the values with a source it went
   through. */
static int tracking;
static Expr **frames, **frozen;
static int capframes, nfrozen = -1;

static void frame_push(Expr *e) {
    if (nframes == capframes) frames = xrealloc(frames, sizeof(Expr *) * (size_t)(capframes = capframes ? 2 * capframes : 256));
    frames[nframes++] = e;
}

/* The source of a value made at e: none before the search, as TLC
   computes the definitions of constants without one. */
static Expr *source(Expr *e) { return arena == &scratch_arena ? e : NULL; }

/* TLC's exit status for an error evaluating the spec. */
static int eval_failure_status(void) { return error_status == MANYAN_VIOLATION_ASSERT ? MANYAN_VIOLATION_ASSERT : MANYAN_FAILURE_EVAL; }

static void error_reset(void) {
    error_message.n = 0;
    if (error_message.s) error_message.s[0] = 0;
    error_expr = NULL;
    error_status = MANYAN_ERROR;
    error_module = 0;
    error_java = NULL;
    stackless = 0;
}

static _Noreturn void raise_error(void) {
    if (tracking && nfrozen < 0) {
        int nfp = fp_depth < 64 ? fp_depth : 64;
        frozen = xmalloc(sizeof(Expr *) * (size_t)(nframes + nfp + 1));
        if (nframes) memcpy(frozen, frames, sizeof(Expr *) * (size_t)nframes);
        nfrozen = nframes;
        for (int i = 0; i < nfp; i++) if (fp_frames[i] >= nframes) frozen[nfrozen++] = fp_trace[i];
    }
    if (!handler) {
        fputs(error_message.s ? error_message.s : "error", stdout);
        exit(MANYAN_ERROR);
    }
    siglongjmp(*handler, 1);
}

static void loc_line(Buf *b, Expr *e);

static _Noreturn void vfail(Expr *e, int module, int status, const char *fmt, va_list ap) {
    va_list size;
    va_copy(size, ap);
    int n = vsnprintf(NULL, 0, fmt, size);
    va_end(size);
    char *small = xmalloc((size_t)n + 1);
    vsnprintf(small, (size_t)n + 1, fmt, ap);
    error_reset();
    /* TLC's evaluator wraps an error in each Java method it is raised in;
       an evaluation method wraps any error raised in it. */
    int wrapped = 0;
    for (int i = 0; i < java_depth && i < 64; i++)
        if (!module || strstr(java_frames[i], "ExprOrOpArgNode[]")) {
            buf_printf(&error_message, "Attempted to apply the operator overridden by the Java method\n%s,\n"
                       "but it produced the following error:\n", java_frames[i]);
            wrapped = 1;
        }
    if (wrapped) {
        buf_puts(&error_message, small);
        loc_line(&error_message, e);
        e = NULL;
        module = 2;
    } else {
        buf_puts(&error_message, small);
    }
    free(small);
    java_depth = 0;   /* errors are caught outside every standard operator */
    error_expr = e;
    error_module = module;
    error_status = status;
    raise_error();
}

static _Noreturn void fail_at(Expr *e, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfail(e, 0, MANYAN_ERROR, fmt, ap);
}

/* An error TLC raises as a TLCRuntimeException, which exits with status. */
static _Noreturn void fail_runtime(Expr *e, int status, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfail(e, 2, status, fmt, ap);
}

/* An error in an operator of a standard module, which TLC implements in Java. */
static _Noreturn void fail_module(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    vfail(NULL, 1, MANYAN_ERROR, fmt, ap);
}

#define fail(...) fail_at(NULL, __VA_ARGS__)

/* An error TLC meets as Java's exception cls. */
static _Noreturn void fail_java(const char *cls, const char *msg) {
    error_reset();
    buf_puts(&error_message, msg);
    error_module = 1;
    error_java = cls;
    raise_error();
}

/* A worker gives a state back to the search, which expands it itself. */
static _Noreturn void worker_cannot(void) { fail("A worker cannot expand this state."); }

/* ---------------------------------------------------------------- values */

/* Kinds, in the order values of different kinds sort (§7.4). */
enum {
    V_BOOL, V_INT, V_STR, V_MODEL, V_TUPLE, V_FCN, V_SET, V_INTERVAL,
    V_LAZY,     /* a set kept as its definition: see LazyKind */
    V_LAMBDA,   /* a function over an infinite domain, kept as its definition */
    V_OPER      /* an operator passed as an argument; never a TLA+ value */
};

/* How a function was made, which decides TLC's errors applying it: a
   record, or [x \in S |-> e] not yet stored in a state or a constant. */
/* MADE_LAMBDA: computed by [x \in S |-> e];
   MADE_HELD: a V_SET that TLC keeps as its definition, a UNION or a \cup, \cap
   or \ of such sets, so that a filter or function over it is lazy (§6.5) */
enum Made { MADE_PLAIN, MADE_RECORD, MADE_LAMBDA, MADE_HELD };

enum LazyKind {
    L_NAT, L_INT, L_STRING, L_SUBSET, L_FCNSET, L_RCDSET, L_SEQ, L_FILTER, L_TIMES, L_ANY,
    L_UNION,    /* UNION S that TLC keeps as it is, S not a set of sets of their elements: S in a, its
                   elements once enumerated in b, and in set once TLC keeps them too (union_cache);
                   n while a is to be sorted (union_sets) */
    L_CUP, L_CAP, L_DIFF
};

struct ManyanValue {
    unsigned char kind;
    union {
        unsigned char lazy;  /* LazyKind of a V_LAZY */
        unsigned char made;  /* Made of a V_FCN or V_SET */
        unsigned char keep;  /* V_LAMBDA: TLC's KeepLazy when it was made, which it is computed in full with */
    };
    unsigned char perm;      /* a V_LAZY made in the permanent arena */
    unsigned char range;     /* a V_FCN whose domain TLC keeps as the interval of its keys; a record of
                                a state, of Trace or CounterExample, whose fields TLC keeps in the order
                                of the variables */
    int n;                   /* elements of a set, tuple, or function */
    union {
        int64_t i;           /* V_BOOL, V_INT, V_STR, V_MODEL (string id) */
        struct { Value **elems; uint64_t hash; Expr *source; Value *product; } set;   /* V_SET, sorted, distinct */
        /* product: the s1 \X ... \X sn TLC keeps, held enumerated */
        struct { Value **keys, **vals; uint64_t hash; Expr *source; } fcn;
        /* V_TUPLE has no keys; source: the <<...>>, [...] or {...} that
           made it, which TLC names when applying or fingerprinting it
           fails, until the state holding it is stored */
        /* hash: the sum of the elements' or pairs' hashes, once known; else 0 */
        struct { int64_t lo, hi; } range;            /* V_INTERVAL */
        struct { Value *a, *b; union { Value **names; Value *set; }; Expr *expr; Env *env; Inst *inst; Def *binder; Value ***made_in; } l;
        /* set: an L_CUP, L_CAP or L_DIFF's elements, once enumerated */
        /* V_LAMBDA: [x \in a |-> expr] in env, with b for @, then n EXCEPT pairs (key, value);
           made_in: in a simulation, the current and next state it was made in */
        struct { Def *def; Env *env; Inst *inst; Expr *lambda; Value *table; } op;
        /* table: TLC's OpRcdValue, a constant operator the configuration
           defines by its values, as tuples <<arg, ..., value>> in order */
    } u;
};

static Value value_true = {.kind = V_BOOL, .u.i = 1};
static Value value_false = {.kind = V_BOOL, .u.i = 0};
#define TRUEV (&value_true)
#define FALSEV (&value_false)
#define BOOLV(b) ((b) ? TRUEV : FALSEV)

static Value *small_ints[1024];

static Value *mk_int(int64_t i) {
    if (i >= -1 && i < 1023 && small_ints[i + 1]) return small_ints[i + 1];
    Value *v = NEW(Value);
    v->kind = V_INT;
    v->u.i = i;
    return v;
}

/* One value for each string, and each model value, outside the arenas. */
static Value *atom_of(Value **at, int kind, int id) {
    if (!*at) {
        *at = xmalloc(sizeof(Value));
        **at = (Value){.kind = (unsigned char)kind, .u.i = id};
    }
    return *at;
}

static Value *mk_str(int id) { return atom_of(&strs[id].value, V_STR, id); }
static Value *mk_model(int id) { return atom_of(&strs[id].model, V_MODEL, id); }

static Value *mk_tuple(int n) {
    Value *v = NEW(Value);
    v->kind = V_TUPLE;
    v->n = n;
    v->u.fcn.vals = alloc_raw(sizeof(Value *) * (size_t)n);
    return v;
}

static Value *substr(Value *s, int from, int len) { return mk_str(intern_n(strs[s->u.i].s + from, len)); }

static Value *mk_fcn(int n) {
    Value *v = NEW(Value);
    v->kind = V_FCN;
    v->n = n;
    v->u.fcn.keys = alloc_raw(sizeof(Value *) * (size_t)n);
    v->u.fcn.vals = alloc_raw(sizeof(Value *) * (size_t)n);
    return v;
}

static Value *mk_interval(int64_t lo, int64_t hi) {
    Value *v = NEW(Value);
    v->kind = V_INTERVAL;
    v->u.range.lo = lo;
    v->u.range.hi = hi;
    v->n = hi < lo ? 0 : hi - lo + 1 > INT32_MAX ? -1 : (int)(hi - lo + 1);
    return v;
}

/* The number of elements of an interval, which TLC keeps in 32 bits. */
static int interval_size(Value *v) {
    if (v->n < 0)
        fail("Size of interval value exceeds the maximum representable size (32bits): %lld..%lld.",
             (long long)v->u.range.lo, (long long)v->u.range.hi);
    return v->n;
}

static Value *mk_lazy(int kind) {
    Value *v = NEW(Value);
    v->kind = V_LAZY;
    v->lazy = (unsigned char)kind;
    v->perm = arena == &perm_arena;
    return v;
}

/* A value or binding made in the permanent arena computes what it keeps
   there, as TLC keeps it, but in the search: the arena to go back to. */
static Arena *keeping(int perm) {
    Arena *saved = arena;
    if (perm && arena != &scratch_arena) arena = &perm_arena;
    return saved;
}

/* Whether lazy s may keep a value made now: not one that dies before it. */
static int may_keep(Value *s) {
    if (s->perm && arena != &perm_arena) return 0;
    held_by(s);
    return 1;
}

static const char *kind_name(Value *v) {
    switch (v->kind) {
    case V_BOOL: return "boolean";
    case V_INT: return "integer";
    case V_STR: return "string";
    case V_MODEL: return "model value";
    case V_TUPLE: case V_FCN: return "function";
    default: return "set";
    }
}

static int is_set(Value *v) { return v->kind == V_SET || v->kind == V_INTERVAL || v->kind == V_LAZY; }

/* Nat, Int, STRING, Seq(S) and Any: what TLC calls overridden values. */
static int user_set(Value *s) {
    return s->kind == V_LAZY && (s->lazy == L_NAT || s->lazy == L_INT || s->lazy == L_STRING || s->lazy == L_SEQ || s->lazy == L_ANY);
}
/* How TLC names the kind of a value in error messages. */
static const char *kind_string(Value *v) {
    switch (v->kind) {
    case V_BOOL: return "a Boolean value";
    case V_INT: return "an integer";
    case V_STR: return "a string";
    case V_MODEL: return "a model value";
    case V_TUPLE: return "a tuple";
    case V_FCN: return v->made == MADE_RECORD ? "a record" : "a function  of the form (d1 :> e1 @@ ... @@ dN :> eN)";
    case V_SET: return "a set of the form {e1, ... ,eN}";
    case V_INTERVAL: return "a set of the form i..j";
    case V_OPER: return "an operator";
    case V_LAMBDA: return "a function of the form  [x \\in S |-> expr]";
    default: break;
    }
    switch (v->lazy) {
    case L_SUBSET: return "a set of the form SUBSET S";
    case L_FCNSET: return "a set of the form [S -> T]";
    case L_RCDSET: return "a set of the form [d1 : S1, ... , dN : SN]";
    case L_FILTER: return "a set of the form {x \\in S : expr}";
    case L_TIMES: return "a cartesian product";
    case L_CUP: return "a set of the form S \\cup T";
    case L_CAP: return "a set of the form S \\cap T";
    case L_DIFF: return "a set of the form S \\ T";
    default: return "a special set constant";
    }
}

static int is_fcn(Value *v) { return v->kind == V_TUPLE || v->kind == V_FCN; }

/* ---------------------------------------------------------------- printing */

static void print_value(Buf *b, Value *v);
static Value *realize_lambda(Value *f);
static void realize_both(Value **a, Value **b);
/* A lazy function over a finite domain as the function it is (§6.6). */
static inline Value *realize(Value *v) { return v->kind == V_LAMBDA ? realize_lambda(v) : v; }
static Value *try_realize(Value *f);
static void print_lambda(Buf *b, Value *f);
static void print_filter(Buf *b, Value *s);
static Value *normalize_set(Value *v);
static __attribute__((noinline)) int lazy_is_infinite(Value *s);
static inline int set_is_infinite(Value *s) { return s->kind == V_LAZY && lazy_is_infinite(s); }
static int64_t set_size(Value *s);
static Value *enumerate_other(Value *s);
static inline Value *enumerate(Value *s) { return s->kind == V_SET ? s : enumerate_other(s); }
static Value *union_cache(Value *s);
static Value *union_sets(Value *s);
static int kinds_differ(Value *a, Value *b);
static int enumerable(Value *s);
static Value *select_members(Value *s, Value *t, int in);

/* Whether TLC enumerates S \cup T, S \cap T or S \ T it keeps as its
   definition, printing it. */
static int set_op_enumerable(Value *v) {
    Value *a = v->u.l.a, *b = v->u.l.b;
    if (v->lazy == L_CUP) return enumerable(a) && enumerable(b) && !kinds_differ(enumerate(a), enumerate(b));
    return enumerable(a) || (v->lazy == L_CAP && enumerable(b));
}

/* A lazy set TLC prints by its elements; others it prints as written. */
static int expandable(Value *v) {
    if (set_is_infinite(v)) return 0;
    int64_t n = set_size(v);
    return n >= 0 && n < 2000000;
}

/* A function whose domain is 1..n prints as a tuple. */
static int fcn_is_tuple(Value *f) {
    if (f->kind == V_TUPLE) return 1;
    for (int i = 0; i < f->n; i++)
        if (f->u.fcn.keys[i]->kind != V_INT || f->u.fcn.keys[i]->u.i != i + 1) return 0;
    return 1;
}

static int fcn_is_record(Value *f) {
    if (f->kind != V_FCN || f->n == 0) return 0;
    for (int i = 0; i < f->n; i++)
        if (f->u.fcn.keys[i]->kind != V_STR) return 0;
    return 1;
}

/* TLC prints a function as a record if each key is a name: letters,
   digits and _, a letter among them, and no WF_ or SF_ of more. */
static int printed_as_record(Value *f) {
    if (!fcn_is_record(f)) return 0;
    for (int i = 0; i < f->n; i++) {
        const char *k = S(f->u.fcn.keys[i]->u.i);
        int letter = 0;
        for (const char *p = k; *p; p++) {
            if (*p != '_' && !isalnum((unsigned char)*p)) return 0;
            letter |= isalpha((unsigned char)*p) != 0;
        }
        if (!letter || (strlen(k) >= 4 && (!strncmp(k, "WF_", 3) || !strncmp(k, "SF_", 3)))) return 0;
    }
    return 1;
}

static void print_string(Buf *b, int id) {
    buf_puts(b, "\"");
    for (const char *s = S(id); *s; s++) {
        switch (*s) {
        case '"': buf_puts(b, "\\\""); break;
        case '\\': buf_puts(b, "\\\\"); break;
        case '\n': buf_puts(b, "\\n"); break;
        case '\t': buf_puts(b, "\\t"); break;
        case '\r': buf_puts(b, "\\r"); break;
        case '\f': buf_puts(b, "\\f"); break;
        default: buf_add(b, s, 1);
        }
    }
    buf_puts(b, "\"");
}

static void print_value(Buf *b, Value *v);
/* An operand of \cup, \cap or \, which TLC parenthesizes unless it is
   Nat, Int, STRING or Seq(S). */
static void print_operand(Buf *b, Value *v) {
    if (user_set(v)) { print_value(b, v); return; }
    buf_puts(b, "(");
    print_value(b, v);
    buf_puts(b, ")");
}

static void print_value(Buf *b, Value *v) {
    if (v->kind == V_LAMBDA) v = try_realize(v);
    if (v->kind == V_LAMBDA) { print_lambda(b, v); return; }
    switch (v->kind) {
    case V_BOOL: buf_puts(b, v->u.i ? "TRUE" : "FALSE"); return;
    case V_INT: buf_printf(b, "%lld", (long long)v->u.i); return;
    case V_STR: print_string(b, (int)v->u.i); return;
    case V_MODEL: buf_puts(b, S(v->u.i)); return;
    case V_INTERVAL:
        if (v->n == 0) buf_puts(b, "{}");
        else buf_printf(b, "%lld..%lld", (long long)v->u.range.lo, (long long)v->u.range.hi);
        return;
    case V_LAZY:
        if (v->lazy == L_NAT) { buf_puts(b, "Nat"); return; }
        if (v->lazy == L_INT) { buf_puts(b, "Int"); return; }
        if (v->lazy == L_STRING) { buf_puts(b, "STRING"); return; }
        if (v->lazy == L_ANY) { buf_puts(b, "ANY"); return; }
        if (v->lazy == L_SEQ) { buf_puts(b, "Seq("); print_value(b, v->u.l.a); buf_puts(b, ")"); return; }
        if (v->lazy == L_UNION) {
            int infinite = 0;
            for (int i = 0; i < v->u.l.a->n; i++) infinite |= is_set(v->u.l.a->u.set.elems[i]) && set_is_infinite(v->u.l.a->u.set.elems[i]);
            if (infinite) { buf_puts(b, "UNION "); print_value(b, v->u.l.a); return; }
        }
        if (v->lazy >= L_CUP && !set_op_enumerable(v)) {
            print_operand(b, v->u.l.a);
            buf_puts(b, v->lazy == L_CUP ? " \\cup " : v->lazy == L_CAP ? " \\cap " : " \\ ");
            print_operand(b, v->u.l.b);
            return;
        }
        if (expandable(v)) { print_value(b, normalize_set(v)); return; }
        if (v->lazy == L_SUBSET) {
            Value *a = v->u.l.a;
            int paren = a->kind == V_INTERVAL || (a->kind == V_LAZY && a->lazy >= L_CUP);   /* .. binds tighter */
            buf_puts(b, paren ? "SUBSET (" : "SUBSET ");
            print_value(b, a);
            if (paren) buf_puts(b, ")");
            return;
        }
        if (v->lazy == L_FCNSET) {
            buf_puts(b, "[");
            print_value(b, v->u.l.a);
            buf_puts(b, " -> ");
            print_value(b, v->u.l.b);
            buf_puts(b, "]");
            return;
        }
        if (v->lazy == L_RCDSET) {
            buf_puts(b, "[");
            for (int i = 0; i < v->n; i++) {
                buf_printf(b, "%s%s: ", i ? ", " : "", S(v->u.l.names[i]->u.i));
                print_value(b, v->u.l.names[v->n + i]);
            }
            buf_puts(b, "]");
            return;
        }
        if (v->lazy == L_TIMES) {
            buf_puts(b, "(");
            for (int i = 0; i < v->n; i++) {
                if (i) buf_puts(b, " \\X ");
                print_value(b, v->u.l.names[v->n + i]);
            }
            buf_puts(b, ")");
            return;
        }
        if (v->lazy == L_FILTER && set_is_infinite(v->u.l.a)) { print_filter(b, v); return; }
        print_value(b, normalize_set(v));
        return;
    case V_SET:
        buf_puts(b, "{");
        for (int i = 0; i < v->n; i++) {
            if (i) buf_puts(b, ", ");
            print_value(b, v->u.set.elems[i]);
        }
        buf_puts(b, "}");
        return;
    case V_TUPLE: case V_FCN:
        if (v->n == 0) { buf_puts(b, v->kind == V_FCN && v->made == MADE_RECORD ? "[]" : "<<>>"); return; }   /* [] from Java: a JSON object */
        if (fcn_is_tuple(v)) {
            buf_puts(b, "<<");
            for (int i = 0; i < v->n; i++) {
                if (i) buf_puts(b, ", ");
                print_value(b, v->u.fcn.vals[i]);
            }
            buf_puts(b, ">>");
        } else if (printed_as_record(v)) {
            buf_puts(b, "[");
            for (int i = 0; i < v->n; i++) {
                if (i) buf_puts(b, ", ");
                buf_printf(b, "%s |-> ", S(v->u.fcn.keys[i]->u.i));
                print_value(b, v->u.fcn.vals[i]);
            }
            buf_puts(b, "]");
        } else {
            buf_puts(b, "(");
            for (int i = 0; i < v->n; i++) {
                if (i) buf_puts(b, " @@ ");
                print_value(b, v->u.fcn.keys[i]);
                buf_puts(b, " :> ");
                print_value(b, v->u.fcn.vals[i]);
            }
            buf_puts(b, ")");
        }
        return;
    case V_OPER:
        if (!v->u.op.table) { buf_puts(b, "<operator>"); return; }
        buf_puts(b, "{ ");
        for (int i = 0; i < v->u.op.table->n; i++) {
            Value *line = v->u.op.table->u.fcn.vals[i];
            buf_puts(b, i ? ", <" : "<");
            for (int j = 0; j < line->n; j++) { if (j) buf_puts(b, ", "); print_value(b, line->u.fcn.vals[j]); }
            buf_puts(b, ">");
        }
        buf_puts(b, "}");
        return;
    }
}

static char *value_str(Value *v) {
    Buf b = {0};
    print_value(&b, v);
    return buf_take(&b);
}

/* TLC's pretty printer (tlc2.pprint.Format) breaks a value longer than
   the line width, element by element (§7.6). */

/* Whether TLC's parser fails on a name it prints bare, a model value or
   a record's field: it takes only letters and digits. */
static int pp_odd_name(int name) {
    for (const char *p = S(name); *p; p++) if (!isalnum((unsigned char)*p)) return 1;
    return 0;
}

static int pp_plain(Value *v) {
    if (v->kind == V_LAMBDA) return try_realize(v)->kind == V_LAMBDA;   /* TLC cannot parse <expression ...> */
    if (v->kind == V_MODEL) return pp_odd_name((int)v->u.i);
    if (v->kind == V_INTERVAL) return v->n && v->u.range.lo < 0;   /* TLC cannot parse -1..3 */
    if (v->kind == V_LAZY && !expandable(v)) return 1;
    if (v->kind == V_LAZY) return pp_plain(normalize_set(v));
    if (v->kind == V_SET)
        for (int i = 0; i < v->n; i++) if (pp_plain(v->u.set.elems[i])) return 1;
    if (is_fcn(v)) {
        int record = v->kind == V_FCN && printed_as_record(v);
        for (int i = 0; i < v->n; i++)
            if (pp_plain(v->u.fcn.vals[i]) || (v->kind == V_FCN && (record ? pp_odd_name((int)v->u.fcn.keys[i]->u.i) : pp_plain(v->u.fcn.keys[i])))) return 1;
    }
    return 0;
}

static void pp_format(Buf *b, Value *v, int width, int trailer, const char *pad);

static void pp_values(Buf *b, Value **vals, int n, int width, int trailer, const char *pad) {
    for (int i = 0; i < n; i++) {
        if (i + 1 < n) {
            pp_format(b, vals[i], width, 1, pad);
            buf_puts(b, ",\n");
            buf_puts(b, pad);
        } else {
            pp_format(b, vals[i], width, trailer, pad);
        }
    }
}

static char *pad_more(const char *pad, int n) {
    size_t len = strlen(pad);
    char *s = alloc(len + (size_t)n + 1);
    memcpy(s, pad, len);
    memset(s + len, ' ', (size_t)n);
    return s;
}

static void pp_pairs(Buf *b, Value *f, int record, int width, int trailer, const char *pad) {
    const char *sep = record ? "," : " @@";
    const char *div = record ? " |->" : " :>";
    int seplen = (int)strlen(sep), divlen = (int)strlen(div), divpad = 4;
    char *inner = pad_more(pad, divpad);
    for (int i = 0; i < f->n; i++) {
        Value *key = f->u.fcn.keys[i], *val = f->u.fcn.vals[i];
        char *ks = record ? S(key->u.i) : value_str(key);
        char *vs = value_str(val);
        int kl = (int)strlen(ks), vl = (int)strlen(vs);
        int last = i + 1 == f->n;
        int tail = last ? trailer : 0;
        if (kl + divlen + 1 + vl + (last ? 0 : seplen) <= width - tail) {
            buf_printf(b, "%s%s %s", ks, div, vs);
        } else {
            if (kl + divlen <= width || record) buf_printf(b, "%s%s", ks, div);
            else { pp_format(b, key, width, trailer + divlen, pad); buf_puts(b, div); }
            buf_printf(b, "\n%s    ", pad);
            pp_format(b, val, width - divpad, last ? trailer : seplen, inner);
        }
        if (!last) { buf_printf(b, "%s\n%s", sep, pad); }
    }
}

static void pp_format(Buf *b, Value *v, int width, int trailer, const char *pad) {
    if (v->kind == V_LAMBDA) v = try_realize(v);
    if (v->kind == V_LAZY && expandable(v)) v = normalize_set(v);
    char *flat = value_str(v);
    if ((int)strlen(flat) <= width - trailer || pp_plain(v) || v->n == 0) { buf_puts(b, flat); return; }
    if (v->kind == V_SET) {
        buf_puts(b, "{ ");
        pp_values(b, v->u.set.elems, v->n, width - 2, trailer + 2, pad_more(pad, 2));
        buf_puts(b, " }");
    } else if (is_fcn(v) && fcn_is_tuple(v)) {
        buf_puts(b, "<< ");
        pp_values(b, v->u.fcn.vals, v->n, width - 3, trailer + 3, pad_more(pad, 3));
        buf_puts(b, " >>");
    } else if (is_fcn(v)) {
        int record = printed_as_record(v);
        buf_puts(b, record ? "[ " : "( ");
        pp_pairs(b, v, record, width - 2, trailer + 2, pad_more(pad, 2));
        buf_puts(b, record ? " ]" : " )");
    } else {
        buf_puts(b, flat);
    }
}

static char *pretty(Value *v) {
    Buf b = {0};
    pp_format(&b, v, 80, 0, "");
    return buf_take(&b);
}

/* ---------------------------------------------------------------- environments */

/* A context is where an expression is evaluated: the bindings of bound
   names and operator parameters, and the module instance (§4.3). */
typedef struct { Env *env; Inst *inst; } Ctx;

/* A binding. An operator's argument is bound unevaluated, as `e` in its
   caller's context, and evaluated where it is used (§5.2). */
struct Env {
    Def *def;
    Value *v;
    Expr *e;
    Env *ctx_env;
    Inst *ctx_inst;
    Env *next;
    unsigned char perm;   /* allocated in the permanent arena */
    unsigned char stateful;   /* v was read from the current state */
};

/* An instance: the module instance definition and the context of the
   instantiation, where the substitutions are evaluated. */
/* kept: the values of the substitutions in the state whose values are
   in state, as TLC keeps a LazyValue, for the search's scratch arena
   while it is not reset (resets). */
struct Inst {
    Def *def;
    Env *env;
    Inst *parent;
    unsigned resets;
    Value **state, **kept;
};

typedef Value *(*EvalFn)(Expr *e, Ctx c);
static inline Value *eval(Expr *e, Ctx c);
static int eval_bool(Expr *e, Ctx c);
static Value *filter_member_test(Value *s, Value *v);

/* ---------------------------------------------------------------- comparison */

static int vcmp(Value *a, Value *b);
static int veq(Value *a, Value *b);

static Value *fcn_key(Value *f, int i) { return f->kind == V_TUPLE ? mk_int(i + 1) : f->u.fcn.keys[i]; }

/* The expression that made a value, as TLC keeps it to name in a
   fingerprint stack trace when an error arises in one of its methods. */
static Expr *value_source(Value *v) {
    return v->kind == V_SET ? v->u.set.source : v->kind == V_TUPLE || v->kind == V_FCN ? v->u.fcn.source : NULL;
}

static _Noreturn void compare_error(Value *a, Value *b) {
    fp_enter(value_source(a));
    const char *k = kind_name(a);
    if (a->kind == V_FCN && a->made == MADE_RECORD)
        fail("Attempted to compare record:\n%s\nwith non-record\n%s", pretty(a), pretty(b));
    if (is_fcn(a)) fail("Attempted to compare the function %s with the value:\n%s", pretty(a), pretty(b));
    if (is_set(a)) fail("Attempted to compare the set %s with the value:\n%s", pretty(a), pretty(b));
    fail("Attempted to compare %s %s with non-%s:\n%s", k, pretty(a), k, pretty(b));
}

/* Nat or Int, which TLC orders and compares without enumerating: Nat first. */
static int number_set(Value *v) { return v->kind == V_LAZY && v->lazy <= L_INT; }

/* TLC's error comparing sets of which one is infinite. */
static _Noreturn void incomparable(Value *a, Value *b) {
    /* Two overridden values compare by the first's module. */
    if (user_set(a) && user_set(b)) fail_module("Attempted to compare %s with the value\n%s", pretty(a), pretty(b));
    fp_enter(value_source(a));
    if (user_set(a)) fail("Attempted to compare overridden value %s with non-overridden value:\n%s", pretty(a), pretty(b));
    if (user_set(b)) fail("Attempted to check equality of the set %s with the value:\n%s", pretty(enumerate(a)), pretty(b));
    enumerate(set_is_infinite(a) ? a : b);   /* fails with TLC's error for that set */
    abort();
}

/* x and y, n atoms each, in order, as vcmp compares the parts of sets and
   tuples; NOT_ATOMS when it meets a pair that are not atoms of one kind. */
enum { NOT_ATOMS = 2 };
static inline int atoms_cmp(Value **x, Value **y, int n) {
    for (int i = 0; i < n; i++) {
        if (x[i]->kind != y[i]->kind || x[i]->kind > V_MODEL) return NOT_ATOMS;
        if (x[i]->u.i != y[i]->u.i) return x[i]->u.i < y[i]->u.i ? -1 : 1;
    }
    return 0;
}

/* The standard order (§7.4). Model values come first; other values of
   different kinds cannot be compared. */
static int vcmp(Value *a, Value *b) {
    if (a->kind == b->kind && a->kind <= V_MODEL) return (a->u.i > b->u.i) - (a->u.i < b->u.i);
    if (a == b) return 0;
    if (a->kind == b->kind && (a->kind == V_SET || a->kind == V_TUPLE)) {   /* of atoms, as the cases below */
        if (a->n != b->n) return a->n < b->n ? -1 : 1;
        int c = a->kind == V_SET ? atoms_cmp(a->u.set.elems, b->u.set.elems, a->n) : atoms_cmp(a->u.fcn.vals, b->u.fcn.vals, a->n);
        if (c != NOT_ATOMS) return c;
    }
    if (a->kind == V_LAMBDA || b->kind == V_LAMBDA) realize_both(&a, &b);
    /* Comparing the parts of a value TLC made with a source names it in
       the fingerprint stack trace of an error there. */
    Expr *src = value_source(a);
    int c = 0;
    if (a->kind == V_TUPLE && b->kind == V_TUPLE) {
        if (a->n != b->n) return a->n < b->n ? -1 : 1;
        fp_enter(src);
        for (int i = 0; i < a->n && !c; i++) {
            Value *x = a->u.fcn.vals[i], *y = b->u.fcn.vals[i];
            c = x->kind == y->kind && x->kind <= V_MODEL ? (x->u.i > y->u.i) - (x->u.i < y->u.i) : vcmp(x, y);
        }
        fp_leave(src);
        return c;
    }
    if (number_set(a) && number_set(b)) return (a->lazy > b->lazy) - (a->lazy < b->lazy);
    if (a->kind == V_MODEL || b->kind == V_MODEL) {
        if (a->kind != b->kind) return a->kind == V_MODEL ? -1 : 1;
        return a->u.i < b->u.i ? -1 : a->u.i > b->u.i;
    }
    if (is_fcn(a) && is_fcn(b)) {
        if (a->n != b->n) return a->n < b->n ? -1 : 1;
        fp_enter(src);
        for (int i = 0; i < a->n && !c; i++) {
            if (a->kind != V_TUPLE || b->kind != V_TUPLE) c = vcmp(fcn_key(a, i), fcn_key(b, i));
            if (!c) c = vcmp(a->u.fcn.vals[i], b->u.fcn.vals[i]);
        }
        fp_leave(src);
        return c;
    }
    if (is_set(a) && is_set(b)) {
        if (a->kind == V_LAZY && b->kind == V_LAZY && a->lazy == b->lazy && a->lazy <= L_STRING) return 0;
        if (a->kind == V_SET && user_set(b)) {   /* TLC's SetEnumValue cannot enumerate the other */
            fp_enter(src);
            fail("Attempted to compare the set %s with the value:\n%s", pretty(a), pretty(b));
        }
        if (set_is_infinite(a) || set_is_infinite(b)) incomparable(user_set(b) ? b : a, user_set(b) ? a : b);   /* as TLC sorts */
        a = enumerate(union_cache(a));
        b = enumerate(b);
        if (a->n != b->n) return a->n < b->n ? -1 : 1;
        fp_enter(src);
        for (int i = 0; i < a->n && !c; i++) {
            Value *x = a->u.set.elems[i], *y = b->u.set.elems[i];
            c = x->kind == y->kind && x->kind <= V_MODEL ? (x->u.i > y->u.i) - (x->u.i < y->u.i) : vcmp(x, y);
        }
        fp_leave(src);
        return c;
    }
    if (a->kind != b->kind || a->kind == V_OPER) compare_error(a, b);
    return a->u.i < b->u.i ? -1 : a->u.i > b->u.i;
}

/* vcmp, inline for atoms and tuples of atoms, the common elements of sets. */
static inline int vcmp_quick(Value *a, Value *b) {
    if (a->kind == b->kind && a->kind <= V_MODEL) return (a->u.i > b->u.i) - (a->u.i < b->u.i);
    if (a->kind == V_TUPLE && b->kind == V_TUPLE && a->n == b->n) {
        int c = atoms_cmp(a->u.fcn.vals, b->u.fcn.vals, a->n);
        if (c != NOT_ATOMS) return c;
    }
    return vcmp(a, b);
}

static _Noreturn void equality_error(Value *a, Value *b) {
    fp_enter(value_source(a));
    const char *k = kind_name(a);
    if (a->kind == V_BOOL) fail("Attempted to compare equality of boolean %s with non-boolean:\n%s", pretty(a), pretty(b));
    if (a->kind == V_FCN && a->made == MADE_RECORD)
        fail("Attempted to check equality of record:\n%s\nwith non-record\n%s", pretty(a), pretty(b));
    if (user_set(a)) fail("Attempted to compare overridden value %s with non-overridden value:\n%s", pretty(a), pretty(b));
    if (is_fcn(a)) fail("Attempted to check equality of the function %s with the value:\n%s", pretty(a), pretty(b));
    if (is_set(a)) fail("Attempted to check equality of the set %s with the value:\n%s", pretty(a), pretty(b));
    fail("Attempted to check equality of %s %s with non-%s:\n%s", k, pretty(a), k, pretty(b));
}

/* Whether TLC makes a record of the function, its domain all strings. */
static int as_record(Value *f) {
    if (f->kind == V_TUPLE) return f->n == 0;
    for (int i = 0; i < f->n; i++) if (f->u.fcn.keys[i]->kind != V_STR) return 0;
    return 1;
}
static int veq(Value *a, Value *b) {
    if (a == b) return 1;
    if (a->kind == V_LAMBDA || b->kind == V_LAMBDA) realize_both(&a, &b);
    if (a->kind == V_MODEL || b->kind == V_MODEL) return a->kind == b->kind && a->u.i == b->u.i;
    Expr *src = value_source(a);   /* named in an error in its parts, as vcmp */
    int same = 1;
    if (is_fcn(a) && is_fcn(b)) {
        if (a->made == MADE_RECORD && !as_record(b)) equality_error(a, b);
        if (a->n != b->n) return 0;
        fp_enter(src);
        for (int i = 0; i < a->n && same; i++)
            same = ((a->kind == V_TUPLE && b->kind == V_TUPLE) || veq(fcn_key(a, i), fcn_key(b, i)))
                && veq(a->u.fcn.vals[i], b->u.fcn.vals[i]);
        fp_leave(src);
        return same;
    }
    if (is_set(a) && is_set(b)) {
        if (a->kind == V_INTERVAL && b->kind == V_INTERVAL)
            return interval_size(a) == interval_size(b) && (a->n == 0 || a->u.range.lo == b->u.range.lo);
        if (a->kind == V_LAZY && b->kind == V_LAZY && a->lazy == b->lazy && a->lazy <= L_STRING) return 1;
        if (number_set(a) && number_set(b)) return 0;
        if (set_is_infinite(a) || set_is_infinite(b)) {
            if (a->kind == V_LAZY && b->kind == V_LAZY && a->lazy == b->lazy && a->lazy == L_SEQ)
                return veq(a->u.l.a, b->u.l.a);
            incomparable(a, b);
        }
        a = enumerate(union_cache(a));
        b = enumerate(b);
        if (a->n != b->n) return 0;
        fp_enter(src);
        for (int i = 0; i < a->n && same; i++) same = veq(a->u.set.elems[i], b->u.set.elems[i]);
        fp_leave(src);
        return same;
    }
    if (a->kind != b->kind || a->kind == V_OPER) equality_error(a, b);
    return a->u.i == b->u.i;
}

/* ---------------------------------------------------------------- sets */

static Value *mk_set(int n) {
    Value *v = NEW(Value);
    v->kind = V_SET;
    v->n = n;
    v->u.set.elems = alloc_raw(sizeof(Value *) * (size_t)n);
    return v;
}

static int cmp_for_sort(const void *x, const void *y) { return vcmp(*(Value **)x, *(Value **)y); }

/* Sorts the elements and removes duplicates. Small sets, often built in
   order, are sorted by insertion, which finds any duplicate next to where
   it stops. */
static Value *set_normalize(Value *s) {
    Value **e = s->u.set.elems;
    int n = s->n, dup = 0;
    if (n < 2) return s;
    if (n <= 32) {
        for (int i = 1; i < n; i++) {
            Value *x = e[i];
            int j = i, c = 1;
            while (j > 0 && (c = vcmp(x, e[j - 1])) < 0) { e[j] = e[j - 1]; j--; }   /* as TLC: the new one first */
            e[j] = x;
            dup |= c == 0;
        }
    } else {
        qsort(e, (size_t)n, sizeof(Value *), cmp_for_sort);
        dup = 1;
    }
    if (dup) {
        int k = 1;
        for (int i = 1; i < n; i++) if (vcmp(e[k - 1], e[i]) != 0) e[k++] = e[i];
        s->n = k;
    }
    return s;
}

/* A list that builds a set. */
typedef struct { Value **v; int n, cap; } List;

static void list_add(List *l, Value *v) {
    if (l->n == l->cap) {
        int cap = l->cap ? l->cap * 2 : 8;
        Value **grown = alloc_raw(sizeof(Value *) * (size_t)cap);
        if (l->n) memcpy(grown, l->v, sizeof(Value *) * (size_t)l->n);
        l->v = grown;
        l->cap = cap;
    }
    l->v[l->n++] = v;
}

/* The enumerated S of {x \in S : p(x)}, whose elements TLC filters as
   it takes them. */
static Value *filter_base(Value *s) {
    if (!is_set(s->u.l.a) || user_set(s->u.l.a))
        fail("Attempted to enumerate { x \\in S : p(x) } when S:\n%s\nis not enumerable", pretty(s->u.l.a));
    return enumerate(s->u.l.a);
}

static Value *list_set(List *l) {
    Value *s = mk_set(l->n);
    if (l->n) memcpy(s->u.set.elems, l->v, sizeof(Value *) * (size_t)l->n);
    return set_normalize(s);
}

static int lazy_is_infinite(Value *s) {
    switch (s->lazy) {
    case L_NAT: case L_INT: case L_STRING: case L_SEQ: case L_ANY: return 1;
    case L_SUBSET: case L_FILTER: case L_UNION: return set_is_infinite(s->u.l.a);
    case L_FCNSET: case L_CUP: return set_is_infinite(s->u.l.a) || set_is_infinite(s->u.l.b);
    case L_CAP: return set_is_infinite(s->u.l.a) && set_is_infinite(s->u.l.b);
    case L_DIFF: return set_is_infinite(s->u.l.a);
    case L_RCDSET: case L_TIMES:
        for (int i = 0; i < s->n; i++) if (set_is_infinite(s->u.l.names[s->n + i])) return 1;
        return 0;
    }
    return 0;
}

static Value *mk_fcn_from(List *keys, List *vals);

/* All functions from the elements of `dom` (sorted) to elements of `rng`,
   made in the standard order: the last value varies fastest. */
/* Calls fn on each function from the nd keys dom to the set rng in the
   standard order, the last key's value varying fastest, until fn returns
   nonzero. The function is one value, reused: fn copies it to keep it. */
static int each_function(Value **dom, int nd, Value *rng, int range, int (*fn)(Value *f, void *data), void *data) {
    rng = enumerate(rng);
    if (nd && !rng->n) return 0;
    Value *f = NEW(Value);
    f->kind = V_FCN;
    f->n = nd;
    f->range = range && nd;
    f->u.fcn.keys = alloc_raw(sizeof(Value *) * (size_t)nd);   /* the copies share them */
    if (nd) memcpy(f->u.fcn.keys, dom, sizeof(Value *) * (size_t)nd);
    f->u.fcn.vals = alloc_raw(sizeof(Value *) * (size_t)nd);
    int *idx = xcalloc((size_t)nd + 1, sizeof(int)), r = 0;
    for (;;) {
        f->u.fcn.hash = 0;
        f->u.fcn.source = NULL;
        for (int i = 0; i < nd; i++) f->u.fcn.vals[i] = rng->u.set.elems[idx[i]];
        if ((r = fn(f, data))) break;
        int i = nd - 1;
        for (; i >= 0; i--) { if (++idx[i] < rng->n) break; idx[i] = 0; }
        if (i < 0) break;
    }
    free(idx);
    return r;
}

static Value *fcn_copy(Value *f) {
    Value *c = NEW(Value);
    *c = *f;
    c->u.fcn.vals = alloc_raw(sizeof(Value *) * (size_t)f->n);
    if (f->n) memcpy(c->u.fcn.vals, f->u.fcn.vals, sizeof(Value *) * (size_t)f->n);
    return c;
}

static int function_keep(Value *f, void *out) { Value *o = out; o->u.set.elems[o->n++] = fcn_copy(f); return 0; }

static Value *enumerate_functions(Value **dom, int nd, Value *rng, int range) {
    int64_t total = 1;
    Value *r = enumerate(rng);
    for (int i = 0; i < nd; i++) {
        total *= r->n;
        if (total > 100000000) fail("Attempted to enumerate a set of functions with too many elements.");
    }
    Value *out = mk_set((int)total);
    out->n = 0;
    each_function(dom, nd, r, range, function_keep, out);
    return out;
}

/* The elements of a finite set, as a normalized V_SET. */
static _Noreturn void count_infinite(Value *s);

static Value *cup_merge(Value *a, Value *b);
static _Noreturn void sort_error(Value *a, Value *b);
static Value **elements_slot(Value *s);
static Value *enumerate_lazy(Value *s);

static Value *enumerate_other(Value *s) {
    if (s->kind == V_INTERVAL) {
        Value *r = mk_set(interval_size(s));
        for (int i = 0; i < s->n; i++) r->u.set.elems[i] = mk_int(s->u.range.lo + i);
        return r;
    }
    if (s->kind != V_LAZY) fail("Attempted to enumerate %s, which is not a set.", pretty(s));
    Value **slot = elements_slot(s);
    if (!slot) return enumerate_lazy(s);
    if (!*slot) {
        Arena *saved = arena;
        arena = &perm_arena;
        *slot = enumerate_lazy(s);
        arena = saved;
    }
    return *slot;
}

/* Where a lazy set made in the permanent arena keeps its elements, if it
   holds no context: they never change. */
static Value **elements_slot(Value *s) {
    if (!s->perm) return NULL;
    switch (s->lazy) {
    case L_SUBSET: case L_TIMES: case L_RCDSET: return &s->u.l.b;
    case L_FCNSET: return &s->u.l.set;
    default: return NULL;
    }
}

/* The domain of [D -> R] enumerated, as TLC fails for one it cannot hold
   as its elements, Nat or Seq(S), or a range it cannot enumerate. */
static Value *fcnset_domain(Value *s) {
    if (user_set(s->u.l.a))
        fail("Attempted to enumerate a set of the form [D -> R],but the domain D:\n%s\ncannot be enumerated.", pretty(s->u.l.a));
    Value *dom = enumerate(s->u.l.a);
    if (set_is_infinite(s->u.l.b))
        fail("Attempted to enumerate a set of the form [D -> R],but the range R:\n%s\ncannot be enumerated.", pretty(s->u.l.b));
    return dom;
}

/* Steps c, k of n indices in increasing order, to the next such in
   order; 0 after the last. */
static int next_combination(int *c, int k, int n) {
    int i = k - 1;
    while (i >= 0 && c[i] == n - k + i) i--;
    if (i < 0) return 0;
    c[i]++;
    for (int j = i + 1; j < k; j++) c[j] = c[j - 1] + 1;
    return 1;
}

/* Calls fn on each subset of the set base in the standard order: smaller
   subsets first, then those of each size in the order of their elements;
   so nothing to sort; until fn returns nonzero. The subset is one value,
   reused: fn copies it to keep it. */
static int each_subset(Value *base, int (*fn)(Value *sub, void *data), void *data) {
    int n = base->n, c[64];
    if (n > 64) fail("Attempted to enumerate SUBSET of a set with too many elements.");
    Value *sub = mk_set(n);
    for (int k = 0; k <= n; k++) {
        for (int i = 0; i < k; i++) c[i] = i;
        do {
            sub->n = k;
            sub->u.set.hash = 0;
            sub->u.set.source = NULL;
            for (int i = 0; i < k; i++) sub->u.set.elems[i] = base->u.set.elems[c[i]];
            int r = fn(sub, data);
            if (r) return r;
        } while (next_combination(c, k, n));
    }
    return 0;
}

static Value *set_copy(Value *s) {
    Value *c = mk_set(s->n);
    memcpy(c->u.set.elems, s->u.set.elems, sizeof(Value *) * (size_t)s->n);
    return c;
}

static Value *filter_member_test(Value *s, Value *v);

/* {x \in S : p} of S SUBSET T or [D -> R], as TLC enumerates it: each
   element of S in turn, given to fn if p holds, never all at once. What
   testing one makes is dropped: in its region, or for the permanent
   arena, which has none, in an arena of its own. */
typedef struct { Value *filter; int (*fn)(Value *, void *); void *data; Arena *own; } Filter;
static Value *fcn_copy(Value *f);
static int filter_one(Value *x, void *data) {
    Filter *f = data;
    Arena *saved = arena;
    if (f->own) arena = f->own;
    Region *r = region_open();
    Value *holds = filter_member_test(f->filter, x);
    region_close(r);
    if (f->own) arena_reset(f->own), arena = saved;
    return holds == TRUEV ? f->fn(x->kind == V_SET ? set_copy(x) : fcn_copy(x), f->data) : 0;
}

static int list_keep(Value *v, void *l) { list_add(l, v); return 0; }

/* Calls fn on each element of the filter s in turn, until it returns
   nonzero: of SUBSET T or [D -> R], without making them all. */
static Value *filter_base(Value *s);
static int each_function(Value **dom, int nd, Value *rng, int range, int (*fn)(Value *f, void *data), void *data);
static int each_filtered(Value *s, int (*fn)(Value *, void *), void *data) {
    Value *in = s->u.l.a;
    Arena own = {0};
    Filter f = {s, fn, data, arena == &perm_arena ? &own : NULL};
    int r = 0, streamed = 1;
    if (in->kind == V_LAZY && in->lazy == L_SUBSET && !in->u.l.b && !set_is_infinite(in->u.l.a)) {
        Value *base = enumerate(in->u.l.a);
        fp_enter(in->u.l.expr);
        r = each_subset(base, filter_one, &f);
        fp_leave(in->u.l.expr);
    } else if (in->kind == V_LAZY && in->lazy == L_FCNSET && !in->u.l.set) {
        fp_enter(in->u.l.expr);
        Value *dom = fcnset_domain(in);
        r = each_function(dom->u.set.elems, dom->n, in->u.l.b, in->u.l.a->kind == V_INTERVAL, filter_one, &f);
        fp_leave(in->u.l.expr);
    } else {
        streamed = 0;
    }
    arena_free(&own);
    if (streamed) return r;
    Value *base = filter_base(s);
    for (int i = 0; i < base->n; i++) {
        int r = filter_member_test(s, base->u.set.elems[i]) == TRUEV ? fn(base->u.set.elems[i], data) : 0;
        if (r) return r;
    }
    return 0;
}

static Value *enumerate_lazy(Value *s) {
    switch (s->lazy) {
    /* A set TLC made with a source names it if enumerating it fails. */
    case L_SUBSET: {
        fp_enter(s->u.l.expr);
        if (set_is_infinite(s->u.l.a)) count_infinite(s->u.l.a);
        Value *base = enumerate(s->u.l.a);
        if (base->n >= 31) fail("Overflow when computing the number of elements in:\n%s", pretty(s));   /* TLC's size() */
        if (base->n > 24) fail("Attempted to enumerate SUBSET of a set with too many elements.");
        /* In the standard order, as each_subset, each subset made in place. */
        int n = base->n, at = 0, c[24];
        Value *out = mk_set(1 << n);
        for (int k = 0; k <= n; k++) {
            for (int i = 0; i < k; i++) c[i] = i;
            do {
                Value *sub = out->u.set.elems[at++] = mk_set(k);
                for (int i = 0; i < k; i++) sub->u.set.elems[i] = base->u.set.elems[c[i]];
            } while (next_combination(c, k, n));
        }
        fp_leave(s->u.l.expr);
        return out;
    }
    case L_FCNSET: {
        fp_enter(s->u.l.expr);
        Value *dom = fcnset_domain(s);
        Value *out = enumerate_functions(dom->u.set.elems, dom->n, s->u.l.b, s->u.l.a->kind == V_INTERVAL);
        fp_leave(s->u.l.expr);
        return out;
    }
    case L_RCDSET: case L_TIMES: {
        fp_enter(s->u.l.expr);
        int n = s->n;
        Value **sets = NEWN(Value *, n);
        int64_t total = 1;
        for (int i = 0; i < n; i++) {
            Value *part = s->u.l.names[n + i];
            if (set_is_infinite(part) && s->lazy == L_TIMES)
                fail("Attempted to enumerate a set of the form s1 \\X s2 ... \\X sn,\nbut can't enumerate s%d:\n%s", i, pretty(part));
            if (set_is_infinite(part))
                fail("Attempted to enumerate a set of the form [l1 : v1, ..., ln : vn],\n"
                     "but can't enumerate the value of the `%s' field:\n%s", S(s->u.l.names[i]->u.i), pretty(part));
            sets[i] = enumerate(part);
            total *= sets[i]->n;
            if (total > 100000000) fail("Attempted to enumerate a set with too many elements.");
        }
        /* Made in the standard order, the last part varying fastest: the
           parts, and a record's fields, are sorted. */
        Value *out = mk_set((int)total);
        int *idx = xcalloc((size_t)n + 1, sizeof(int));
        for (int64_t k = 0; k < total; k++) {
            Value *t;
            if (s->lazy == L_TIMES) {
                t = mk_tuple(n);
                for (int i = 0; i < n; i++) t->u.fcn.vals[i] = sets[i]->u.set.elems[idx[i]];
            } else {
                t = mk_fcn(n);
                t->made = MADE_RECORD;
                for (int i = 0; i < n; i++) { t->u.fcn.keys[i] = s->u.l.names[i]; t->u.fcn.vals[i] = sets[i]->u.set.elems[idx[i]]; }
            }
            out->u.set.elems[k] = t;
            for (int i = n - 1; i >= 0; i--) { if (++idx[i] < sets[i]->n) break; idx[i] = 0; }
        }
        free(idx);
        fp_leave(s->u.l.expr);
        return out;
    }
    case L_FILTER: {
        if (s->u.l.b) return s->u.l.b;
        Arena *saved = keeping(s->perm);
        List out = {0};
        Value *in = s->u.l.a;
        if (in->kind == V_LAZY && (in->lazy == L_SUBSET || in->lazy == L_FCNSET)) each_filtered(s, list_keep, &out);
        else {   /* a set held whole: in a loop, not a call for each element */
            Value *base = filter_base(s);
            for (int i = 0; i < base->n; i++)
                if (filter_member_test(s, base->u.set.elems[i]) == TRUEV) list_add(&out, base->u.set.elems[i]);
        }
        Value *set = list_set(&out);
        /* Keep the elements unless they would outlive the filter's arena. */
        if (may_keep(s)) s->u.l.b = set;
        arena = saved;
        return set;
    }
    case L_UNION: {
        /* As TLC: each element enumerated, unless it is a set it defines. */
        if (s->u.l.b) return s->u.l.b;
        Arena *saved = keeping(s->perm);
        union_sets(s);
        List l = {0};
        fp_enter(s->u.l.expr);
        for (int i = 0; i < s->u.l.a->n; i++) {
            Value *t = s->u.l.a->u.set.elems[i];
            if (!is_set(t) || user_set(t)) fail("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
            t = enumerate(t);
            for (int j = 0; j < t->n; j++) list_add(&l, t->u.set.elems[j]);
        }
        Value *set = list_set(&l);
        fp_leave(s->u.l.expr);
        if (may_keep(s)) s->u.l.b = set;
        arena = saved;
        return set;
    }
    case L_CUP: case L_CAP: case L_DIFF: {
        /* As TLC: S \cup T of both, S \cap T of an enumerable one, S \ T of S. */
        if (s->u.l.set) return s->u.l.set;
        Arena *saved = keeping(s->perm);
        Value *a = s->u.l.a, *b = s->u.l.b, *set;
        fp_enter(s->u.l.expr);
        if (s->lazy == L_CUP) {
            if (!enumerable(a) || !enumerable(b))
                fail("Attempted to enumerate S \\cup T when S:\n%s\nand T:\n%s\nare not both enumerable", pretty(a), pretty(b));
            if (kinds_differ(enumerate(a), enumerate(b))) sort_error(a, b);
            set = cup_merge(a, b);
        } else if (s->lazy == L_CAP) {
            if (enumerable(a)) set = select_members(a, b, 1);
            else if (enumerable(b)) set = select_members(b, a, 1);
            else fail("Attempted to enumerate S \\cap T when neither S:\n%s\nnor T:\n%s\nis enumerable", pretty(a), pretty(b));
        } else {
            if (!enumerable(a)) fail("Attempted to enumerate S \\ T when S:\n%s\nis not enumerable.", pretty(a));
            set = select_members(a, b, 0);
        }
        fp_leave(s->u.l.expr);
        if (may_keep(s)) s->u.l.set = set;
        arena = saved;
        return set;
    }
    default:
        fail("TLC encountered a non-enumerable quantifier bound\n%s.", pretty(s));
    }
}

static Value *normalize_set(Value *v) { return enumerate(v); }

/* The sets of a UNION TLC keeps, sorted once it must: comparing them, an
   error names the UNION and the set of them. */
static Value *union_sets(Value *s) {
    if (s->n) {   /* in place: in its own arena */
        Arena *saved = arena;
        if (s->perm) arena = &perm_arena;
        Expr *sets = s->u.l.a->u.set.source;
        fp_enter(s->u.l.expr);
        fp_enter(sets);
        held_by(s);
        s->u.l.a = set_normalize(s->u.l.a);
        fp_leave(sets);
        fp_leave(s->u.l.expr);
        s->n = 0;
        arena = saved;
    }
    return s->u.l.a;
}

/* As TLC's UnionValue once it compares, counts or fingerprints itself:
   it keeps its elements, which x \in U then takes in order. */
static Value *union_cache(Value *s) {
    if (s->kind == V_LAZY && s->lazy == L_UNION && !s->u.l.set) {
        Arena *saved = keeping(s->perm);
        Value *e = enumerate(s);
        if (may_keep(s)) s->u.l.set = e;
        arena = saved;
    }
    return s;
}

/* The elements of s as TLC's x \in s takes them in Init and Next (its
   quantifiers take them sorted): a UNION it keeps, those of each of its
   sets in turn, duplicates too; another set, in order. Only to iterate:
   the result is no normalized set. */
static Value *elements(Value *s) {
    if (s->kind != V_LAZY || s->lazy != L_UNION) return enumerate(s);
    if (s->u.l.set) return s->u.l.set;
    union_sets(s);
    List l = {0};
    fp_enter(s->u.l.expr);
    for (int i = 0; i < s->u.l.a->n; i++) {
        Value *t = s->u.l.a->u.set.elems[i];
        if (!is_set(t) || user_set(t)) fail("Attempted to enumerate UNION(s), but some element of s is nonenumerable.");
        t = elements(t);
        for (int j = 0; j < t->n; j++) list_add(&l, t->u.set.elems[j]);
    }
    fp_leave(s->u.l.expr);
    Value *r = mk_set(l.n);
    if (l.n) memcpy(r->u.set.elems, l.v, sizeof(Value *) * (size_t)l.n);
    return r;
}

/* TLC's error counting an infinite set: the first part it cannot count. */
static _Noreturn void count_infinite(Value *s) {
    for (Value *part = s; part; ) {
        s = part, part = NULL;
        if (user_set(s)) fail("Attempted to compute the number of elements in the overridden value %s.", pretty(s));
        if (s->lazy == L_SUBSET || s->lazy == L_FCNSET) part = set_is_infinite(s->u.l.a) ? s->u.l.a : s->u.l.b;
        if (s->lazy == L_RCDSET || s->lazy == L_TIMES)
            for (int i = 0; i < s->n && !part; i++) if (set_is_infinite(s->u.l.names[s->n + i])) part = s->u.l.names[s->n + i];
    }
    enumerate(s);   /* fails, as s is infinite */
    abort();
}

/* Lazy functions compared are computed, the left first; TLC cannot count
   an infinite domain. */
static void realize_both(Value **a, Value **b) {
    *a = realize(*a);
    if ((*a)->kind == V_LAMBDA) count_infinite((*a)->u.l.a);
    *b = realize(*b);
    if ((*b)->kind == V_LAMBDA) count_infinite((*b)->u.l.a);
}

/* The number of elements of a finite set, without enumerating a product of
   sets, or -1 when it is not a 32-bit int, TLC's count. */
static int64_t set_size(Value *s) {
    if (s->kind == V_INTERVAL) return interval_size(s);
    if (s->kind != V_LAZY || (s->lazy != L_SUBSET && s->lazy != L_FCNSET && s->lazy != L_RCDSET && s->lazy != L_TIMES))
        return enumerate(s)->n;
    int64_t n = 1, k;
    if (s->lazy == L_SUBSET) {
        if ((k = set_size(s->u.l.a)) < 0 || k > 30) return -1;
        return (int64_t)1 << k;
    }
    if (s->lazy == L_FCNSET) {
        int64_t r = set_size(s->u.l.b);
        if ((k = set_size(s->u.l.a)) < 0 || r < 0) return -1;
        for (; k > 0 && n; k--) if ((n *= r) > 2147483647) return -1;
        return n;
    }
    for (int i = 0; i < s->n; i++)
        if ((k = set_size(s->u.l.names[s->n + i])) < 0 || (n *= k) > 2147483647) return -1;
    return n;
}

static int set_member(Value *v, Value *s);

static int all_members(Value *sub, Value *s) {
    Value *e = enumerate(sub);
    for (int i = 0; i < e->n; i++) if (!set_member(e->u.set.elems[i], s)) return 0;
    return 1;
}

/* S \subseteq T, as TLC's isSubsetEq: SUBSET A \subseteq SUBSET B as
   A \subseteq B, an interval in an interval by their bounds, else each
   element of S in T. An error inside S, made with a source, is one TLC
   cannot fingerprint. */
static int subseteq(Value *a, Value *b) {
    Expr *src = a->kind == V_LAZY ? a->u.l.expr : a->kind == V_SET ? a->u.set.source : NULL;
    fp_enter(src);
    int r;
    if (a->kind == V_LAZY && a->lazy == L_SUBSET && b->kind == V_LAZY && b->lazy == L_SUBSET && !user_set(a->u.l.a))
        r = subseteq(a->u.l.a, b->u.l.a);
    else if (a->kind == V_INTERVAL && b->kind == V_INTERVAL && b->u.range.lo <= a->u.range.lo && b->u.range.hi >= a->u.range.hi)
        r = 1;
    else
        r = all_members(a, b);
    fp_leave(src);
    return r;
}

/* TLC's error testing membership in a value that is not a set. */
static _Noreturn void not_a_set(Value *v, Value *s) {
    if (s->kind == V_TUPLE) fail("Attempted to check set membership in a tuple value.");
    if (s->kind == V_FCN && s->made == MADE_RECORD) fail("Attempted to check if element:\n%s\nis in the record:\n%s", pretty(v), pretty(s));
    fail("Attempted to check if the value:\n%s\nis an element of the %s %s", pretty(v),
         s->kind == V_FCN || s->kind == V_LAMBDA ? "function" : kind_name(s), pretty(s));
}

static int set_member(Value *v, Value *s) {
    if (!is_set(s)) not_a_set(v, s);
    v = realize(v);
    switch (s->kind) {
    case V_SET: {
        int lo = 0, hi = s->n;
        if (v->kind == V_MODEL || (s->n && s->u.set.elems[0]->kind == V_MODEL)) {
            for (int i = 0; i < s->n; i++) if (veq(v, s->u.set.elems[i])) return 1;
            return 0;
        }
        if (s->u.set.product && v->kind == V_TUPLE) {   /* the search below, as a product of intervals */
            Value *p = s->u.set.product;
            int in = v->n == p->n;
            for (int i = 0; i < v->n; i++) {
                Value *x = v->u.fcn.vals[i], *part = in ? p->u.l.names[p->n + i] : NULL;
                if (x->kind != V_INT || (part && part->kind != V_INTERVAL)) goto search;
                in = in && x->u.i >= part->u.range.lo && x->u.i <= part->u.range.hi;
            }
            return in;
        }
    search:
        /* TLC's search: its probes decide which element an error names. */
        while (lo < hi) {
            int mid = (lo + hi) >> 1;
            int c = vcmp_quick(v, s->u.set.elems[mid]);
            if (!c) return 1;
            if (c < 0) hi = mid; else lo = mid + 1;
        }
        return 0;
    }
    case V_INTERVAL:
        if (v->kind != V_INT) {
            if (v->kind == V_MODEL || !s->n) return 0;   /* TLC finds nothing in an empty interval */
            fail("Attempted to check if the value:\n%s\nis in the integer interval %s", pretty(v), pretty(s));
        }
        return v->u.i >= s->u.range.lo && v->u.i <= s->u.range.hi;
    case V_LAZY:
        switch (s->lazy) {
        case L_NAT: case L_INT: case L_STRING:
            if (v->kind == V_MODEL) return 0;
            if (v->kind != (s->lazy == L_STRING ? V_STR : V_INT))
                fail_module("Attempted to check if the value:\n%s\nis an element of %s.", pretty(v),
                            s->lazy == L_NAT ? "Nat" : s->lazy == L_INT ? "Int" : "STRING");
            return s->lazy != L_NAT || v->u.i >= 0;
        case L_ANY: return 1;
        case L_SUBSET:
            if (!is_set(v)) fail("Attempted to check if the non-enumerable value\n%s\nis element of\n%s", pretty(v), pretty(s));
            return all_members(v, s->u.l.a);
        case L_SEQ:
            if (!is_fcn(v) || !fcn_is_tuple(v))
                fail_module("Attempted to check if the value:\n%s\nis an element of %s.", pretty(v), pretty(s));
            for (int i = 0; i < v->n; i++) if (!set_member(v->u.fcn.vals[i], s->u.l.a)) return 0;
            return 1;
        case L_FCNSET: {
            if (!is_fcn(v))
                fail("Attempted to check if \n%s\nwhich is not a TLC function value, is in the set of functions:\n%s", pretty(v), pretty(s));
            Value *dom = enumerate(s->u.l.a);
            if (dom->n != v->n) return 0;
            for (int i = 0; i < v->n; i++) {
                if (!veq(fcn_key(v, i), dom->u.set.elems[i])) return 0;
                if (!set_member(v->u.fcn.vals[i], s->u.l.b)) return 0;
            }
            return 1;
        }
        case L_RCDSET: {
            if (!is_fcn(v) || !(v->n == 0 || fcn_is_record(v)))
                fail("Attempted to check if non-record\n%s\nis in the set of records:\n%s", pretty(v), pretty(s));
            if (v->kind != V_FCN || v->n != s->n) return 0;
            for (int i = 0; i < s->n; i++) {
                if (!veq(v->u.fcn.keys[i], s->u.l.names[i])) return 0;
                if (!set_member(v->u.fcn.vals[i], s->u.l.names[s->n + i])) return 0;
            }
            return 1;
        }
        case L_TIMES: {
            if (!is_fcn(v) || !fcn_is_tuple(v))
                fail("Attempted to check if non-tuple\n%s\nis in the set of tuples:\n%s", pretty(v), pretty(s));
            if (v->n != s->n) return 0;
            for (int i = 0; i < s->n; i++) if (!set_member(v->u.fcn.vals[i], s->u.l.names[s->n + i])) return 0;
            return 1;
        }
        case L_FILTER:
            if (s->u.l.b) return set_member(v, s->u.l.b);
            return set_member(v, s->u.l.a) && filter_member_test(s, v) == TRUEV;
        case L_UNION:
            union_sets(s);
            for (int i = 0; i < s->u.l.a->n; i++) if (set_member(v, s->u.l.a->u.set.elems[i])) return 1;
            return 0;
        case L_CUP: case L_CAP: case L_DIFF: {
            fp_enter(s->u.l.expr);
            int in = set_member(v, s->u.l.a);
            if (s->lazy == L_CUP ? !in : in) in = set_member(v, s->u.l.b) == (s->lazy != L_DIFF);
            fp_leave(s->u.l.expr);
            return in;
        }
        }
        return 0;
    default:
        fail("Attempted to check if the value:\n%s\nis an element of %s.", pretty(v), pretty(s));
    }
}

/* A set operation whose result may be infinite stays lazy (§7). */
static Value *lazy_op(int kind, Value *a, Value *b) {
    Value *s = mk_lazy(kind);
    s->u.l.a = a;
    s->u.l.b = b;
    return s;
}

/* A set TLC holds as its elements: one it computes filters and functions
   over at once (TLC's Reducible). */
static int reducible(Value *s) {
    return s->kind == V_INTERVAL || (s->kind == V_SET && s->made != MADE_HELD);
}

/* s, as a set TLC holds as its definition. */
static Value *held(Value *s) {
    if (s->kind != V_SET || s->made == MADE_HELD) return s;
    Value *t = NEW(Value);
    *t = *s;
    t->made = MADE_HELD;
    return t;
}

/* TLC's error making S \cup T of elements that do not compare: it looks
   for each of T's in S, an interval by its bounds, another comparing for
   equality. */
static _Noreturn void cup_error(Value *a, Value *b) {
    for (int j = 0; j < b->n; j++) {
        if (a->kind == V_INTERVAL) set_member(b->u.set.elems[j], a);
        else for (int i = 0; i < a->n; i++) veq(a->u.set.elems[i], b->u.set.elems[j]);
    }
    abort();
}

/* TLC's error enumerating S \cup T it keeps as its definition, of
   elements that do not compare: it sorts S's and then T's by binary
   insertion. */
static _Noreturn void sort_error(Value *a, Value *b) {
    a = enumerate(a); b = enumerate(b);
    Value **v = NEWN(Value *, a->n + b->n);
    memcpy(v, a->u.set.elems, a->n * sizeof *v);
    memcpy(v + a->n, b->u.set.elems, b->n * sizeof *v);
    for (int i = 1, n = 1; i < a->n + b->n; i++) {
        int lo = 0, hi = n, idx = 0, c = 0;
        while (lo < hi) {
            idx = lo + (hi - lo) / 2;
            if (!(c = vcmp(v[i], v[idx]))) break;
            if (c < 0) hi = idx; else lo = idx + 1;
        }
        if (c) {
            idx = c < 0 ? idx : idx + 1;
            Value *e = v[i];
            memmove(v + idx + 1, v + idx, (n - idx) * sizeof *v);
            v[idx] = e;
            n++;
        }
    }
    abort();
}

/* The kind of a set's elements but model values, which compare with any
   value; -1 if it has no other. */
static int elem_kind(Value *s) {
    for (int i = 0; i < s->n; i++) {
        Value *e = s->u.set.elems[i];
        if (e->kind != V_MODEL) return is_fcn(e) ? V_FCN : is_set(e) ? V_SET : e->kind;
    }
    return -1;
}

/* Whether two enumerated sets have elements that do not compare. */
static int kinds_differ(Value *a, Value *b) {
    int ka = elem_kind(a), kb = elem_kind(b);
    return ka >= 0 && kb >= 0 && ka != kb;
}

/* S \cup T of two finite sets, enumerated. */
static Value *cup_merge(Value *s, Value *b) {
    Value *a = enumerate(s);
    b = enumerate(b);
    if (!b->n) return a;
    if (!a->n) return b;
    if (kinds_differ(a, b)) cup_error(s->kind == V_INTERVAL ? s : a, b);
    /* Both are sorted: merge them. */
    Value *r = mk_set(a->n + b->n);
    Value **x = a->u.set.elems, **y = b->u.set.elems, **out = r->u.set.elems;
    int i = 0, j = 0, k = 0;
    while (i < a->n && j < b->n) {
        int c = vcmp(x[i], y[j]);
        out[k++] = c <= 0 ? x[i] : y[j];
        i += c <= 0;
        j += c >= 0;
    }
    while (i < a->n) out[k++] = x[i++];
    while (j < b->n) out[k++] = y[j++];
    r->n = k;
    return r;
}

/* TLC enumerates S \cup T only of two sets it holds as their elements; it
   keeps another as its definition, the enumerated first, unless that is
   empty. */
static Value *set_union(Value *a, Value *b) {
    if (reducible(a) && reducible(b)) return cup_merge(a, b);
    if (reducible(a) && !a->n) return b;
    if (reducible(b) && !b->n) return a;
    return reducible(b) ? lazy_op(L_CUP, b, a) : lazy_op(L_CUP, a, b);
}

static int enumerable(Value *s) { return is_set(s) && !set_is_infinite(s); }

/* The elements of s that are in t, or not: in order, as they are in s. */
static Value *select_members(Value *s, Value *t, int in) {
    s = enumerate(s);
    Value *r = mk_set(s->n);
    int k = 0;
    for (int i = 0; i < s->n; i++) if (set_member(s->u.set.elems[i], t) == in) r->u.set.elems[k++] = s->u.set.elems[i];
    r->n = k;
    return r;
}

/* As TLC: S \cap T and S \ T of an enumerated set are its elements in T,
   or not; others are kept as their definitions. */
static Value *set_inter(Value *a, Value *b) {
    if (reducible(a)) return select_members(a, b, 1);
    if (reducible(b)) return select_members(b, a, 1);
    return lazy_op(L_CAP, a, b);
}

static Value *set_minus(Value *a, Value *b) {
    return reducible(a) ? select_members(a, b, 0) : lazy_op(L_DIFF, a, b);
}

/* ---------------------------------------------------------------- functions */

static Value *lambda_apply(Value *f, Value *a);

/* The index of a in the domain of the function or tuple f, or -1. */
static int fcn_index(Value *f, Value *a) {
    if (f->kind == V_TUPLE) return a->kind == V_INT && a->u.i >= 1 && a->u.i <= f->n ? (int)a->u.i - 1 : -1;
    int models = f->n && f->u.fcn.keys[0]->kind == V_MODEL && f->u.fcn.keys[f->n - 1]->kind == V_MODEL;
    if (a->kind == V_MODEL ? !models : f->n && f->u.fcn.keys[0]->kind == V_MODEL) {
        /* A domain mixing model values with others: compare for equality. */
        for (int i = 0; i < f->n; i++) if (veq(a, f->u.fcn.keys[i])) return i;
        return -1;
    }
    if (f->n && (a->kind == V_INT || a->kind == V_MODEL) && f->u.fcn.keys[0]->kind == a->kind) {
        /* A domain of consecutive numbers or model values: index it. */
        int64_t i = a->u.i - f->u.fcn.keys[0]->u.i;
        if (i >= 0 && i < f->n && f->u.fcn.keys[i]->kind == a->kind && f->u.fcn.keys[i]->u.i == a->u.i) return (int)i;
    }
    /* Probing as TLC tests membership in a function's domain. */
    int lo = 0, hi = f->n;
    while (lo < hi) {
        int mid = (lo + hi) >> 1;
        int c = vcmp_quick(a, f->u.fcn.keys[mid]);
        if (!c) return mid;
        if (c < 0) hi = mid; else lo = mid + 1;
    }
    return -1;
}

/* Applies f to the argument a. */
static Value *fcn_apply(Value *f, Value *a, Expr *where) {
    if (f->kind == V_LAMBDA) return lambda_apply(f, a);
    if (!is_fcn(f)) fail_at(where, "A non-function (%s) was applied as a function.", kind_string(f));
    if (f->made == MADE_RECORD && a->kind != V_STR) fail("Attempted to access record by a non-string argument: %s", pretty(a));
    int i = fcn_index(f, a);
    if (i >= 0) return f->u.fcn.vals[i];
    if (f->kind == V_TUPLE) {
        fp_enter(f->u.fcn.source);   /* TLC cannot fingerprint the tuple */
        if (a->kind != V_INT) fail("Attempted to access tuple at a non integral index: %s", pretty(a));
        fail("Attempted to access index %lld of tuple\n%s\nwhich is out of bounds.", (long long)a->u.i, pretty(f));
    }
    if (f->made == MADE_RECORD) fail("Attempted to access nonexistent field '%s' of record\n%s", S(a->u.i), pretty(f));
    if (f->made >= MADE_LAMBDA)
        fail("In applying the function\n%s,\nthe first argument is:\n%s\nwhich is not in its domain.\n", pretty(f), pretty(a));
    fail("Attempted to apply function:\n%s\nto argument %s, which is not in the domain of the function.",
         pretty(f), pretty(a));
}

static Value *fcn_domain(Value *f) {
    if (f->kind == V_LAMBDA) return f->u.l.a;
    if (f->kind == V_TUPLE) return mk_interval(1, f->n);
    if (f->range && f->made != MADE_RECORD) return mk_interval(f->u.fcn.keys[0]->u.i, f->u.fcn.keys[f->n - 1]->u.i);
    Value *s = mk_set(f->n);
    for (int i = 0; i < f->n; i++) s->u.set.elems[i] = f->u.fcn.keys[i];
    return s;
}

typedef struct { Value *k, *v; } Pair;

static int cmp_pair(const void *x, const void *y) { return vcmp(((Pair *)x)->k, ((Pair *)y)->k); }

/* A function from parallel lists of keys and values, sorted by key. */
static Value *mk_fcn_from(List *keys, List *vals) {
    int n = keys->n;
    Pair *p = NEWN(Pair, n);
    for (int i = 0; i < n; i++) { p[i].k = keys->v[i]; p[i].v = vals->v[i]; }
    if (n > 1) qsort(p, (size_t)n, sizeof(Pair), cmp_pair);
    Value *f = mk_fcn(n);
    for (int i = 0; i < n; i++) { f->u.fcn.keys[i] = p[i].k; f->u.fcn.vals[i] = p[i].v; }
    return f;
}

/* A copy of f whose value at key is val; key must be in the domain. */
static inline uint64_t pair_hash(Value *f, int i, Value *val);

/* f with the value val at key, which is its i-th argument unless f is a lambda. */
static Value *fcn_update(Value *f, int i, Value *key, Value *val) {
    Value *g = NEW(Value);
    *g = *f;
    if (f->kind == V_LAMBDA) {
        g->n = f->n + 1;
        g->u.l.names = NEWN(Value *, 2 * g->n);
        if (f->n) memcpy(g->u.l.names, f->u.l.names, sizeof(Value *) * 2 * (size_t)f->n);
        g->u.l.names[2 * f->n] = key;
        g->u.l.names[2 * f->n + 1] = val;
        return g;
    }
    g->u.fcn.vals = alloc_raw(sizeof(Value *) * (size_t)f->n);
    memcpy(g->u.fcn.vals, f->u.fcn.vals, sizeof(Value *) * (size_t)f->n);
    g->u.fcn.vals[i] = val;
    g->u.fcn.source = NULL;   /* a tuple TLC makes anew */
    /* Kept up to date only with a hash known: TLC hashes a set when it
       fingerprints the state, where an error is its own. */
    int known = val->kind <= V_MODEL || (val->kind == V_SET ? val->u.set.hash != 0
              : (val->kind == V_TUPLE || val->kind == V_FCN) && val->u.fcn.hash != 0);
    if (f->u.fcn.hash && known) g->u.fcn.hash = f->u.fcn.hash - pair_hash(f, i, f->u.fcn.vals[i]) + pair_hash(f, i, val);
    else g->u.fcn.hash = 0;
    return g;
}

/* ---------------------------------------------------------------- syntax */

enum { T_EOF, T_IDENT, T_NUM, T_STR, T_OP, T_KW, T_SEP, T_END, T_STEP };   /* T_STEP: a proof step, <1>2. */

typedef struct {
    int kind;
    int id;              /* interned text of an identifier, numeral, operator, or keyword */
    int64_t num;
    const char *text;    /* a string literal's contents, unescaped */
    int len;
    int line, col, eline, ecol;
    const char *notes;   /* the comments before it, if they may hold annotations: @type */
} Tok;

/* Expression kinds. The parser produces the X_ kinds; the resolver turns
   names and operator applications into the kinds after X_RESOLVED. */
enum {
    X_NUM, X_STR, X_BOOL, X_NAME, X_OP, X_AT, X_LAMBDA, X_OPREF,
    X_SETENUM, X_TUPLE, X_RECORD, X_RCDSET, X_FCNSET, X_FCN, X_APPLY, X_DOT, X_EXCEPT,
    X_FILTER, X_MAP, X_FORALL, X_EXISTS, X_CHOOSE, X_IF, X_CASE, X_LET,
    X_SQACT, X_ANGLEACT, X_WF, X_SF, X_TFORALL, X_TEXISTS,
    X_RESOLVED,
    /* resolved */
    K_BOUND,     /* a bound name or operator parameter: def */
    K_DECL,      /* a constant or variable: def */
    K_CALL,      /* a definition applied to args: def */
    K_PARAMCALL, /* an operator parameter applied to args: def */
    K_INSTCALL,  /* a definition reached through instances: path in defs, final def */
    K_BOOLEAN, K_STRINGSET,
    K_AND, K_OR, K_NOT, K_IMPLIES, K_EQUIV, K_EQ, K_NEQ, K_IN, K_NOTIN,
    K_CUP, K_CAP, K_SETMINUS, K_SUBSETEQ, K_SUBSET, K_UNION, K_DOMAIN,
    K_PRIME, K_UNCHANGED, K_ENABLED, K_ALWAYS, K_EVENTUALLY, K_LEADSTO, K_TIMES, K_CDOT, K_WHILE
};

typedef struct {
    int n;
    int *names;
    Def **defs;     /* filled by the resolver */
    int tuple;      /* <<a, b>> \in S */
    Expr *set;      /* NULL for an unbounded binding */
    int line, col;  /* of its first name */
} Bound;

/* A segment of A!B(x)!C, or a subexpression selector (§5.7): !2, !<<, !>>,
   !:, !@ and !(x) are sel > 0 or the SEL_ kinds; a name is sel 0. */
typedef struct { int name; int sel; Expr **args; int n; int line, col; } Seg;   /* line, col: a record field's */
enum { SEL_LL = -1, SEL_GG = -2, SEL_COLON = -3, SEL_AT = -4, SEL_NULL = -5 };

/* lab(x, y) :: e names e, with the bound identifiers x and y, for selectors. */
typedef struct { int name; int n; int *names; Def **defs; } Label;

typedef struct { int n; Expr **keys; int *fields; int line, col; } Path;  /* an EXCEPT path: fields[i] >= 0 for .f; line and col of its ! */

struct Expr {
    short kind;
    unsigned char fixed;  /* fixed_expr: 0 not yet known, 1 yes, 2 no */
    unsigned char made;   /* made by manyan, not written: no frame of TLC's call stack */
    int op;               /* operator or name; field of X_DOT */
    int n;
    int field;            /* X_DOT: where the field was in the last record */
    Expr **args;
    Bound *bounds;
    int nb;
    Def *def;
    Def **defs;           /* LET definitions; instance path of K_INSTCALL */
    int ndefs;
    Seg *segs;            /* X_NAME: A!B(x)!C */
    Label *label;
    int nseg;
    Path *paths;          /* X_EXCEPT */
    int64_t num;
    const char *text;
    int len;
    Module *mod;
    int l1, c1, l2, c2;
    int pl1, pc1, pl2, pc2;   /* with the parentheses around it, if any */
    Value *value;         /* X_SETENUM of literals of one kind, or a fixed product: its value, once computed */
    Inst *inst;           /* K_INSTCALL from the root module through instances without parameters: its chain */
};

enum { D_OP, D_FCN, D_CONST, D_VAR, D_BOUND, D_PARAM, D_INST, D_RECURSIVE, D_THM };   /* D_THM: a theorem's or assumption's name */

typedef Value *(*Native)(Expr *call, Value **args, Ctx c);

struct Def {
    int kind;
    int name;
    int arity;            /* of an operator parameter or declared constant: F(_, _) */
    int nparams;
    Def **params;
    Expr *body;
    Bound *bounds;        /* D_FCN: f[x \in S] == body */
    int nb;
    Module *mod;
    Native native;
    ManyanNative api;        /* a native of manyan_define: native is then n_defined, which marks it */
    int lazy;             /* a native of TLC's evaluation methods: it evaluates the call's arguments itself, unless given values */
    char intop;           /* a native of Naturals on two integers: '<', 'l' (\leq), '>', 'g' (\geq), '+', '-', '*' */
    const char *java;     /* a native's Java method in TLC, as TLC prints it */
    int var_index;        /* D_VAR of the root: index in the state, or -1 */
    Value *value;         /* the configured value of a constant or definition */
    Def *replacement;     /* D_CONST or D_OP replaced by an operator of the configuration */
    int bad_target;       /* the undefined name the configuration replaces it by */
    int level;            /* 0 constant, 1 state, 2 action, 3 temporal; -1 unknown */
    int level_busy;
    Def *level_probe;     /* a LET definition's: the parameter probed when its level was found */
    unsigned level_mask;  /* 1 + twice the bits of the parameters a call's level depends on; 0 unknown */
    int level_bound;      /* TLC's bound on its level, plus 1; 0 unknown */
    int level_max;        /* a parameter's or declaration's: the highest level its uses allow, plus 1; 0 for any */
    int level_checked;
    unsigned level_walk;  /* the walk of subst_level that last entered it */
    Value *cache;         /* a constant definition without parameters, once evaluated */
    int uncached;         /* one that failed as TLC started: evaluated each time, as in TLC */
    int local;
    int recursive;        /* a LET definition declared RECURSIVE: in scope before it */
    int self;             /* D_FCN whose body names it: TLC's RecursiveFcnSpec, always lazy (§6.6) */
    Module *target;       /* D_INST */
    int nsubst;
    Def **subst_decl;
    Expr **subst_expr;
    char *subst_kept;     /* each substitution: 1 if its value is kept for a state (Inst), 2 if not; 0 unknown */
    Module *subst_in;     /* a declaration's: the module subst_at was found for (subst_index) */
    int subst_at;
    Expr *where;          /* the definition's location */
    const char *notes;    /* the comments before it, for annotations: @type */
    int part;             /* a copy whose body is part of the original's, as an instance sees it (in_instance) */
};

static Value *call_native(Def *d, Expr *call, Value **args, Ctx c);

/* A symbol of a module: a definition, reached through `npath` instances. */
typedef struct { int name; Def *def; Def **path; int npath; int local; } Sym;

typedef struct {
    int kind;             /* 0 definition, 1 instance, 2 assume, 3 nested module, 4 name only */
    Def *def;
    Expr *expr;
    Module *module;
    int local;
    Expr *where;          /* an assumption's, from its keyword */
} Unit;

struct Module {
    int name;
    char *path;
    Module *outer;        /* a nested module's enclosing module */
    int nouter_syms;      /* the enclosing module's symbols visible to it */
    Buf warnings;         /* a file's module: SANY's warnings for it, nested modules' too */
    int nwarnings;
    Expr **records;       /* its records and sets of records, as resolved */
    int nrecords;
    int *extends;
    int nextends;
    Sym *syms;
    int nsyms, capsyms;
    Def **decls;          /* constants and variables, own and extended, in order */
    int ndecls, capdecls;
    Unit *units;
    int nunits, capunits;
    Module **nested;
    int nnested;
    Tok *toks;
    int ntoks;
    int resolved;         /* 1 while resolving, 2 after */
    int standard;         /* read from the text of a standard module */
    int instantiated;     /* the target of an INSTANCE */
    Expr *odd[3];         /* its first decimal or too big integer: in a definition, an assumption, a theorem */
};

/* ---------------------------------------------------------------- lexer */

static const char *keywords[] = {
    "ASSUME", "ASSUMPTION", "AXIOM", "BOOLEAN", "CASE", "CHOOSE", "CONSTANT", "CONSTANTS", "DOMAIN", "ELSE",
    "ENABLED", "EXCEPT", "EXTENDS", "FALSE", "IF", "IN", "INSTANCE", "LET", "LOCAL", "MODULE", "OTHER",
    "STRING", "SUBSET", "THEN", "THEOREM", "TRUE", "UNCHANGED", "UNION", "VARIABLE", "VARIABLES",
    "WITH", "WF_", "SF_", "LAMBDA", "RECURSIVE", "LEMMA", "PROPOSITION", "COROLLARY", "PROOF", "BY",
    "OBVIOUS", "OMITTED", "QED", "USE", "HIDE", "DEFS", "DEF", "SUFFICES", "HAVE", "TAKE", "WITNESS",
    "PICK", "NEW", "ACTION", "STATE", "TEMPORAL", "ONLY", NULL};

static const char *symbols[] = {
    "(\\X)", "-+->", "<=>", "...", "::=", "|->", "(+)", "(-)", "(.)", "(/)",
    "<<", ">>", "==", "/=", "<=", ">=", "=<", "=>", "->", "<-", "/\\", "\\/", "..", "::", ":=", ":>",
    "<:", "@@", "~>", "[]", "<>", "++", "--", "**", "//", "^^", "%%", "&&", "||", "$$", "??", "!!",
    "##", "|-", "-|", "|=", "=|", "^+", "^*", "^#", "-.",
    "(", ")", "[", "]", "{", "}", ",", ":", ".", "!", "@", "'", "=", "#", "<", ">", "+", "-", "*",
    "/", "%", "^", "&", "|", "$", "?", "~", "_", "\\", NULL};

static int is_keyword(const char *s, int len) {
    for (int i = 0; keywords[i]; i++)
        if ((int)strlen(keywords[i]) == len && memcmp(keywords[i], s, (size_t)len) == 0) return 1;
    return 0;
}

static int id_char(int c) { return isalnum(c) || c == '_'; }

typedef struct { const char *src; const char *file; int pos, line, col; } Lexer;

static _Noreturn void parse_error(const char *file, int line, int col, const char *fmt, ...);

static void lex_advance(Lexer *L, int n) {
    while (n--) {
        if (L->src[L->pos] == '\n') { L->line++; L->col = 1; }
        else if (L->src[L->pos] == '\t') L->col = ((L->col - 1) / 8 + 1) * 8 + 1;   /* SANY's tab stops */
        else L->col++;
        L->pos++;
    }
}

static int starts_module(Lexer *L) {
    const char *s = L->src + L->pos;
    int i = 0;
    while (s[i] == '-') i++;
    if (i < 4) return 0;
    while (s[i] == ' ' || s[i] == '\t') i++;
    return strncmp(s + i, "MODULE", 6) == 0 && !id_char(s[i + 6]);
}

/* Skips white space and comments. */
static void lex_space(Lexer *L) {
    for (;;) {
        char c = L->src[L->pos];
        if (c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\f') { lex_advance(L, 1); continue; }
        if (c == '\\' && L->src[L->pos + 1] == '*') {
            while (L->src[L->pos] && L->src[L->pos] != '\n') lex_advance(L, 1);
            continue;
        }
        if (c == '(' && L->src[L->pos + 1] == '*') {
            int depth = 0;
            do {
                if (!L->src[L->pos]) parse_error(L->file, L->line, L->col, "Unterminated comment");
                if (L->src[L->pos] == '(' && L->src[L->pos + 1] == '*') { depth++; lex_advance(L, 2); }
                else if (L->src[L->pos] == '*' && L->src[L->pos + 1] == ')') { depth--; lex_advance(L, 2); }
                else lex_advance(L, 1);
            } while (depth > 0);
            continue;
        }
        return;
    }
}

static int digit_value(int c) {
    if (isdigit(c)) return c - '0';
    if (c >= 'a' && c <= 'f') return c - 'a' + 10;
    if (c >= 'A' && c <= 'F') return c - 'A' + 10;
    return 99;
}

/* The tokens of a file's outermost module, interning identifiers and
   numerals in the order they appear (§7.5). */
/* The length of the proof step s begins with, as <1>, <2>3., <*>; 0 if none. */
static int proof_step(const char *s) {
    if (s[0] != '<') return 0;
    int len = isdigit((unsigned char)s[1]) ? 1 + (int)strspn(s + 1, "0123456789") : s[1] == '*' || s[1] == '+' ? 2 : 0;
    if (!len || s[len] != '>') return 0;
    for (len++; id_char(s[len]); len++) {}
    while (s[len] == '.') len++;
    return len;
}

static Tok *lex(const char *src, const char *file, int *count) {
    Lexer L = {src, file, 0, 1, 1};
    Tok *toks = NULL;
    int n = 0, cap = 0, depth = 0;
    /* Text before the module is ignored (§3.2). */
    for (;;) {
        if (!src[L.pos]) parse_error(file, L.line, L.col, "Could not find a module");
        if ((L.pos == 0 || src[L.pos - 1] == '\n' || 1) && src[L.pos] == '-' && starts_module(&L)) break;
        lex_advance(&L, 1);
    }
    for (;;) {
        int gap = L.pos;
        lex_space(&L);
        if (n + 2 >= cap) { cap = cap ? cap * 2 : 1024; toks = xrealloc(toks, sizeof(Tok) * (size_t)cap); }
        Tok *t = &toks[n];
        memset(t, 0, sizeof *t);
        t->line = L.line; t->col = L.col;
        if (memchr(src + gap, '@', (size_t)(L.pos - gap))) t->notes = strndup(src + gap, (size_t)(L.pos - gap));
        const char *s = src + L.pos;
        if (!*s) { t->kind = T_EOF; n++; break; }
        int len = 0;
        if (s[0] == '-' && s[1] == '-' && s[2] == '-' && s[3] == '-') {
            while (s[len] == '-') len++;
            t->kind = T_SEP;
            if (starts_module(&L)) depth++;
        } else if (s[0] == '=' && s[1] == '=' && s[2] == '=' && s[3] == '=') {
            while (s[len] == '=') len++;
            t->kind = T_END;
            depth--;
        } else if (id_char(s[0])) {
            while (id_char(s[len])) len++;
            int digits = 1;
            for (int i = 0; i < len; i++) if (!isdigit((unsigned char)s[i])) digits = 0;
            if (digits) {
                t->kind = T_NUM;
                int64_t v = 0;
                for (int i = 0; i < len; i++) { v = v * 10 + (s[i] - '0'); if (v > 0x7fffffffffffLL) v = 0x7fffffffffffLL; }
                t->num = v;
                if (s[len] == '.' && isdigit((unsigned char)s[len + 1])) {   /* a decimal: -1 */
                    for (len++; isdigit((unsigned char)s[len]); len++) {}
                    t->num = -1;
                }
                t->id = intern_n(s, len);
            } else if ((len > 3 && (strncmp(s, "WF_", 3) == 0 || strncmp(s, "SF_", 3) == 0))) {
                len = 3;
                t->kind = T_KW;
                t->id = intern_n(s, 3);
            } else if (is_keyword(s, len)) {
                t->kind = T_KW;
                t->id = intern_n(s, len);
            } else if (len == 1 && s[0] == '_') {
                t->kind = T_OP;
                t->id = intern("_");
            } else {
                t->kind = T_IDENT;
                t->id = intern_n(s, len);
            }
        } else if (s[0] == '"') {
            Buf b = {0};
            len = 1;
            while (s[len] != '"') {
                if (!s[len] || s[len] == '\n') parse_error(file, t->line, t->col, "Unterminated string");
                if (s[len] == '\\') {
                    char e = s[len + 1];
                    if (!e) parse_error(file, t->line, t->col, "Unterminated string");
                    char c = e == 'n' ? '\n' : e == 't' ? '\t' : e == 'r' ? '\r' : e == 'f' ? '\f' : e;
                    buf_add(&b, &c, 1);
                    len += 2;
                } else {
                    buf_add(&b, s + len, 1);
                    len++;
                }
            }
            len++;
            t->kind = T_STR;
            t->len = (int)b.n;
            t->text = b.s ? b.s : "";
        } else if (s[0] == '\\' && isalnum((unsigned char)s[1])) {
            len = 1;
            while (isalnum((unsigned char)s[len])) len++;
            int base = strchr("bB", s[1]) ? 2 : strchr("oO", s[1]) ? 8 : strchr("hH", s[1]) ? 16 : 0;
            int ok = base && len > 2;
            for (int i = 2; ok && i < len; i++) if (digit_value(s[i]) >= base) ok = 0;
            if (ok) {
                t->kind = T_NUM;
                int64_t v = 0;
                for (int i = 2; i < len; i++) { v = v * base + digit_value(s[i]); if (v > 0x7fffffffffffLL) v = 0x7fffffffffffLL; }
                t->num = v;
                t->id = intern_n(s, len);
            } else {
                t->kind = T_OP;
                t->id = intern_n(s, len);
            }
        } else if ((len = proof_step(s))) {
            t->kind = T_STEP;
            t->id = intern_n(s, len);
        } else {
            for (int i = 0; symbols[i]; i++) {
                int l = (int)strlen(symbols[i]);
                if (strncmp(s, symbols[i], (size_t)l) == 0) { len = l; break; }
            }
            if (!len) parse_error(file, t->line, t->col, "Unexpected character '%c'", s[0]);
            /* >>_ and ]_ begin a subscript: <<A>>_v and [A]_v. */
            if ((len == 2 && s[0] == '>' && s[1] == '>' && s[2] == '_') || (len == 1 && s[0] == ']' && s[1] == '_')) len++;
            t->kind = T_OP;
            t->id = intern_n(s, len);
        }
        lex_advance(&L, len - 1);
        t->eline = L.line; t->ecol = L.col;
        lex_advance(&L, 1);
        n++;
        if (t->kind == T_END && depth == 0) {
            toks[n].kind = T_EOF; toks[n].line = L.line; toks[n].col = L.col; n++;
            break;
        }
    }
    *count = n;
    return toks;
}

/* ---------------------------------------------------------------- parser */

typedef struct {
    Tok *t;
    int pos, n;
    int limit;        /* tokens at or left of this column end the junction item (§6.2) */
    Module *mod;
    const char *file;
} Parser;

static Parser *P;

/* How deep expressions nest and definitions call (-stack): past it, TLC's
   Java stack has overflowed. 0 leaves parsing to the C stack and calls
   to 5000. */
static int stack_limit;

static const char stack_overflow[] =
    "This was a Java StackOverflowError. It was probably the result\n"
    "of an incorrect recursive function definition that caused TLC to enter\n"
    "an infinite loop when trying to compute the function or its application\n"
    "to an element in its putative domain.";

static const char *breakpoint;   /* the -inv expression being read, whose errors TLC reports as its own */

/* TLC's error in an -inv expression: a syntax error, or one SANY finds
   after (Unknown location), its own if why is NULL. */
static _Noreturn void breakpoint_error(int syntax, const char *why) {
    printf("Error: Parsing or semantic analysis failed.Parsing or semantic analysis failed.%s", syntax ? "" : "Unknown location\n\n");
    if (why) printf("%s\n", why);
    else printf("%s error while parsing breakpoint expression \"%s\"\n", syntax ? "Syntax" : "Semantic", breakpoint);
    exit(MANYAN_ERROR_PARSE);
}

static _Noreturn void parse_error(const char *file, int line, int col, const char *fmt, ...) {
    if (breakpoint) breakpoint_error(1, NULL);
    char msg[1024];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);
    printf("***Parse Error***\n%s at line %d, column %d in %s\n\n", msg, line, col, file);
    printf("Error: Parsing or semantic analysis failed.\n");
    exit(MANYAN_ERROR_PARSE);
}

static Tok eof_tok;

static Tok *peek(void) {
    Tok *t = &P->t[P->pos];
    if (t->kind != T_EOF && t->col <= P->limit) { eof_tok = *t; eof_tok.kind = T_EOF; return &eof_tok; }
    return t;
}

static Tok *peek_at(int k) {
    if (P->pos + k >= P->n) return &P->t[P->n - 1];
    return &P->t[P->pos + k];
}

static Tok *prev_tok(void) { return &P->t[P->pos - 1]; }

static Tok *next(void) { Tok *t = &P->t[P->pos]; if (t->kind != T_EOF) P->pos++; return t; }

static _Noreturn void syntax_error(const char *what) {
    Tok *t = &P->t[P->pos];
    const char *text = t->kind == T_EOF ? "end of module" : t->kind == T_STR ? "string" : S(t->id);
    parse_error(P->file, t->line, t->col, "Encountered \"%s\": %s", text, what);
}

static int is_op(Tok *t, const char *s) { return t->kind == T_OP && strcmp(S(t->id), s) == 0; }
static int is_kw(Tok *t, const char *s) { return t->kind == T_KW && strcmp(S(t->id), s) == 0; }

static void expect_op(const char *s) { if (!is_op(peek(), s)) syntax_error(s); next(); }
static void expect_kw(const char *s) { if (!is_kw(peek(), s)) syntax_error(s); next(); }

static int expect_ident(void) {
    Tok *t = peek();
    if (t->kind != T_IDENT) syntax_error("expected an identifier");
    next();
    return t->id;
}

/* A record field: any word, keywords included. */
static int is_field(Tok *t) { return t->kind == T_IDENT || (t->kind == T_KW && isalpha((unsigned char)S(t->id)[0])); }

static int expect_field(void) {
    Tok *t = peek();
    if (!is_field(t)) syntax_error("expected a field name");
    next();
    return t->id;
}

static Expr *mk_expr(int kind, Tok *start) {
    Expr *e = NEW(Expr);
    e->kind = (short)kind;
    e->mod = P->mod;
    e->l1 = start->line; e->c1 = start->col;
    e->l2 = start->eline; e->c2 = start->ecol;
    return e;
}

static void finish(Expr *e) {
    Tok *t = prev_tok();
    e->l2 = t->eline; e->c2 = t->ecol;
}

/* e starts where a does, or at the parenthesis before it. */
static void span_from(Expr *e, Expr *a) {
    if (a->pl1) { e->l1 = a->pl1; e->c1 = a->pc1; } else { e->l1 = a->l1; e->c1 = a->c1; }
}

static void span_to(Expr *e, Expr *a) {
    if (a->pl1) { e->l2 = a->pl2; e->c2 = a->pc2; } else { e->l2 = a->l2; e->c2 = a->c2; }
}

static Expr **args_array(Expr **a, int n) {
    Expr **r = NEWN(Expr *, n);
    for (int i = 0; i < n; i++) r[i] = a[i];
    return r;
}

/* Operators (§6.1). */
typedef struct { const char *name; int lo, hi, left, fix; } OpInfo;
enum { INFIX, PREFIX, POSTFIX };

static const OpInfo op_table[] = {
    {"=>", 1, 1, 0, INFIX}, {"~>", 2, 2, 0, INFIX}, {"<=>", 2, 2, 0, INFIX}, {"-+->", 2, 2, 0, INFIX},
    {"/\\", 3, 3, 1, INFIX}, {"\\/", 3, 3, 1, INFIX},
    {"=", 5, 5, 0, INFIX}, {"/=", 5, 5, 0, INFIX}, {"<", 5, 5, 0, INFIX}, {">", 5, 5, 0, INFIX},
    {"\\leq", 5, 5, 0, INFIX}, {"\\geq", 5, 5, 0, INFIX}, {"\\in", 5, 5, 0, INFIX},
    {"\\notin", 5, 5, 0, INFIX}, {"\\subseteq", 5, 5, 0, INFIX}, {"\\subset", 5, 5, 0, INFIX},
    {"\\supseteq", 5, 5, 0, INFIX}, {"\\supset", 5, 5, 0, INFIX}, {"\\prec", 5, 5, 0, INFIX},
    {"\\succ", 5, 5, 0, INFIX}, {"\\preceq", 5, 5, 0, INFIX}, {"\\succeq", 5, 5, 0, INFIX},
    {"\\sim", 5, 5, 0, INFIX}, {"\\simeq", 5, 5, 0, INFIX}, {"\\ll", 5, 5, 0, INFIX},
    {"\\gg", 5, 5, 0, INFIX}, {"\\asymp", 5, 5, 0, INFIX}, {"\\approx", 5, 5, 0, INFIX},
    {"\\cong", 5, 5, 0, INFIX}, {"\\sqsubset", 5, 5, 0, INFIX}, {"\\sqsubseteq", 5, 5, 0, INFIX},
    {"\\sqsupset", 5, 5, 0, INFIX}, {"\\sqsupseteq", 5, 5, 0, INFIX}, {"\\doteq", 5, 5, 0, INFIX},
    {"\\propto", 5, 5, 0, INFIX}, {":=", 5, 5, 0, INFIX}, {"::=", 5, 5, 0, INFIX},
    {"|-", 5, 5, 0, INFIX}, {"-|", 5, 5, 0, INFIX}, {"|=", 5, 5, 0, INFIX}, {"=|", 5, 5, 0, INFIX},
    {"\\cdot", 5, 14, 1, INFIX}, {"@@", 6, 6, 1, INFIX}, {":>", 7, 7, 0, INFIX}, {"<:", 7, 7, 0, INFIX},
    {"\\", 8, 8, 0, INFIX}, {"\\cap", 8, 8, 1, INFIX}, {"\\cup", 8, 8, 1, INFIX},
    {"..", 9, 9, 0, INFIX}, {"...", 9, 9, 0, INFIX}, {"!!", 9, 13, 0, INFIX}, {"##", 9, 13, 1, INFIX},
    {"$", 9, 13, 1, INFIX}, {"$$", 9, 13, 1, INFIX}, {"??", 9, 13, 1, INFIX}, {"\\uplus", 9, 13, 1, INFIX},
    {"\\sqcap", 9, 13, 1, INFIX}, {"\\sqcup", 9, 13, 1, INFIX}, {"\\wr", 9, 14, 0, INFIX},
    {"\\X", 10, 13, 1, INFIX}, {"+", 10, 10, 1, INFIX}, {"++", 10, 10, 1, INFIX},
    {"\\oplus", 10, 10, 1, INFIX}, {"%", 10, 11, 0, INFIX}, {"%%", 10, 11, 1, INFIX},
    {"|", 10, 11, 1, INFIX}, {"||", 10, 11, 1, INFIX}, {"-", 11, 11, 1, INFIX}, {"--", 11, 11, 1, INFIX},
    {"\\ominus", 11, 11, 1, INFIX}, {"*", 13, 13, 1, INFIX}, {"**", 13, 13, 1, INFIX},
    {"&", 13, 13, 1, INFIX}, {"&&", 13, 13, 1, INFIX}, {"\\o", 13, 13, 1, INFIX},
    {"\\odot", 13, 13, 1, INFIX}, {"\\otimes", 13, 13, 1, INFIX}, {"\\star", 13, 13, 1, INFIX},
    {"\\bigcirc", 13, 13, 1, INFIX}, {"\\bullet", 13, 13, 1, INFIX}, {"/", 13, 13, 0, INFIX},
    {"//", 13, 13, 0, INFIX}, {"\\div", 13, 13, 0, INFIX}, {"\\oslash", 13, 13, 0, INFIX},
    {"^", 14, 14, 0, INFIX}, {"^^", 14, 14, 0, INFIX},
    {"~", 4, 4, 0, PREFIX}, {"[]", 4, 15, 0, PREFIX}, {"<>", 4, 15, 0, PREFIX},
    {"ENABLED", 4, 15, 0, PREFIX}, {"UNCHANGED", 4, 15, 0, PREFIX}, {"SUBSET", 8, 8, 0, PREFIX},
    {"UNION", 8, 8, 0, PREFIX}, {"DOMAIN", 9, 9, 0, PREFIX}, {"-.", 12, 12, 0, PREFIX},
    {"'", 15, 15, 0, POSTFIX}, {"^+", 15, 15, 0, POSTFIX}, {"^*", 15, 15, 0, POSTFIX}, {"^#", 15, 15, 0, POSTFIX},
    {NULL, 0, 0, 0, 0}};

/* The canonical name of an operator symbol: synonyms map to one name. */
static int canonical(int id) {
    static const char *syn[][2] = {
        {"\\land", "/\\"}, {"\\lor", "\\/"}, {"\\lnot", "~"}, {"\\neg", "~"}, {"\\equiv", "<=>"},
        {"#", "/="}, {"\\intersect", "\\cap"}, {"\\union", "\\cup"}, {"\\times", "\\X"},
        {"<=", "\\leq"}, {"=<", "\\leq"}, {">=", "\\geq"}, {"\\circ", "\\o"},
        {"(+)", "\\oplus"}, {"(-)", "\\ominus"}, {"(.)", "\\odot"}, {"(/)", "\\oslash"},
        {"(\\X)", "\\otimes"}, {NULL, NULL}};
    for (int i = 0; syn[i][0]; i++) if (strcmp(S(id), syn[i][0]) == 0) return intern(syn[i][1]);
    return id;
}

static const OpInfo *op_info(Tok *t, int fix) {
    if (t->kind != T_OP && t->kind != T_KW) return NULL;
    const char *name = S(canonical(t->id));
    if (fix == PREFIX && strcmp(name, "-") == 0) name = "-.";
    for (int i = 0; op_table[i].name; i++)
        if (op_table[i].fix == fix && strcmp(op_table[i].name, name) == 0) return &op_table[i];
    return NULL;
}

static Expr *parse_expr(void);
static Expr *parse_binary(int bound);
static Def *parse_definition(int local);
static void parse_bounds(Expr *e, int allow_unbounded);

static Expr *mk_op(Tok *start, int op, int n, Expr **args) {
    Expr *e = mk_expr(X_OP, start);
    e->op = op;
    e->n = n;
    e->args = args_array(args, n);
    return e;
}

static int is_junction(Tok *t) { return is_op(t, "/\\") || is_op(t, "\\/") || is_op(t, "\\land") || is_op(t, "\\lor"); }

/* LAMBDA x, y : e, where an operator argument may be. */
static Expr *parse_lambda(void) {
    Expr *l = mk_expr(X_LAMBDA, next());
    Def *params[16];
    int np = 0;
    do {
        if (np == 16) syntax_error("too many parameters");
        Def *d = NEW(Def);
        d->kind = D_PARAM;
        d->name = expect_ident();
        params[np++] = d;
    } while (is_op(peek(), ",") && next());
    expect_op(":");
    Def *op = NEW(Def);
    op->kind = D_OP;
    op->name = intern("LAMBDA");
    op->nparams = np;
    op->params = NEWN(Def *, np);
    memcpy(op->params, params, sizeof(Def *) * (size_t)np);
    op->body = parse_expr();
    op->mod = P->mod;
    op->level = -1;
    op->var_index = -1;
    l->def = op;
    finish(l);
    return l;
}

/* Arguments of an operator application: expressions, LAMBDAs, or
   operator symbols passed as operators. */
static Expr **parse_args(int *count) {
    Expr **args = NULL;
    int n = 0;
    int saved = P->limit;
    P->limit = 0;
    expect_op("(");
    for (;;) {
        Tok *t = peek();
        if (is_kw(t, "LAMBDA")) {
            PUSH(args, n, parse_lambda());
        } else if ((t->kind == T_OP || t->kind == T_KW) && (op_info(t, INFIX) || op_info(t, PREFIX) || op_info(t, POSTFIX)) &&
                   (is_op(peek_at(1), ",") || is_op(peek_at(1), ")"))) {
            Expr *r = mk_expr(X_OPREF, t);
            r->op = canonical(t->id);
            next();
            PUSH(args, n, r);
        } else {
            PUSH(args, n, parse_expr());
        }
        if (is_op(peek(), ",")) { next(); continue; }
        expect_op(")");
        break;
    }
    P->limit = saved;
    *count = n;
    return args;
}

/* A name, its arguments, and instance selections: A!B(x)!C. */
static Expr *parse_name(void) {
    Tok *start = peek();
    Expr *e = mk_expr(X_NAME, start);
    Seg segs[32];
    int n = 0;
    for (;;) {
        Tok *t = peek();
        Seg *s = &segs[n++];
        memset(s, 0, sizeof *s);
        static const char *sels[] = {"<<", ">>", ":", "@", "("};
        for (int k = 0; k < 5 && n > 1; k++) if (is_op(t, sels[k])) s->sel = -1 - k;
        if (n > 1 && t->kind == T_NUM && t->num > 0) s->sel = (int)t->num;
        if (s->sel == SEL_NULL) {
            s->args = parse_args(&s->n);
        } else if (s->sel) {
            next();
        } else {
            if (t->kind == T_IDENT) s->name = t->id;
            else if (t->kind == T_OP || t->kind == T_KW) s->name = canonical(t->id);
            else syntax_error("expected a name");
            next();
            if (is_op(peek(), "(")) s->args = parse_args(&s->n);
        }
        if (is_op(peek(), "!") && n < 32) { next(); continue; }
        break;
    }
    e->segs = NEWN(Seg, n);
    memcpy(e->segs, segs, sizeof(Seg) * (size_t)n);
    e->nseg = n;
    while (segs[n - 1].sel) n--;
    e->op = segs[n - 1].name;
    finish(e);
    return e;
}

/* `x, y \in S, <<a, b>> \in T` or, unbounded, `x, y`. */
static void parse_bounds(Expr *e, int allow_unbounded) {
    for (;;) {
        Bound b = {.tuple = is_op(peek(), "<<")};
        if (b.tuple) next();
        b.line = peek()->line;
        b.col = peek()->col;
        if (b.tuple) {
            do PUSH(b.names, b.n, expect_ident()); while (is_op(peek(), ",") && next());
            expect_op(">>");
        } else {
            PUSH(b.names, b.n, expect_ident());
            while (is_op(peek(), ",") && peek_at(1)->kind == T_IDENT) {
                next();
                PUSH(b.names, b.n, expect_ident());
            }
        }
        if (is_op(peek(), "\\in")) {
            next();
            b.set = parse_expr();
        } else if (!allow_unbounded) {
            syntax_error("expected \\in");
        }
        PUSH(e->bounds, e->nb, b);
        if (!is_op(peek(), ",")) break;
        next();
    }
}

/* Whether the tokens ahead are `x \in` or `x, y \in` or `<<x, y>> \in`. */
static int binder_ahead(void) {
    int k = 0;
    if (is_op(peek_at(0), "<<")) {
        k = 1;
        while (peek_at(k)->kind == T_IDENT && is_op(peek_at(k + 1), ",")) k += 2;
        if (peek_at(k)->kind != T_IDENT || !is_op(peek_at(k + 1), ">>")) return 0;
        return is_op(peek_at(k + 2), "\\in");
    }
    while (peek_at(k)->kind == T_IDENT && is_op(peek_at(k + 1), ",")) k += 2;
    return peek_at(k)->kind == T_IDENT && is_op(peek_at(k + 1), "\\in");
}

static _Noreturn void semantic_error(Expr *where, const char *fmt, ...);

static Expr *parse_junction(Tok *bullet) {
    int col = bullet->col;
    int op = canonical(bullet->id);
    int saved = P->limit;
    Expr *list = mk_expr(X_OP, bullet);
    for (;;) {
        Tok *t = &P->t[P->pos];
        if (t->kind != T_OP || canonical(t->id) != op || t->col != col) break;
        next();
        P->limit = col;
        PUSH(list->args, list->n, parse_expr());
        P->limit = saved;
    }
    list->op = op;
    finish(list);
    return list;
}

/* The v of WF_v(A), [A]_v and <<A>>_v: a name, I!v, or a tuple, set,
   bracketed or parenthesized expression, as SANY's ReducedExpression. */
static Expr *parse_subscript(void) {
    Tok *t = peek();
    if (t->kind == T_IDENT) {
        Expr *e = mk_expr(X_NAME, t);
        Seg segs[32];
        int n = 0;
        do segs[n++] = (Seg){.name = expect_ident()};
        while (n < 32 && is_op(peek(), "!") && peek_at(1)->kind == T_IDENT && next());
        e->segs = NEWN(Seg, n);
        memcpy(e->segs, segs, sizeof(Seg) * (size_t)n);
        e->nseg = n;
        e->op = segs[n - 1].name;
        finish(e);
        return e;
    }
    if (is_op(t, "<<") || is_op(t, "(") || is_op(t, "{") || is_op(t, "[")) return parse_binary(16);
    syntax_error("expected a subscript");
}

static int unit_section;   /* the part of the module being parsed, as Module.odd counts them */

static Expr *parse_primary(void) {
    Tok *t = peek();
    Expr *e;
    switch (t->kind) {
    case T_NUM:
        next();
        e = mk_expr(X_NUM, t);
        e->num = t->num;
        e->op = t->id;
        if ((e->num < 0 || e->num > 2147483647) && !P->mod->odd[unit_section]) P->mod->odd[unit_section] = e;
        return e;
    case T_STR:
        next();
        e = mk_expr(X_STR, t);
        e->text = t->text;
        e->len = t->len;
        return e;
    case T_IDENT:
        return parse_name();
    case T_KW:
        if (is_kw(t, "TRUE") || is_kw(t, "FALSE")) {
            next();
            e = mk_expr(X_BOOL, t);
            e->num = is_kw(t, "TRUE");
            return e;
        }
        if (is_kw(t, "BOOLEAN") || is_kw(t, "STRING")) {
            next();
            e = mk_expr(X_OP, t);
            e->op = t->id;
            return e;
        }
        if (is_kw(t, "IF")) {
            next();
            e = mk_expr(X_IF, t);
            Expr *a[3];
            a[0] = parse_expr();
            expect_kw("THEN");
            a[1] = parse_expr();
            expect_kw("ELSE");
            a[2] = parse_expr();
            e->n = 3;
            e->args = args_array(a, 3);
            finish(e);
            return e;
        }
        if (is_kw(t, "CASE")) {
            next();
            e = mk_expr(X_CASE, t);
            e->num = 0;
            for (;;) {
                if (is_kw(peek(), "OTHER")) {
                    next();
                    expect_op("->");
                    PUSH(e->args, e->n, NULL);
                    PUSH(e->args, e->n, parse_expr());
                    e->num = 1;
                    break;
                }
                PUSH(e->args, e->n, parse_expr());
                expect_op("->");
                PUSH(e->args, e->n, parse_expr());
                if (!is_op(peek(), "[]")) break;
                next();
            }
            finish(e);
            return e;
        }
        if (is_kw(t, "LET")) {
            next();
            e = mk_expr(X_LET, t);
            int *recursive = NULL, nrec = 0;
            while (!is_kw(peek(), "IN")) {
                if (is_kw(peek(), "RECURSIVE")) {
                    next();
                    do {
                        int name = expect_ident();
                        PUSH(recursive, nrec, name);
                        if (is_op(peek(), "(")) {
                            next();
                            while (!is_op(peek(), ")")) next();
                            next();
                        }
                    } while (is_op(peek(), ",") && next());
                    continue;
                }
                PUSH(e->defs, e->ndefs, parse_definition(0));
            }
            next();
            for (int i = 0; i < e->ndefs; i++)
                for (int k = 0; k < nrec; k++) e->defs[i]->recursive |= e->defs[i]->name == recursive[k];
            e->n = 1;
            e->args = NEWN(Expr *, 1);
            e->args[0] = parse_expr();
            finish(e);
            return e;
        }
        if (is_kw(t, "CHOOSE")) {
            next();
            e = mk_expr(X_CHOOSE, t);
            parse_bounds(e, 1);
            expect_op(":");
            e->n = 1;
            e->args = NEWN(Expr *, 1);
            e->args[0] = parse_expr();
            finish(e);
            return e;
        }
        if (is_kw(t, "WF_") || is_kw(t, "SF_")) {
            next();
            e = mk_expr(is_kw(t, "WF_") ? X_WF : X_SF, t);
            Expr *a[2];
            a[0] = parse_subscript();
            expect_op("(");
            int saved = P->limit;
            P->limit = 0;
            a[1] = parse_expr();
            P->limit = saved;
            expect_op(")");
            e->n = 2;
            e->args = args_array(a, 2);
            finish(e);
            return e;
        }
        break;
    case T_OP:
        if (is_op(t, "\\A") || is_op(t, "\\E") || is_op(t, "\\AA") || is_op(t, "\\EE") ||
            is_op(t, "\\forall") || is_op(t, "\\exists")) {
            next();
            int all = is_op(t, "\\A") || is_op(t, "\\forall") || is_op(t, "\\AA");
            int temporal = is_op(t, "\\AA") || is_op(t, "\\EE");
            e = mk_expr(temporal ? (all ? X_TFORALL : X_TEXISTS) : all ? X_FORALL : X_EXISTS, t);
            parse_bounds(e, 1);
            expect_op(":");
            e->n = 1;
            e->args = NEWN(Expr *, 1);
            e->args[0] = parse_expr();
            finish(e);
            return e;
        }
        if (is_op(t, "(")) {
            next();
            int saved = P->limit;
            P->limit = 0;
            e = parse_expr();
            P->limit = saved;
            expect_op(")");
            /* A parenthesized expression keeps its location; what encloses it spans the parentheses. */
            Tok *close = prev_tok();
            e->pl1 = t->line; e->pc1 = t->col; e->pl2 = close->eline; e->pc2 = close->ecol;
            return e;
        }
        if (is_op(t, "@")) {
            next();
            return mk_expr(X_AT, t);
        }
        if (is_op(t, "<<")) {
            next();
            int saved = P->limit;
            P->limit = 0;
            Expr **a = NULL;
            int n = 0;
            if (!is_op(peek(), ">>") && !is_op(peek(), ">>_"))
                do PUSH(a, n, parse_expr()); while (is_op(peek(), ",") && next());
            P->limit = saved;
            if (is_op(peek(), ">>_")) {
                next();
                e = mk_expr(X_ANGLEACT, t);
                Expr *b[2] = {n == 1 ? a[0] : NULL, parse_subscript()};
                if (n != 1) syntax_error("<<A>>_v takes one action");
                e->n = 2;
                e->args = args_array(b, 2);
                finish(e);
                return e;
            }
            expect_op(">>");
            e = mk_expr(X_TUPLE, t);
            e->n = n;
            e->args = a;
            finish(e);
            return e;
        }
        if (is_op(t, "{")) {
            next();
            int saved = P->limit;
            P->limit = 0;
            Expr **a = NULL;
            int n = 0;
            if (is_op(peek(), "}")) {
                next();
                P->limit = saved;
                e = mk_expr(X_SETENUM, t);
                finish(e);
                return e;
            }
            if (binder_ahead()) {
                e = mk_expr(X_FILTER, t);
                int start = P->pos;
                Bound b;
                memset(&b, 0, sizeof b);
                Expr tmp;
                memset(&tmp, 0, sizeof tmp);
                parse_bounds(&tmp, 0);
                if (tmp.nb == 1 && is_op(peek(), ":") && (tmp.bounds[0].n == 1 || tmp.bounds[0].tuple)) {
                    next();
                    e->bounds = tmp.bounds;
                    e->nb = 1;
                    e->n = 1;
                    e->args = NEWN(Expr *, 1);
                    e->args[0] = parse_expr();
                    expect_op("}");
                    P->limit = saved;
                    finish(e);
                    return e;
                }
                P->pos = start;
            }
            Expr *first = parse_expr();
            if (is_op(peek(), ":")) {
                next();
                e = mk_expr(X_MAP, t);
                parse_bounds(e, 0);
                e->n = 1;
                e->args = NEWN(Expr *, 1);
                e->args[0] = first;
                expect_op("}");
                P->limit = saved;
                finish(e);
                return e;
            }
            PUSH(a, n, first);
            while (is_op(peek(), ",")) {
                next();
                PUSH(a, n, parse_expr());
            }
            expect_op("}");
            P->limit = saved;
            e = mk_expr(X_SETENUM, t);
            e->n = n;
            e->args = a;
            finish(e);
            return e;
        }
        if (is_op(t, "[")) {
            next();
            int saved = P->limit;
            P->limit = 0;
            if (peek()->kind == T_IDENT && (is_op(peek_at(1), "|->") || is_op(peek_at(1), ":"))) {
                int set = is_op(peek_at(1), ":");
                e = mk_expr(set ? X_RCDSET : X_RECORD, t);
                do {
                    Tok *field = peek();
                    int name = expect_ident();
                    for (int i = 0; i < e->nseg; i++)
                        if (e->segs[i].name == name) semantic_error(mk_expr(X_NAME, field), "Non-unique fields in constructor.");
                    PUSH(e->segs, e->nseg, ((Seg){.name = name, .line = field->line, .col = field->col}));
                    expect_op(set ? ":" : "|->");
                    PUSH(e->args, e->n, parse_expr());
                } while (is_op(peek(), ",") && next());
                expect_op("]");
                P->limit = saved;
                finish(e);
                return e;
            }
            if (binder_ahead()) {
                e = mk_expr(X_FCN, t);
                parse_bounds(e, 0);
                expect_op("|->");
                e->n = 1;
                e->args = NEWN(Expr *, 1);
                e->args[0] = parse_expr();
                expect_op("]");
                P->limit = saved;
                finish(e);
                return e;
            }
            Expr *first = parse_expr();
            if (is_op(peek(), "->")) {
                next();
                e = mk_expr(X_FCNSET, t);
                Expr *a[2] = {first, parse_expr()};
                expect_op("]");
                P->limit = saved;
                e->n = 2;
                e->args = args_array(a, 2);
                finish(e);
                return e;
            }
            if (is_kw(peek(), "EXCEPT")) {
                next();
                e = mk_expr(X_EXCEPT, t);
                PUSH(e->args, e->n, first);
                int n = 0;
                do {
                    Path path = {.line = peek()->line, .col = peek()->col};
                    expect_op("!");
                    Expr *keys[32];
                    int fields[32];
                    int k = 0;
                    while (k < 32) {
                        if (is_op(peek(), ".")) {
                            next();
                            fields[k] = expect_field();
                            keys[k++] = NULL;
                        } else if (is_op(peek(), "[")) {
                            Tok *open = peek();
                            next();
                            Expr *ks[32];
                            int nk = 0;
                            do ks[nk++] = parse_expr(); while (is_op(peek(), ",") && next() && nk < 32);
                            expect_op("]");
                            if (nk == 1) keys[k] = ks[0];
                            else {
                                Expr *tup = mk_expr(X_TUPLE, open);
                                tup->n = nk;
                                tup->args = args_array(ks, nk);
                                finish(tup);
                                keys[k] = tup;
                            }
                            fields[k++] = -1;
                        } else break;
                    }
                    if (!k) syntax_error("expected ! path");
                    expect_op("=");
                    path.n = k;
                    path.keys = args_array(keys, k);
                    path.fields = NEWN(int, k);
                    memcpy(path.fields, fields, sizeof(int) * (size_t)k);
                    PUSH(e->paths, n, path);
                    PUSH(e->args, e->n, parse_expr());
                } while (is_op(peek(), ",") && next());
                expect_op("]");
                P->limit = saved;
                finish(e);
                return e;
            }
            if (is_op(peek(), "]_")) {
                next();
                P->limit = saved;
                e = mk_expr(X_SQACT, t);
                Expr *a[2] = {first, parse_subscript()};
                e->n = 2;
                e->args = args_array(a, 2);
                finish(e);
                return e;
            }
            syntax_error("expected ]_, ->, or EXCEPT");
        }
        if (is_junction(t)) return parse_junction(t);
        break;
    default:
        break;
    }
    syntax_error("unexpected token");
}

/* A primary followed by applications f[a], fields r.f and postfix
   operators x', in any order: x'[1] is (x')[1]. */
static Expr *parse_postfix(void) {
    Expr *e = parse_primary();
    for (;;) {
        Tok *t = peek();
        const OpInfo *post = op_info(t, POSTFIX);
        if (post) {
            next();
            Expr *p = mk_op(t, intern(post->name), 1, &e);
            span_from(p, e);
            e = p;
        } else if (is_op(t, "[")) {
            Tok *start = t;
            next();
            int saved = P->limit;
            P->limit = 0;
            Expr *app = mk_expr(X_APPLY, start);
            PUSH(app->args, app->n, e);
            do PUSH(app->args, app->n, parse_expr()); while (is_op(peek(), ",") && next());
            expect_op("]");
            P->limit = saved;
            span_from(app, e);
            finish(app);
            e = app;
        } else if (is_op(t, ".") && is_field(peek_at(1))) {
            next();
            Expr *d = mk_expr(X_DOT, t);
            span_from(d, e);
            d->op = expect_field();
            d->n = 1;
            d->args = NEWN(Expr *, 1);
            d->args[0] = e;
            finish(d);
            e = d;
        } else {
            return e;
        }
    }
}

/* An operand; *prefix is its prefix operator, if it is an application of one. */
/* lab :: or lab(x, y) :: ahead. */
static int label_ahead(void) {
    if (peek()->kind != T_IDENT) return 0;
    int k = 1;
    if (is_op(peek_at(1), "(")) {
        do if (peek_at(++k)->kind != T_IDENT) return 0;
        while (is_op(peek_at(++k), ","));
        if (!is_op(peek_at(k++), ")")) return 0;
    }
    return is_op(peek_at(k), "::");
}

static Expr *parse_unary(const OpInfo **prefix) {
    Tok *t = peek();
    *prefix = NULL;
    if (label_ahead()) {
        Label *l = NEW(Label);
        l->name = next()->id;
        int names[32];
        if (is_op(peek(), "(")) {
            next();
            do names[l->n++] = expect_ident(); while (is_op(peek(), ",") && next() && l->n < 32);
            expect_op(")");
        }
        l->names = NEWN(int, l->n);
        memcpy(l->names, names, sizeof(int) * (size_t)l->n);
        expect_op("::");
        Expr *e = parse_expr();
        e->label = l;
        return e;
    }
    const OpInfo *info = op_info(t, PREFIX), *named = op_info(t, INFIX);
    if (!named) named = op_info(t, POSTFIX);
    if (!info && named && !is_junction(t) && is_op(peek_at(1), "(")) {
        /* An infix or postfix operator applied to its arguments: +(a, b), ^+(a). */
        next();
        Tok *open = peek();
        int n, want = op_info(t, INFIX) ? 2 : 1;
        Expr **args = parse_args(&n);
        if (n != want) {
            Expr *where = mk_op(open, 0, 0, NULL);
            finish(where);
            semantic_error(where, "The operator %s requires %d arguments.", named->name, want);
        }
        Expr *e = mk_op(t, intern(named->name), n, args);
        finish(e);
        return e;
    }
    if (info) {
        next();
        *prefix = info;
        Expr *arg = parse_binary(info->hi);
        Expr *e = mk_op(t, intern(info->name), 1, &arg);
        span_to(e, arg);
        return e;
    }
    return parse_postfix();
}

/* An expression whose operators all bind tighter than `bound` (§6.1). */
static Expr *parse_binary(int bound) {
    static int nesting;   /* every nesting of expressions passes here */
    if (++nesting > stack_limit && stack_limit) {
        printf("Error: %s\n", stack_overflow);
        exit(MANYAN_ERROR);
    }
    const OpInfo *last;   /* the operator before the next one, as on SANY's stack */
    Expr *left = parse_unary(&last);
    for (;;) {
        Tok *t = peek();
        const OpInfo *post = op_info(t, POSTFIX);
        if (post && post->lo > bound) {
            next();
            Expr *e = mk_op(t, intern(post->name), 1, &left);
            span_from(e, left);
            left = e;
            continue;
        }
        const OpInfo *info = op_info(t, INFIX);
        if (!info) break;
        /* Operators whose ranges overlap conflict, but for a left-associative one repeated. */
        if (last && !(info->hi < last->lo) && !(info == last && info->left))
            parse_error(P->file, t->line, t->col, "Precedence conflict between ops %s and %s", last->name, info->name);
        if (info->lo <= bound) break;
        next();
        if (strcmp(info->name, "\\X") == 0) {
            /* a \X b \X c is a product of three sets. */
            Expr *a[32];
            int n = 0;
            a[n++] = left;
            a[n++] = parse_binary(info->hi);
            while (is_op(peek(), "\\X") || is_op(peek(), "\\times")) {
                next();
                if (n == 32) syntax_error("product too long");
                a[n++] = parse_binary(info->hi);
            }
            Expr *e = mk_op(t, intern("\\X"), n, a);
            span_from(e, left);
            span_to(e, a[n - 1]);
            left = e;
            last = info;
            continue;
        }
        /* SANY rejects a prefix minus right of an operator binding tighter: 2 * -1. */
        if (info->lo > 12 && is_op(peek(), "-"))
            parse_error(P->file, t->line, t->col, "Precedence conflict between ops %s and -.", info->name);
        Expr *right = parse_binary(info->hi);
        Expr *pair[2] = {left, right};
        Expr *e = mk_op(t, intern(info->name), 2, pair);
        span_from(e, left);
        span_to(e, right);
        left = e;
        last = info;
    }
    nesting--;
    return left;
}

static Expr *parse_expr(void) { return parse_binary(0); }

static Def *new_def(int kind, int name, Tok *where) {
    Def *d = NEW(Def);
    d->kind = kind;
    d->name = name;
    d->mod = P->mod;
    d->var_index = -1;
    d->level = -1;
    if (where) {
        Expr *w = mk_expr(X_BOOL, where);
        d->where = w;
    }
    return d;
}

/* An operator parameter or constant: x, F(_, _), _ + _, -. _, or _ ^+. */
static Def *parse_param(int kind) {
    Tok *t = peek();
    if (is_op(t, "_")) {
        next();
        Tok *op = peek();
        if (op->kind != T_OP && op->kind != T_KW) syntax_error("expected an operator");
        next();
        Def *d = new_def(kind, canonical(op->id), op);
        if (is_op(peek(), "_")) { next(); d->arity = 2; }
        else d->arity = 1;
        return d;
    }
    if ((t->kind == T_OP || t->kind == T_KW) && is_op(peek_at(1), "_")) {
        next();
        next();
        int name = canonical(t->id);
        if (strcmp(S(name), "-") == 0) name = intern("-.");
        Def *d = new_def(kind, name, t);
        d->arity = 1;
        return d;
    }
    Def *d = new_def(kind, expect_ident(), t);
    if (is_op(peek(), "(")) {
        next();
        do { expect_op("_"); d->arity++; } while (is_op(peek(), ",") && next());
        expect_op(")");
    }
    return d;
}

static Def *parse_instance(Tok *start, int name);

/* Name == e, Name(p) == e, f[x \in S] == e, a + b == e, -. a == e, a ^+ == e. */
static Def *parse_definition(int local) {
    Tok *t = peek();
    const char *notes = t->notes;
    Def *d;
    Def *params[64];
    int np = 0;
    if (t->kind == T_IDENT && is_op(peek_at(1), "==")) {
        d = new_def(D_OP, t->id, t);
        next();
    } else if (t->kind == T_IDENT && is_op(peek_at(1), "(")) {
        d = new_def(D_OP, t->id, t);
        next();
        next();
        do {
            if (np == 64) syntax_error("too many parameters");
            params[np++] = parse_param(D_PARAM);
        } while (is_op(peek(), ",") && next());
        expect_op(")");
    } else if (t->kind == T_IDENT && is_op(peek_at(1), "[")) {
        d = new_def(D_FCN, t->id, t);
        next();
        next();
        Expr tmp;
        memset(&tmp, 0, sizeof tmp);
        parse_bounds(&tmp, 0);
        d->bounds = tmp.bounds;
        d->nb = tmp.nb;
        expect_op("]");
    } else if (t->kind == T_IDENT && op_info(peek_at(1), INFIX) &&
               peek_at(2)->kind == T_IDENT && is_op(peek_at(3), "==")) {
        Tok *op = peek_at(1);
        d = new_def(D_OP, canonical(op->id), op);
        params[np++] = new_def(D_PARAM, t->id, t);
        next();
        next();
        params[np++] = new_def(D_PARAM, peek()->id, peek());
        next();
    } else if (op_info(t, PREFIX) && peek_at(1)->kind == T_IDENT && is_op(peek_at(2), "==")) {
        int name = canonical(t->id);
        if (strcmp(S(name), "-") == 0) name = intern("-.");
        d = new_def(D_OP, name, t);
        next();
        params[np++] = new_def(D_PARAM, peek()->id, peek());
        next();
    } else if (t->kind == T_IDENT && op_info(peek_at(1), POSTFIX) && is_op(peek_at(2), "==")) {
        Tok *op = peek_at(1);
        d = new_def(D_OP, canonical(op->id), op);
        params[np++] = new_def(D_PARAM, t->id, t);
        next();
        next();
    } else {
        syntax_error("expected a definition");
    }
    expect_op("==");
    d->local = local;
    d->notes = notes;
    d->nparams = np;
    d->params = NEWN(Def *, np);
    memcpy(d->params, params, sizeof(Def *) * (size_t)np);
    if (is_kw(peek(), "INSTANCE")) {
        Tok *start = peek();
        next();
        Def *inst = parse_instance(start, d->name);
        inst->where->l1 = d->where->l1;   /* the statement, from the name */
        inst->where->c1 = d->where->c1;
        inst->nparams = np;
        inst->params = d->params;
        inst->local = local;
        return inst;
    }
    d->body = parse_expr();
    if (d->kind == D_FCN) finish(d->where);   /* TLC's function constructor: the definition */
    return d;
}

/* INSTANCE M WITH a <- e, ...: the substitutions are completed by the
   resolver once M is read. */
static Def *parse_instance(Tok *start, int name) {
    Def *d = new_def(D_INST, name, start);
    d->target = (Module *)(intptr_t)expect_ident();   /* the module's name until resolved */
    int n = 0;
    if (is_kw(peek(), "WITH")) {
        next();
        do {
            Tok *t = peek();
            int pname;
            if (t->kind == T_IDENT) pname = t->id;
            else if (t->kind == T_OP || t->kind == T_KW) pname = canonical(t->id);
            else syntax_error("expected a parameter");
            next();
            expect_op("<-");
            Def *p = NEW(Def);
            p->name = pname;
            PUSH(d->subst_decl, n, p);
            Tok *at = peek();
            if ((at->kind == T_OP || at->kind == T_KW) && (is_op(peek_at(1), ",") || peek_at(1)->line != at->line ||
                                                             peek_at(1)->kind == T_SEP || peek_at(1)->kind == T_END)) {
                Expr *r = mk_expr(X_OPREF, at);
                r->op = canonical(at->id);
                next();
                PUSH(d->subst_expr, d->nsubst, r);
            } else {
                PUSH(d->subst_expr, d->nsubst, is_kw(at, "LAMBDA") ? parse_lambda() : parse_expr());
            }
        } while (is_op(peek(), ",") && next());
    }
    finish(d->where);
    return d;
}

static void add_unit(Module *m, int kind, Def *d, Expr *e, Module *nested, int local) {
    if (m->nunits == m->capunits) {
        m->capunits = m->capunits ? m->capunits * 2 : 64;
        m->units = xrealloc(m->units, sizeof(Unit) * (size_t)m->capunits);
    }
    Unit *u = &m->units[m->nunits++];
    u->kind = kind; u->def = d; u->expr = e; u->module = nested; u->local = local;
}

/* A name SANY records where it appears: a RECURSIVE operator's, a theorem's or an assumption's. */
static void add_name(Module *m, Def *d) { add_unit(m, 4, d, NULL, NULL, 0); }

static Def *thm_name(int name) {
    Def *d = NEW(Def);
    d->kind = D_THM;
    d->name = name;
    return d;
}

static int at_unit_start(void) {
    Tok *t = &P->t[P->pos];
    return t->kind == T_EOF || t->kind == T_END || t->kind == T_SEP || t->col == 1;
}

/* The facts of a HIDE: names of theorems, assumptions, or steps, which
   are the only expressions it may hide. */
static void hide_facts(void) {
    while (!at_unit_start() && !is_kw(peek(), "DEF") && !is_kw(peek(), "DEFS")) {
        Tok *t = next();
        if (is_kw(t, "MODULE")) next();
        else if (t->kind != T_IDENT && t->kind != T_STEP)
            semantic_error(mk_expr(X_NAME, t), "The only expression allowed as a fact in a HIDE is \nthe name of a theorem, assumption, or step.");
        while (is_op(peek(), "!") && !at_unit_start()) { next(); next(); }
        if (!is_op(peek(), ",")) return;
        next();
    }
}

/* A proof, or the rest of USE, HIDE, or BY: up to the next unit. */
static void skip_proof(void) {
    while (!at_unit_start())
        if (is_kw(next(), "HIDE")) hide_facts();
}

/* A module: ---- MODULE Name ---- units ====. */
static Module *parse_module(Module *outer) {
    Module *m = NEW(Module);
    m->outer = outer;
    Module *saved_mod = P->mod;
    P->mod = m;
    if (peek()->kind != T_SEP) syntax_error("expected ---- MODULE");
    next();
    expect_kw("MODULE");
    m->name = expect_ident();
    if (peek()->kind != T_SEP) syntax_error("expected ----");
    next();
    if (is_kw(peek(), "EXTENDS")) {
        next();
        do PUSH(m->extends, m->nextends, expect_ident()); while (is_op(peek(), ",") && next());
    }
    for (;;) {
        Tok *t = peek();
        unit_section = 0;
        if (t->kind == T_END) { next(); break; }
        if (t->kind == T_EOF) syntax_error("missing ==== at the end of the module");
        if (t->kind == T_SEP) {
            if (is_kw(peek_at(1), "MODULE")) {
                Module *inner = parse_module(m);
                add_unit(m, 3, NULL, NULL, inner, 0);
            } else {
                next();
            }
            continue;
        }
        int local = 0;
        Tok *first = t;   /* a statement begins at its LOCAL */
        if (is_kw(t, "LOCAL")) { local = 1; next(); t = peek(); }
        if (is_kw(t, "CONSTANT") || is_kw(t, "CONSTANTS") || is_kw(t, "VARIABLE") || is_kw(t, "VARIABLES")) {
            int var = is_kw(t, "VARIABLE") || is_kw(t, "VARIABLES");
            next();
            do {
                const char *notes = peek()->notes;
                Def *d = parse_param(var ? D_VAR : D_CONST);
                d->notes = notes;
                add_unit(m, 0, d, NULL, NULL, 0);
            } while (is_op(peek(), ",") && next());
            continue;
        }
        if (is_kw(t, "ASSUME") || is_kw(t, "ASSUMPTION") || is_kw(t, "AXIOM")) {
            unit_section = 1;
            next();
            Def *d = NULL;
            if (peek()->kind == T_IDENT && is_op(peek_at(1), "==")) { d = thm_name(next()->id); next(); }
            Expr *e = parse_expr();
            if (d) { d->body = e; add_name(m, d); }
            add_unit(m, 2, d, e, NULL, 0);
            Expr *where = m->units[m->nunits - 1].where = mk_expr(e->kind, t);
            where->l2 = e->l2, where->c2 = e->c2;
            continue;
        }
        if (is_kw(t, "THEOREM") || is_kw(t, "LEMMA") || is_kw(t, "PROPOSITION") || is_kw(t, "COROLLARY")) {
            unit_section = 2;
            next();
            Def *d = NULL;
            if (peek()->kind == T_IDENT && is_op(peek_at(1), "==")) { d = thm_name(next()->id); next(); add_name(m, d); }
            /* A theorem's statement is kept for its subexpressions; ASSUME ... PROVE is not. */
            if (!is_kw(peek(), "ASSUME")) {
                Expr *body = parse_expr();
                if (d) d->body = body;
            }
            skip_proof();
            continue;
        }
        if (is_kw(t, "USE") || is_kw(t, "HIDE") || is_kw(t, "PROOF") || is_kw(t, "BY") || is_kw(t, "OBVIOUS") ||
            is_kw(t, "OMITTED") || t->kind == T_STEP) {
            next();
            if (is_kw(t, "HIDE")) hide_facts();
            skip_proof();
            continue;
        }
        if (is_kw(t, "RECURSIVE")) {
            next();
            do add_name(m, parse_param(D_RECURSIVE)); while (is_op(peek(), ",") && next());
            continue;
        }
        if (is_kw(t, "INSTANCE")) {
            next();
            Def *d = parse_instance(first, 0);
            d->local = local;
            add_unit(m, 1, d, NULL, NULL, local);
            continue;
        }
        Def *d = parse_definition(local);
        if (local && !d->notes) d->notes = first->notes;
        add_unit(m, 0, d, NULL, NULL, local);
    }
    P->mod = saved_mod;
    return m;
}

/* ---------------------------------------------------------------- modules */

static int symbolic_mode;   /* -symbolic: the configuration is read as Apalache reads it */
static const char *sym_cinit_name;   /* -cinit: the operator that chooses the constants left */

/* The modules manyan_module gives. */
static struct { const char *name, *text; } *library;
static int nlibrary;

int manyan_module(const char *name, const char *text) {
    void *grown = realloc(library, sizeof *library * (size_t)(nlibrary + 1));
    if (!grown) return -1;
    library = grown;
    library[nlibrary].name = name, library[nlibrary++].text = text;
    return 0;
}

/* The standard modules of tla2tools, without their comments (§8). Their
   operators are evaluated natively; their identifiers are interned as
   TLC interns them. */
static const struct { const char *name, *text; } standard_modules[] = {
    {"Naturals",
     "---- MODULE Naturals ----\n"
     "\n\n\n\n\n\n\n\n\n\n\n\nNat       == { }\n"
     "a+b       == {a, b}\n"
     "\na-b       == CHOOSE n : b + n = a\n"
     "a*b       == TRUE\n"
     "a^b       == {a, b}\n"
     "a<b       ==  a = b\n"
     "a>b       ==  a = b\n"
     "a \\leq b  ==  a = b\n"
     "a \\geq b  ==  a = b\n"
     "\n\n\n\n\n\n\n\n\na % b     ==  {a, b}\n"
     "a \\div b  ==  {a, b}\n"
     "a .. b    ==  {a, b}\n"
     "====\n"},
    {"Integers",
     "---- MODULE Integers ----\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\nEXTENDS Naturals\n"
     "\nInt  ==  { }\n"
     "\n\n\n-. a == 0 - a\n"
     "====\n"},
    /* TLC's, which cannot compute with real numbers; its definitions on TLC's lines */
    {"Reals",
     "---- MODULE Reals ----\n\n\n\n\n\n\n\n\n\n\n\n"
     "EXTENDS Integers\n"
     "\n"
     "Real  == \"Reals\"\n"
     "a / b == CHOOSE m \\in Real : m * b = a\n"
     "Infinity == CHOOSE i : (i \\notin Real) /\\ (\\A r \\in Real : i > r)\n"
     "====\n"},
    {"RealTime",
     "---- MODULE RealTime ----\n"
     "\n\n\n\n\nEXTENDS Reals\n"
     "VARIABLE now\n"
     "\nRTBound(A, v, D, E) ==\n"
     "  LET TNext(t)  ==  t' = IF <<A>>_v \\/ ~(ENABLED <<A>>_v)'\n"
     "                           THEN 0\n"
     "                           ELSE t + (now'-now)\n"
     "\n      Timer(t) == (t=0)  /\\  [][TNext(t)]_<<t, v, now>>\n"
     "\n      MaxTime(t) == [](t \\leq E)\n"
     "\n      MinTime(t) == [][A => t \\geq D]_v\n"
     "  IN \\EE t : Timer(t) /\\ MaxTime(t) /\\ MinTime(t)\n"
     "\nRTnow(v) == LET NowNext == /\\ now' \\in {r \\in Real : r > now}\n"
     "                           /\\ UNCHANGED v\n"
     "            IN  /\\ now \\in Real\n"
     "                /\\ [][NowNext]_now\n"
     "                /\\ \\A r \\in Real : WF_now(NowNext /\\ (now'>r))\n"
     "====\n"},
    {"Sequences",
     "---- MODULE Sequences ----\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\nLOCAL INSTANCE Naturals\n"
     "\n\n\n\nSeq(S) == UNION {[1..n -> S] : n \\in Nat}\n"
     "\n\n\n\nLen(s) == CHOOSE n \\in Nat : DOMAIN s = 1..n\n"
     "\n\n\n\ns \\o t == [i \\in 1..(Len(s) + Len(t)) |-> IF i \\leq Len(s) THEN s[i]\n"
     "                                                           ELSE t[i-Len(s)]]\n"
     "\n\n\n\nAppend(s, e) == s \\o <<e>>\n"
     "\n\n\n\nHead(s) == s[1]\n"
     "Tail(s) == CASE s # << >> -> [i \\in 1..(Len(s)-1) |-> s[i+1]]\n"
     "\n\n\n\n\nSubSeq(s, m, n) == [i \\in 1..(1+n-m) |-> s[i+m-1]]\n"
     "\n\n\n\nSelectSeq(s, Test(_)) ==\n"
     "\n\n\n\n  LET F[i \\in 0..Len(s)] ==\n"
     "\n\n\n        IF i = 0 THEN << >>\n"
     "                 ELSE IF Test(s[i]) THEN Append(F[i-1], s[i])\n"
     "                                    ELSE F[i-1]\n"
     "  IN F[Len(s)]\n"
     "====\n"},
    {"FiniteSets",
     "---- MODULE FiniteSets ----\n"
     "\n\n\n\n\nLOCAL INSTANCE Naturals\n"
     "LOCAL INSTANCE Sequences\n"
     "\n\n\n\n\nIsFiniteSet(S) ==\n"
     "\n\n\n\n  \\E seq \\in Seq(S) : \\A s \\in S : \\E n \\in 1..Len(seq) : seq[n] = s\n"
     "\nCardinality(S) ==\n"
     "\n\n\n  LET CS[T \\in SUBSET S] == IF T = {} THEN 0\n"
     "                                      ELSE 1 + CS[T \\ {CHOOSE x : x \\in T}]\n"
     "  IN  CS[S]\n"
     "====\n"},
    {"TLC",
     "---- MODULE TLC ----\n"
     "\n\n\n\n\n\n\n\n\n\n\nLOCAL INSTANCE Naturals\n"
     "LOCAL INSTANCE Sequences\n"
     "LOCAL INSTANCE FiniteSets\n"
     "\nPrint(out, val) == val\n"
     "PrintT(out) == TRUE\n"
     "\n\n\n\n\nAssert(val, out) == IF val = TRUE THEN TRUE\n"
     "                                  ELSE CHOOSE v : TRUE\n"
     "JavaTime == CHOOSE n : n \\in Nat\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\nTLCGet(i) == CHOOSE n : TRUE\n"
     "TLCSet(i, v) == TRUE\n"
     "\nd :> e == [x \\in {d} |-> e]\n"
     "f @@ g == [x \\in (DOMAIN f) \\cup (DOMAIN g) |->\n"
     "            IF x \\in DOMAIN f THEN f[x] ELSE g[x]]\n"
     "Permutations(S) ==\n"
     "   {f \\in [S -> S] : \\A w \\in S : \\E v \\in S : f[v]=w}\n"
     "\n\n\n\n\nSortSeq(s, Op(_, _)) ==\n"
     "    LET Perm == CHOOSE p \\in Permutations(1 .. Len(s)) :\n"
     "                  \\A i, j \\in 1..Len(s) :\n"
     "                     (i < j) => Op(s[p[i]], s[p[j]]) \\/ (s[p[i]] = s[p[j]])\n"
     "    IN  [i \\in 1..Len(s) |-> s[Perm[i]]]\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\nRandomElement(s) == CHOOSE x \\in s : TRUE\n"
     "\n\n\n\n\n\n\n\nAny == CHOOSE x : TRUE\n"
     "\nToString(v) == (CHOOSE x \\in [a : v, b : STRING] : TRUE).b\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\nTLCEval(v) == v\n"
     "====\n"},
    {"Bags",
     "---- MODULE Bags ----\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\nLOCAL INSTANCE Naturals\n"
     "\nIsABag(B) ==\n"
     "\n\n\n  B \\in [DOMAIN B -> {n \\in Nat : n > 0}]\n"
     "\nBagToSet(B) == DOMAIN B\n"
     "\n\n\n\nSetToBag(S) == [e \\in S |-> 1]\n"
     "\n\n\n\nBagIn(e,B) == e \\in BagToSet(B)\n"
     "\n\n\n\nEmptyBag == SetToBag({})\n"
     "\nB1 (+) B2  ==\n"
     "\n\n\n  [e \\in (DOMAIN B1) \\cup (DOMAIN B2) |->\n"
     "      (IF e \\in DOMAIN B1 THEN B1[e] ELSE 0)\n"
     "    + (IF e \\in DOMAIN B2 THEN B2[e] ELSE 0) ]\n"
     "\nB1 (-) B2  ==\n"
     "\n\n\n\n\n\n  LET B == [e \\in DOMAIN B1 |-> IF e \\in DOMAIN B2 THEN B1[e] - B2[e]\n"
     "                                                   ELSE B1[e]]\n"
     "  IN  [e \\in {d \\in DOMAIN B : B[d] > 0} |-> B[e]]\n"
     "\nLOCAL Sum(f) ==\n"
     "\n\n\n\n\n        LET DSum[S \\in SUBSET DOMAIN f] ==\n"
     "               LET elt == CHOOSE e \\in S : TRUE\n"
     "               IN  IF S = {} THEN 0\n"
     "                             ELSE f[elt] + DSum[S \\ {elt}]\n"
     "        IN  DSum[DOMAIN f]\n"
     "\nBagUnion(S) ==\n"
     "\n\n\n  [e \\in UNION {BagToSet(B) : B \\in S} |->\n"
     "    Sum( [B \\in S |-> IF BagIn(e, B) THEN B[e] ELSE 0] ) ]\n"
     "\nB1 \\sqsubseteq B2  ==\n"
     "\n\n\n\n  /\\ (DOMAIN B1) \\subseteq (DOMAIN B2)\n"
     "  /\\ \\A e \\in DOMAIN B1 : B1[e] \\leq B2[e]\n"
     "\nSubBag(B) ==\n"
     "\n\n\n\n\n\n\n  LET RemoveFromDom(x, f) == [y \\in (DOMAIN f) \\ {x} |-> f[y]]\n"
     "      Combine(x, BagSet) ==\n"
     "         BagSet \\cup\n"
     "          {[y \\in (DOMAIN f) \\cup {x} |-> IF y = x THEN i ELSE f[y]] :\n"
     "                f \\in BagSet, i \\in 1..B[x]}\n"
     "      Biggest == LET Range == {B[x] : x \\in DOMAIN B}\n"
     "                 IN  IF Range = {} THEN 0\n"
     "                                   ELSE CHOOSE r \\in Range :\n"
     "                                           \\A s \\in Range : r \\geq s\n"
     "      RSB[BB \\in UNION {[S -> 1..Biggest] : S \\in SUBSET DOMAIN B}] ==\n"
     "        IF BB = << >> THEN {<< >>}\n"
     "                      ELSE LET x == CHOOSE x \\in DOMAIN BB : TRUE\n"
     "                           IN  Combine(x, RSB[RemoveFromDom(x, BB)])\n"
     "  IN RSB[B]\n"
     "\n\n\n\n\n\n\n\n\n\n\nBagOfAll(F(_), B) ==\n"
     "\n\n\n\n\n\n  [e \\in {F(d) : d \\in BagToSet(B)} |->\n"
     "     Sum( [d \\in BagToSet(B) |-> IF F(d) = e THEN B[d] ELSE 0] ) ]\n"
     "\nBagCardinality(B) ==\n"
     "\n\n\n\n\n  Sum(B)\n"
     "\nCopiesIn(e, B) ==\n"
     "\n\n\n\n  IF BagIn(e, B) THEN B[e] ELSE 0\n"
     "====\n"},
    {"Json",
     "---- MODULE Json ----\n"
     "\nLOCAL INSTANCE Sequences\n"
     "LOCAL INSTANCE FiniteSets\n"
     "LOCAL INSTANCE TLC\n"
     "\n\n\n\n-----------------------------------------------------------------------------\n"
     "\nLOCAL IsSequence(F, D) == TRUE \\/ FALSE\n"
     "\nLOCAL ToJsonKeyValue(F, d) ==\n"
     "  ToString(ToString(d)) \\o \":\" \\o ToString(F[d])\n"
     "\nRECURSIVE ToJsonObjectString(_,_)\n"
     "LOCAL ToJsonObjectString(F, D) ==\n"
     "  LET d == CHOOSE d \\in D: TRUE\n"
     "  IN IF D = DOMAIN F\n"
     "     THEN \"{\" \\o ToJsonKeyValue(F, d) \\o IF D \\ {d} = {}\n"
     "                                         THEN \"}\"\n"
     "                                         ELSE ToJsonObjectString(F, D \\ {d})\n"
     "     ELSE \", \" \\o ToJsonKeyValue(F, d) \\o IF D \\ {d} = {}\n"
     "                                          THEN \"}\"\n"
     "                                          ELSE ToJsonObjectString(F, D \\ {d})\n"
     "\nRECURSIVE ToJsonArrayString(_,_)\n"
     "LOCAL ToJsonArrayString(F, D) ==\n"
     "  LET d == CHOOSE d \\in D: TRUE\n"
     "  IN IF D = DOMAIN F\n"
     "     THEN \"[\" \\o ToString(F[d]) \\o IF D \\ {d} = {}\n"
     "                                   THEN \"]\"\n"
     "                                   ELSE ToJsonArrayString(F, D \\ {d})\n"
     "     ELSE \", \" \\o ToString(F[d]) \\o IF D \\ {d} = {}\n"
     "                                    THEN \"]\"\n"
     "                                    ELSE ToJsonArrayString(F, D \\ {d})\n"
     "\nRECURSIVE ToJsonString(_,_)\n"
     "LOCAL ToJsonString(F, D) ==\n"
     "  IF IsFiniteSet(F) \\/ IsSequence(F, D) THEN\n"
     "    ToJsonArrayString(F, D)\n"
     "  ELSE\n"
     "    ToJsonObjectString(F, D)\n"
     "\nToJson(value) ==\n"
     "\n\n\n\n\n  IF DOMAIN value = {} THEN\n"
     "    \"{}\"\n"
     "  ELSE\n"
     "    ToJsonString(value, DOMAIN value)\n"
     "\nToJsonArray(value) ==\n"
     "\n\n\n  IF DOMAIN value = {} THEN\n"
     "    \"[]\"\n"
     "  ELSE\n"
     "    ToJsonArrayString(value, DOMAIN value)\n"
     "\nToJsonObject(value) ==\n"
     "\n\n\n  IF DOMAIN value = {} THEN\n"
     "    \"{}\"\n"
     "  ELSE\n"
     "    ToJsonObjectString(value, DOMAIN value)\n"
     "\nJsonSerialize(absoluteFilename, value) ==\n"
     "\n\n\n\n  TRUE\n"
     "\nJsonDeserialize(absoluteFilename) ==\n"
     "\n\n\n\n  CHOOSE val : TRUE\n"
     "\nndJsonSerialize(absoluteFilename, value) ==\n"
     "\n\n\n\n\n  TRUE\n"
     "\nndJsonDeserialize(absoluteFilename) ==\n"
     "\n\n\n\n\n  CHOOSE val : TRUE\n"
     "\n====\n"},
    {"Randomization",
     "---- MODULE Randomization ----\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\nLOCAL INSTANCE Naturals\n"
     "LOCAL INSTANCE FiniteSets\n"
     "\n\n\n\n\nRandomSubset(k, S) == CHOOSE T \\in SUBSET S : Cardinality(T) = k\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\nRandomSetOfSubsets(k, n, S) == CHOOSE T \\in SUBSET SUBSET S :\n"
     "                                              Cardinality(T) \\leq k\n"
     "\n\n\n\n\n\n\n\n\n\n\nTestRandomSetOfSubsets(k, n, S) ==\n"
     "              [i \\in 1..5 |-> Cardinality(RandomSetOfSubsets(k, n, S))]\n"
     "====\n"},
    {"TLCExt",
     "---- MODULE TLCExt ----\n"
     "\nLOCAL INSTANCE TLC\n"
     "LOCAL INSTANCE Integers\n"
     "\n\n\n\n\n\n\n\n\nAssertEq(a, b) ==\n"
     "    IF a # b THEN\n"
     "        /\\ PrintT(\"Assertion failed\")\n"
     "        /\\ PrintT(a)\n"
     "        /\\ PrintT(b)\n"
     "        /\\ a = b\n"
     "    ELSE a = b\n"
     "\n\nAssertError(err, exp) ==\n"
     "    LET FailsEval(e) == CHOOSE b \\in BOOLEAN : TRUE\n"
     "        TLCError     == CHOOSE s \\in STRING  : TRUE\n"
     "    IN IF FailsEval(exp) THEN Assert(err = TLCError, TLCError) ELSE TRUE\n"
     "\n\n\nTLCGetOrDefault(key, defaultVal) ==\n"
     "  CHOOSE n : TRUE\n"
     "\nTLCGetAndSet(key, Op(_,_), val, defaultVal) ==\n"
     "  LET oldVal == TLCGetOrDefault(key, defaultVal)\n"
     "  IN CHOOSE v \\in {oldVal} : TLCSet(key, Op(oldVal, val))\n"
     "\n\n\n\n\nTrace ==\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n  TRUE\n"
     "\n\n\nCounterExample ==\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n    TRUE\n"
     "\nToTrace(CE) ==\n"
     "\n\n\n\n\n\n\n\n\n    TRUE\n"
     "\n\n\nTLCModelValue(str) ==\n"
     "\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n\n  CHOOSE v: ToString(v) = str\n"
     "\nTLCDefer(expression) ==\n"
     "\n\n\n\n\n\n\n\n\n\n\n  TRUE\n"
     "\n\n\nTLCNoOp(val) ==\n"
     "\n\n\n\n\n\n  val\n"
     "\n\nPickSuccessor(exp) ==\n"
     "\n\n\n\n\n\n\n\n\n\n\n  IF (exp)\n"
     "  THEN TRUE\n"
     "  ELSE CHOOSE bool \\in BOOLEAN : TRUE\n"
     "\n\n\nTLCCache(expression, closure) ==\n"
     "\n\n\n\n\n\n  expression\n"
     "\nTLCFP(var) ==\n"
     "\n\n\n\n\n  CHOOSE i \\in Int: TRUE\n"
     "\n\n\nTLCEvalDefinition(definitionName) ==\n"
     "\n\n\n\n  TRUE\n"
     "\n====\n"},
    {"_JsonTrace",   /* TLC's -dumpTrace json, without what -loadTrace reads */
     "------------------------------- MODULE _JsonTrace -------------------------------\n"
     "LOCAL INSTANCE TLC\n"
     "LOCAL INSTANCE TLCExt\n"
     "LOCAL INSTANCE Json\n"
     "LOCAL INSTANCE Sequences\n"
     "LOCAL INSTANCE Naturals\n"
     "\n"
     "CONSTANT _JsonTraceFile\n"
     "\n"
     "_JsonTrace ==\n"
     "    IF CounterExample.state = {} \\/ (\"console\" \\in DOMAIN CounterExample /\\ CounterExample[\"console\"] = FALSE) THEN TRUE ELSE\n"
     "        /\\ LET trace == ToTrace(CounterExample)\n"
     "               vars  == UNION { DOMAIN trace[i] : i \\in DOMAIN trace }\n"
     "           IN JsonSerialize(_JsonTraceFile, [counterexample |-> CounterExample, vars |-> vars])\n"
     "        /\\ PrintT(\"CounterExample written: \" \\o _JsonTraceFile)\n"
     "\n"
     "====\n"},
    {"Toolbox",
     "---- MODULE Toolbox ----\n"
     "\n\n\nLOCAL INSTANCE Naturals\n"
     "LOCAL INSTANCE FiniteSets\n"
     "LOCAL INSTANCE TLC\n"
     "\n\n\n\n\n_TETrace ==\n"
     "    CHOOSE f \\in [ (Nat \\ {0}) -> STRING ] : TRUE\n"
     "\nLOCAL _TETraceLength == Cardinality(DOMAIN _TETrace)\n"
     "\n\n\n\n\n_TEPosition ==\n"
     "    IF TLCGet(\"level\") >= _TETraceLength\n"
     "       THEN _TETraceLength\n"
     "       ELSE IF TLCGet(\"level\") = 0 THEN 1 ELSE TLCGet(\"level\")\n"
     "\n====\n"},
    {NULL, NULL}};

static Module **modules;      /* in the order they were read */
static int nmodules;
static Module **finished;     /* each after the modules it uses, as SANY finishes them */
static int nfinished;

static void finish_module(Module *m) {
    finished = xrealloc(finished, sizeof(Module *) * (size_t)(nfinished + 1));
    finished[nfinished++] = m;
}
static char *spec_dir;

static char *read_file(const char *path) {
    FILE *f = fopen(path, "rb");
    if (!f) return NULL;
    Buf b = {0};
    char chunk[1 << 16];   /* not the file's size: a pipe has none */
    for (size_t got; (got = fread(chunk, 1, sizeof chunk, f)) > 0;) buf_add(&b, chunk, got);
    fclose(f);
    if (!b.s) buf_add(&b, "", 0);
    return b.s;
}

static void collect_nested(Module *m) {
    for (int i = 0; i < m->nunits; i++)
        if (m->units[i].kind == 3) {
            m->nested = xrealloc(m->nested, sizeof(Module *) * (size_t)(m->nnested + 1));
            m->nested[m->nnested++] = m->units[i].module;
            collect_nested(m->units[i].module);
        }
}

static Module *find_module(int name);
static Module *load_module(int name, Module *from);

/* Reads the modules a module refers to, in order of reference. */
static void load_references(Module *m) {
    for (int i = 0; i < m->nextends; i++) load_module(m->extends[i], m);
    for (int i = 0; i < m->nunits; i++) {
        Unit *u = &m->units[i];
        if (u->kind == 1 || (u->kind == 0 && u->def->kind == D_INST))
            load_module((int)(intptr_t)u->def->target, m)->instantiated = 1;
        if (u->kind == 3) load_references(u->module);
    }
}

static Module *find_module(int name) {
    for (int i = 0; i < nmodules; i++) if (modules[i]->name == name) return modules[i];
    return NULL;
}

static Module *parse_text(const char *text, const char *path) {
    int n;
    Tok *toks = lex(text, path, &n);
    Parser p = {toks, 0, n, 0, NULL, path};
    Parser *saved = P;
    P = &p;
    Module *m = parse_module(NULL);
    P = saved;
    m->path = (char *)path;
    m->toks = toks;
    m->ntoks = n;
    collect_nested(m);
    return m;
}

static void check_file_name(Module *m, const char *name) {
    if (strcmp(S(m->name), name) == 0) return;
    printf("File name '%s' does not match the name '%s' of the top level module it contains.\n\n", name, S(m->name));
    printf("Error: Parsing or semantic analysis failed.\n");
    exit(MANYAN_ERROR_PARSE);
}

static const char *root_text;   /* the root module's file */
static char *config_text;       /* the configuration file's */

/* Whether line, up to end, is ----* MODULE name ---- as SANY reads one. */
static int module_marker(const char *line, const char *end, const char *name) {
    const char *p = line;
    while (p < end && *p == '-') p++;
    if (p - line < 4) return 0;
    while (p < end && isspace((unsigned char)*p)) p++;
    size_t n = strlen(name);
    if (end - p < 6 || strncmp(p, "MODULE", 6)) return 0;
    const char *q = p += 6;
    while (p < end && isspace((unsigned char)*p)) p++;
    if (p == q || end - p < (long)n || strncmp(p, name, n)) return 0;
    p += n;
    while (p < end && isspace((unsigned char)*p)) p++;
    q = p;
    while (p < end && *p == '-') p++;
    return p == end && p - q >= 3;
}

/* Module name from the root module's file, as SANY reads a monolithic
   spec: from its MODULE line to the next line that starts with ====,
   numbered from that MODULE line; NULL if it has none. */
static char *monolith_module(const char *name) {
    const char *start = NULL;
    for (const char *line = root_text; *line;) {
        const char *end = line + strcspn(line, "\n");
        if (start && !strncmp(line, "====", 4)) return strndup(start, (size_t)(end - start));
        if (!start && module_marker(line, end > line && end[-1] == '\r' ? end - 1 : end, name)) start = line;
        line = *end ? end + 1 : end;
    }
    return start ? strdup(start) : NULL;
}

static Module *load_module(int name, Module *from) {
    for (Module *o = from; o; o = o->outer)
        for (int i = 0; i < o->nnested; i++) if (o->nested[i]->name == name) return o->nested[i];
    Module *m = find_module(name);
    if (m) return m;
    const char *text = NULL;
    char *path = xmalloc(strlen(spec_dir) + strlen(S(name)) + 8);
    sprintf(path, "%s%s.tla", spec_dir, S(name));
    char *file = read_file(path);
    int standard = 0;
    if (file) text = file;
    else {
        for (int i = 0; standard_modules[i].name; i++)
            if (strcmp(standard_modules[i].name, S(name)) == 0) { text = standard_modules[i].text; standard = 1; }
        for (int i = 0; !text && i < nlibrary; i++) if (strcmp(library[i].name, S(name)) == 0) text = library[i].text;
        sprintf(path, "%s.tla", S(name));
        if (!text) text = file = monolith_module(S(name));
    }
    if (!text) {
        printf("Cannot find source file for module %s imported in module %s.\n\n", S(name), S(from->name));
        printf("Error: Parsing or semantic analysis failed.\n");
        exit(MANYAN_ERROR_PARSE);
    }
    m = parse_text(text, path);
    free(file);
    m->standard = standard;
    check_file_name(m, S(name));
    modules = xrealloc(modules, sizeof(Module *) * (size_t)(nmodules + 1));
    modules[nmodules++] = m;
    load_references(m);
    finish_module(m);
    return m;
}

/* ---------------------------------------------------------------- resolver */

typedef struct Scope { int name; Def *def; struct Scope *next; } Scope;

static Module *cur_module;   /* the module being resolved */

static void loc_text(Buf *b, Expr *e) {
    if (!e || !e->mod) { buf_puts(b, "Unknown location"); return; }
    buf_printf(b, "line %d, col %d to line %d, col %d of module %s", e->l1, e->c1, e->l2, e->c2, S(e->mod->name));
}

/* An expression as TLC names it after a message: a number as written,
   else its location. */
static void node_text(Buf *b, Expr *e) {
    if (e && e->kind == X_NUM) buf_puts(b, S(e->op));
    else loc_text(b, e);
}

/* Their texts in the arena, for a message an error may never free. */
static const char *loc_str(Expr *e) { Buf b = {0}; loc_text(&b, e); return buf_take(&b); }
static const char *node_str(Expr *e) { Buf b = {0}; node_text(&b, e); return buf_take(&b); }

/* A new line naming e, if it has a location. */
static void loc_line(Buf *b, Expr *e) {
    if (!e || !e->mod) return;
    buf_puts(b, "\n");
    node_text(b, e);
}

static _Noreturn void semantic_error(Expr *where, const char *fmt, ...) {
    if (breakpoint) breakpoint_error(0, NULL);
    char msg[1024];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);
    printf("Semantic errors:\n\n*** Errors: 1\n\n%s\n\n%s\n\n", loc_str(where), msg);
    printf("Error: Parsing or semantic analysis failed.\n");
    exit(MANYAN_ERROR_PARSE);
}

static Def *scope_lookup(Scope *sc, int name);
static Sym *module_lookup(Module *m, int name);

/* A new name in scope, which must not hide one (§5.6). */
static Scope *bind(Scope *sc, int name, Def *d) {
    Def *old = scope_lookup(sc, name);
    Sym *sym = old || !cur_module ? NULL : module_lookup(cur_module, name);
    if ((old && old != d) || (sym && sym->def != d))
        semantic_error(d->where, "Multiply-defined symbol '%s': this definition or declaration conflicts with another one.", S(name));
    Scope *s = NEW(Scope);
    s->name = name; s->def = d; s->next = sc;
    return s;
}

static Sym *module_lookup(Module *m, int name) {
    for (Module *o = m; o; o = o->outer) {
        int limit = o == m ? o->nsyms : 0;
        if (o != m) {
            /* an enclosing module's symbols defined before the nested module */
            Module *inner = m;
            while (inner->outer != o) inner = inner->outer;
            limit = inner->nouter_syms;
        }
        for (int i = limit - 1; i >= 0; i--) if (o->syms[i].name == name) return &o->syms[i];
    }
    return NULL;
}

/* A nested module's own declaration or definition of a name its enclosing
   modules already give it: SANY warns of a declaration repeated, of the
   same kind and arity, and rejects any other. */
static Module *file_module(Module *m) {
    while (m->outer) m = m->outer;
    return m;
}

/* A location as SANY gives it, in the module of its file. */
static void file_loc_text(Buf *b, Expr *e) {
    buf_printf(b, "line %d, col %d to line %d, col %d of module %s", e->l1, e->c1, e->l2, e->c2, S(file_module(e->mod)->name));
}

static void check_outer(Module *m, Def *d) {
    Sym *s = m->outer ? module_lookup(m, d->name) : NULL;
    if (!s || (m->nsyms && s >= m->syms && s < m->syms + m->nsyms)) return;   /* its own: add_sym's */
    Def *o = s->def;
    Buf here = {0}, there = {0};
    file_loc_text(&here, d->where);
    file_loc_text(&there, o->where);
    if ((d->kind != D_CONST && d->kind != D_VAR) || o->kind != d->kind || o->arity != d->arity)
        semantic_error(d->where, "Multiple declarations or definitions for symbol %s.\nThis duplicates the one at %s.", S(d->name), there.s);
    Module *file = file_module(m);
    buf_printf(&file->warnings, "%s\n\nMultiple declarations or definitions for symbol %s.  \nThis duplicates the one at %s.\n\n\n",
               here.s, S(d->name), there.s);
    file->nwarnings++;
    free(here.s);
    free(there.s);
}

/* SANY's warnings so far, all of them printed as each file's module is
   processed. */
static Buf warnings;
static int nwarnings;

static void print_warnings(Module *m) {
    buf_add(&warnings, m->warnings.s ? m->warnings.s : "", m->warnings.n);
    nwarnings += m->nwarnings;
    if (nwarnings) printf("*** Warnings: %d\n\n%s", nwarnings, warnings.s);
}

static Sym *own_sym(Module *m, int name) {
    for (int i = 0; i < m->nsyms; i++) if (m->syms[i].name == name) return &m->syms[i];
    return NULL;
}

/* A definition's location as SANY gives it: from its name to the end of its body. */
static Expr def_span(Def *d) {
    Expr e = *d->where;
    Expr *b = d->body;
    if (b) { e.l2 = b->pl2 ? b->pl2 : b->l2; e.c2 = b->pl2 ? b->pc2 : b->c2; }
    return e;
}

/* Whether the definition d, which m extends or, with instance, instantiates,
   gives way to another of its name m has: as SANY, with a warning, keeping
   the first. A declaration conflicts. The warning is at d, or at a LOCAL
   INSTANCE. */
static int inherited_conflict(Module *m, Def *d, Def *instance) {
    Sym *old = own_sym(m, d->name);
    if (!old || old->def == d || d->kind == D_CONST || d->kind == D_VAR || old->def->kind == D_CONST || old->def->kind == D_VAR)
        return 0;
    Buf here = {0}, there = {0};
    Expr at = instance && instance->local ? *instance->where : def_span(d), span = def_span(old->def);
    file_loc_text(&here, &at);
    file_loc_text(&there, &span);
    Module *file = file_module(m);
    buf_printf(&file->warnings, instance ? "%s\n\nMultiple declarations or definitions for symbol %s.  \nThis duplicates the one at %s.\n\n\n"
                                         : "%s\n\nWarning: the definition of '%s' conflicts with \nits definition at %s.\n\n\n",
               here.s, S(d->name), there.s);
    file->nwarnings++;
    free(here.s);
    free(there.s);
    return 1;
}

static void add_sym(Module *m, int name, Def *def, Def **path, int npath, int local, Expr *where) {
    for (int i = 0; i < m->nsyms; i++)
        if (m->syms[i].name == name) {
            if (m->syms[i].def == def) return;
            if (def->kind != D_RECURSIVE && m->syms[i].def->kind != D_RECURSIVE && npath == 0 && m->syms[i].npath == 0)
                semantic_error(where, "Multiply-defined symbol '%s': this definition or declaration conflicts with another one.", S(name));
            m->syms[i].def = def; m->syms[i].path = path; m->syms[i].npath = npath; m->syms[i].local = local;
            return;
        }
    if (m->nsyms == m->capsyms) {
        m->capsyms = m->capsyms ? m->capsyms * 2 : 64;
        m->syms = xrealloc(m->syms, sizeof(Sym) * (size_t)m->capsyms);
    }
    Sym *s = &m->syms[m->nsyms++];
    s->name = name; s->def = def; s->path = path; s->npath = npath; s->local = local;
}

static void add_decl(Module *m, Def *d) {
    for (int i = 0; i < m->ndecls; i++) if (m->decls[i] == d) return;
    if (m->ndecls == m->capdecls) {
        m->capdecls = m->capdecls ? m->capdecls * 2 : 16;
        m->decls = xrealloc(m->decls, sizeof(Def *) * (size_t)m->capdecls);
    }
    m->decls[m->ndecls++] = d;
}

static void resolve_expr(Expr *e, Scope *sc);
static void resolve_def(Def *d, Scope *sc);
static void resolve_module(Module *m);
static void check_levels(Expr *e, int max);
static void check_def_levels(Def *d);

static Def *scope_lookup(Scope *sc, int name) {
    for (; sc; sc = sc->next) if (sc->name == name) return sc->def;
    return NULL;
}

static void check_arity(Expr *e, Def *d, int n) {
    int want = d->kind == D_OP ? d->nparams : d->kind == D_PARAM || d->kind == D_CONST ? d->arity : 0;
    if (d->kind == D_INST) want = d->nparams;
    if (n != want) {
        if (want == 0) semantic_error(e, "The operator %s requires 0 arguments.", S(d->name));
        semantic_error(e, "The operator %s requires %d arguments.", S(d->name), want);
    }
}

static void resolve_args(Expr **args, int n, Scope *sc) {
    for (int i = 0; i < n; i++) if (args[i]) resolve_expr(args[i], sc);
}

/* An operator symbol passed as an argument: a Def to call. Core
   operators are wrapped in a definition that applies them. */
static Def *operator_def(Expr *at, int op, Scope *sc) {
    Def *d = scope_lookup(sc, op);
    if (d) return d;
    Sym *s = module_lookup(cur_module, op);
    if (s && !s->npath) return s->def;
    /* A built-in operator: an infix one takes two arguments, others one. */
    int n = 1;
    for (int i = 0; op_table[i].name; i++) if (op_table[i].fix == INFIX && strcmp(op_table[i].name, S(op)) == 0) n = 2;
    Def *w = NEW(Def);
    w->kind = D_OP;
    w->name = op;
    w->nparams = n;
    w->params = NEWN(Def *, n);
    w->level = -1;
    w->var_index = -1;
    w->mod = cur_module;
    Expr *body = NEW(Expr);
    *body = *at;
    body->kind = X_OP;
    body->op = op;
    body->n = n;
    body->args = NEWN(Expr *, n);
    Scope *inner = sc;
    for (int i = 0; i < n; i++) {
        w->params[i] = NEW(Def);
        w->params[i]->kind = D_PARAM;
        w->params[i]->name = intern(i ? "#b" : "#a");
        inner = bind(inner, w->params[i]->name, w->params[i]);
        Expr *ref = NEW(Expr);
        *ref = *at;
        ref->kind = X_NAME;
        ref->nseg = 1;
        ref->segs = NEW(Seg);
        ref->segs->name = w->params[i]->name;
        ref->op = w->params[i]->name;
        body->args[i] = ref;
    }
    resolve_expr(body, inner);
    w->body = body;
    return w;
}

static int expr_level(Expr *e);

/* TLA+ has no raw actions in temporal formulas (§6.10). */
static void check_temporal(Expr *e) {
    switch (e->kind) {
    case K_ALWAYS:
        if (expr_level(e->args[0]) == 2 && e->args[0]->kind != X_SQACT)
            semantic_error(e, "[] followed by action not of form [A]_v.");
        return;
    case K_EVENTUALLY:
        if (expr_level(e->args[0]) == 2 && e->args[0]->kind != X_ANGLEACT)
            semantic_error(e, "<> followed by action not of form <<A>>_v.");
        return;
    case K_LEADSTO: case K_WHILE:
        if (expr_level(e->args[0]) == 2 || expr_level(e->args[1]) == 2)
            semantic_error(e, "Action used where only temporal formula or state predicate allowed.");
        return;
    case X_FORALL: case X_EXISTS:
        if (expr_level(e->args[0]) == 3)
            for (int i = 0; i < e->nb; i++)
                if (e->bounds[i].set && expr_level(e->bounds[i].set) == 2)
                    semantic_error(e->bounds[i].set, "Action-level bound of quantified temporal formula.");
        return;
    }
}

static void resolve_bounds(Expr *e, Scope **sc) {
    Scope *outer = *sc;
    for (int i = 0; i < e->nb; i++) {
        Bound *b = &e->bounds[i];
        if (b->set) resolve_expr(b->set, outer);
        b->defs = NEWN(Def *, b->n);
        for (int j = 0; j < b->n; j++) {
            Def *d = NEW(Def);
            d->kind = D_BOUND;
            d->name = b->names[j];
            d->var_index = -1;
            b->defs[j] = d;
            *sc = bind(*sc, d->name, d);
        }
    }
}

static const struct { const char *name; int kind; } core_ops[] = {
    {"/\\", K_AND}, {"\\/", K_OR}, {"~", K_NOT}, {"=>", K_IMPLIES}, {"<=>", K_EQUIV}, {"=", K_EQ},
    {"/=", K_NEQ}, {"\\in", K_IN}, {"\\notin", K_NOTIN}, {"\\cup", K_CUP}, {"\\cap", K_CAP},
    {"\\", K_SETMINUS}, {"\\subseteq", K_SUBSETEQ}, {"SUBSET", K_SUBSET}, {"UNION", K_UNION},
    {"DOMAIN", K_DOMAIN}, {"'", K_PRIME}, {"UNCHANGED", K_UNCHANGED}, {"ENABLED", K_ENABLED},
    {"[]", K_ALWAYS}, {"<>", K_EVENTUALLY}, {"~>", K_LEADSTO}, {"\\X", K_TIMES}, {"\\cdot", K_CDOT},
    {"-+->", K_WHILE}, {"BOOLEAN", K_BOOLEAN}, {"STRING", K_STRINGSET}, {NULL, 0}};

/* The expression labeled `name` in x, but not in another label in it or
   in a LET definition, which have labels of their own (§5.7). */
static Expr *find_label(Expr *x, int name, int own) {
    if (!x) return NULL;
    if (x->label && !own) return x->label->name == name ? x : NULL;
    if (x->kind == X_LET) return find_label(x->args[0], name, 0);
    Expr *l = NULL;
    for (int i = 0; i < x->n && !l; i++) l = find_label(x->args[i], name, 0);
    for (int i = 0; i < x->nb && !l; i++) l = find_label(x->bounds[i].set, name, 0);
    return l;
}

/* The LET expressions on the way from x to y, outermost first, after n
   others; -1 if y is not in x. */
static int lets_to(Expr *x, Expr *y, Expr **lets, int n) {
    if (!x) return -1;
    if (x == y) return n;
    int r = -1;
    if (x->kind == X_LET && n < 64) {
        lets[n++] = x;
        for (int i = 0; i < x->ndefs && r < 0; i++) r = lets_to(x->defs[i]->body, y, lets, n);
    }
    for (int i = 0; i < x->n && r < 0; i++) r = lets_to(x->args[i], y, lets, n);
    for (int i = 0; i < x->nb && r < 0; i++) r = lets_to(x->bounds[i].set, y, lets, n);
    for (int i = 0; x->kind == X_EXCEPT && i < x->n - 1 && r < 0; i++)
        for (int k = 0; k < x->paths[i].n && r < 0; k++) r = lets_to(x->paths[i].keys[k], y, lets, n);
    return r;
}

/* Which of n operands selector sel picks, from 1; 0 for none. */
static int operand(int sel, int n) {
    if (sel > 0) return sel <= n ? sel : 0;
    if (sel == SEL_LL) return n > 0;
    if (sel == SEL_GG) return n == 2 ? 2 : 0;
    return 0;
}

/* The parameters met selecting a subexpression, and their arguments. */
typedef struct { Def *params[64]; Expr *args[64]; int np, nargs, missing; } Selection;

/* The parameters defs, with the arguments seg gives them, if any. */
static void take(Selection *sel, Expr *e, Def **defs, int n, Seg *seg) {
    if (seg->n && seg->n != n) semantic_error(e, "The operator %s requires %d arguments.", S(e->op), n);
    if (sel->np + n > 64) semantic_error(e, "Too many parameters.");
    for (int k = 0; k < n; k++) {
        sel->params[sel->np++] = defs[k];
        if (seg->n) sel->args[sel->nargs++] = seg->args[k];
    }
    sel->missing |= n && !seg->n;
}

/* d(a)!lab(b)!2!(c)...: the subexpression that segments i.. of e name, as
   an operator of every parameter met on the way: d's, the labels', and the
   identifiers !(c) or !@ bind. Its arguments, if given, are in *args. */
static Def *subexpression(Expr *e, Def *d, int i, Expr ***args, int *nargs) {
    if (d->kind != D_OP || d->local == 2 || !d->body)
        semantic_error(e, "Cannot take subexpression of `%s'.", S(d->name));
    Selection sel = {0};
    take(&sel, e, d->params, d->nparams, &e->segs[i]);
    Expr *cur = d->body;
    int names = 1, own = 0;   /* a name next is a label, else a LET definition */
    for (int k = i + 1; k < e->nseg; k++) {
        Seg *s = &e->segs[k];
        if (s->sel == 0 && names) {
            cur = find_label(cur, s->name, own);
            if (!cur) semantic_error(e, "Unknown label `%s'.", S(s->name));
            take(&sel, e, cur->label->defs, cur->label->n, s);
            own = 1;
        } else if (s->sel == 0) {
            Def *x = NULL;
            for (int j = 0; cur->kind == X_LET && j < cur->ndefs && !x; j++)
                if (cur->defs[j]->name == s->name) x = cur->defs[j];
            if (!x || !x->body) semantic_error(e, "Unknown operator: `%s'.", S(s->name));
            take(&sel, e, x->params, x->nparams, s);
            cur = x->body;
            names = 1, own = 0;
        } else if (s->sel == SEL_COLON) {
            names = 0;
        } else {
            int n = 0, first = k;
            if (cur->kind == X_LET) {
                if (operand(s->sel, 1)) n = 1, cur = cur->args[0];
            } else if (cur->nb) {
                if (s->sel == SEL_NULL || s->sel == SEL_AT) {
                    Def *bound[64];
                    int nbound = 0;
                    for (int b = 0; b < cur->nb; b++)
                        for (int j = 0; j < cur->bounds[b].n && nbound < 64; j++) bound[nbound++] = cur->bounds[b].defs[j];
                    take(&sel, e, bound, nbound, s);
                    n = 1, cur = cur->args[0];
                } else if ((n = operand(s->sel, cur->bounds[0].set ? cur->nb : 0))) {
                    cur = cur->bounds[n - 1].set;
                }
            } else if (cur->kind == X_CASE) {   /* an arm, then its guard or value */
                int arm = operand(s->sel, cur->n / 2);
                if (arm && ++k < e->nseg && (n = operand(e->segs[k].sel, 2))) cur = cur->args[2 * arm - 3 + n];
            } else if (cur->kind == X_DOT) {
                if ((n = operand(s->sel, 2)) == 1) cur = cur->args[0];
                else if (n) {
                    Expr *f = NEW(Expr);
                    *f = *cur;
                    f->kind = X_STR, f->n = 0, f->label = NULL;
                    f->num = cur->op;
                    cur = f;
                }
            } else if ((n = operand(s->sel, cur->n)) && (cur->kind != X_EXCEPT || n == 1)) {
                cur = cur->args[n - 1];
            }
            if (!n || !cur) semantic_error(e, "Nonexistent operand specified by selector %d of %s.", first - i, S(d->name));
            names = 0, own = 0;
        }
    }
    if (sel.missing && sel.nargs) semantic_error(e, "The operator %s requires %d arguments.", S(e->op), sel.np);
    /* The LET definitions around the subexpression are in scope in it. */
    Expr *lets[64];
    Expr *body = cur;
    for (int n = lets_to(d->body, cur, lets, 0); n > 0; n--) {
        Expr *let = NEW(Expr);
        *let = *lets[n - 1];
        let->label = NULL;
        let->args = NEWN(Expr *, 1);
        let->args[0] = body;
        body = let;
    }
    Def *f = NEW(Def);
    f->kind = D_OP;
    f->name = d->name;
    f->mod = d->mod;
    f->where = d->where;
    f->level = f->var_index = -1;
    f->nparams = sel.np;
    f->params = NEWN(Def *, sel.np);
    memcpy(f->params, sel.params, sizeof(Def *) * (size_t)sel.np);
    f->body = body;
    *nargs = sel.nargs;
    *args = NEWN(Expr *, sel.nargs);
    memcpy(*args, sel.args, sizeof(Expr *) * (size_t)sel.nargs);
    return f;
}

/* Resolves A!B(x)!C: each segment but the last names an instance, or
   the segments after a definition select a subexpression of it. */
static void resolve_path(Expr *e, Scope *sc) {
    Def *path[32];
    Seg pargs[32];
    int np = 0;
    memset(pargs, 0, sizeof pargs);
    Module *m = cur_module;
    Def *d = NULL;
    Expr **args = NULL;
    int nargs = 0;
    for (int i = 0; i < e->nseg; i++) resolve_args(e->segs[i].args, e->segs[i].n, sc);
    for (int i = 0; i < e->nseg; i++) {
        Seg *s = &e->segs[i];
        Sym *sym = NULL;
        if (i == 0) {
            d = scope_lookup(sc, s->name);
            if (!d) sym = module_lookup(m, s->name);
        } else {
            sym = module_lookup(m, s->name);
            if (sym && sym->local) sym = NULL;
        }
        if (sym) {
            for (int k = 0; k < sym->npath && np < 32; k++) path[np++] = sym->path[k];
            d = sym->def;
        }
        if (!d) semantic_error(e, "Unknown operator: `%s'.", S(s->name));
        if (i + 1 < e->nseg && d->kind == D_INST) {
            check_arity(e, d, s->n);
            pargs[np] = *s;
            path[np++] = d;
            m = d->target;
            d = NULL;
        } else if (i + 1 < e->nseg) {
            d = subexpression(e, d, i, &args, &nargs);
            break;
        } else {
            if (s->n || d->kind != D_OP || !d->nparams) check_arity(e, d, s->n);   /* bare, an operator argument */
            args = s->args;
            nargs = s->n;
        }
    }
    e->kind = np ? K_INSTCALL : K_CALL;
    e->def = d;
    e->defs = NEWN(Def *, np);
    memcpy(e->defs, path, sizeof(Def *) * (size_t)np);
    e->ndefs = np;
    e->args = args;
    e->n = nargs;
    /* segs now holds each instance's arguments, aligned with defs. */
    e->segs = NEWN(Seg, np);
    memcpy(e->segs, pargs, sizeof(Seg) * (size_t)np);
    e->nseg = np;
}

static void resolve_name(Expr *e, Scope *sc) {
    if (e->nseg > 1) { resolve_path(e, sc); return; }
    Seg *s = &e->segs[0];
    resolve_args(s->args, s->n, sc);
    e->args = s->args;
    e->n = s->n;
    Def *d = scope_lookup(sc, s->name);
    if (d) {
        if (d->kind == D_INST) semantic_error(e, "Operator name %s is incomplete.", S(d->name));
        if (d->kind == D_BOUND || (d->kind == D_PARAM && d->arity == 0 && s->n == 0)) {
            if (s->n) semantic_error(e, "The operator %s requires 0 arguments.", S(d->name));
            e->kind = K_BOUND;
        } else if (d->kind == D_PARAM) {
            if (s->n) check_arity(e, d, s->n);   /* bare, it is an operator argument */
            e->kind = K_PARAMCALL;
        } else {
            if (s->n || !d->nparams) check_arity(e, d, s->n);
            e->kind = K_CALL;
        }
        e->def = d;
        return;
    }
    Sym *sym = module_lookup(cur_module, s->name);
    if (!sym || sym->def->kind == D_RECURSIVE) {   /* located, as SANY, at the name */
        Expr name = *e;
        name.l2 = name.l1;
        name.c2 = name.c1 + (int)strlen(S(s->name)) - 1;
        semantic_error(&name, "Unknown operator: `%s'.", S(s->name));
    }
    d = sym->def;
    if (d->kind == D_INST) semantic_error(e, "Operator name %s is incomplete.", S(d->name));
    int bare = s->n == 0 && (d->kind == D_OP ? d->nparams : d->kind == D_CONST ? d->arity : 0) > 0;
    if (!bare) check_arity(e, d, s->n);   /* bare, it is an operator argument */
    e->def = d;
    if (d->kind == D_CONST || d->kind == D_VAR) {
        e->kind = d->arity ? K_PARAMCALL : K_DECL;
    } else if (sym->npath) {
        e->kind = K_INSTCALL;
        e->defs = sym->path;
        e->ndefs = sym->npath;
        e->segs = NEWN(Seg, sym->npath);
        e->nseg = sym->npath;
    } else {
        e->kind = K_CALL;
    }
}

/* The function definitions being resolved: one named in its own body is
   recursive (§6.6). */
static Def *open_defs[64];
static int nopen_defs;

static void resolve_expr(Expr *e, Scope *sc) {
    if (e->label && !e->label->defs) {
        Label *l = e->label;
        l->defs = NEWN(Def *, l->n);
        for (int i = 0; i < l->n; i++)
            if (!(l->defs[i] = scope_lookup(sc, l->names[i]))) semantic_error(e, "Unknown operator: `%s'.", S(l->names[i]));
    }
    switch (e->kind) {
    case X_NUM: case X_BOOL: case X_AT:
        return;
    case X_STR:
        e->num = intern_n(e->text, e->len);
        mk_str(e->num);   /* a string the specification has, which Gen may make */
        return;
    case X_NAME:
        resolve_name(e, sc);
        for (int i = 0; i < nopen_defs; i++) if (open_defs[i] == e->def) e->def->self = 1;
        return;
    case X_OPREF:
        e->def = operator_def(e, e->op, sc);
        return;
    case X_LAMBDA: {
        Scope *inner = sc;
        for (int i = 0; i < e->def->nparams; i++) inner = bind(inner, e->def->params[i]->name, e->def->params[i]);
        e->def->mod = cur_module;
        resolve_expr(e->def->body, inner);
        return;
    }
    case X_OP: {
        resolve_args(e->args, e->n, sc);
        for (int i = 0; core_ops[i].name; i++)
            if (strcmp(core_ops[i].name, S(e->op)) == 0) { e->kind = (short)core_ops[i].kind; check_temporal(e); return; }
        Def *d = scope_lookup(sc, e->op);
        Sym *sym = d ? NULL : module_lookup(cur_module, e->op);
        if (sym) d = sym->def;
        if (!d) semantic_error(e, "Unknown operator: `%s'.", S(e->op));
        check_arity(e, d, e->n);
        e->def = d;
        if (d->kind == D_PARAM || d->kind == D_CONST) e->kind = K_PARAMCALL;
        else if (sym && sym->npath) {
            e->kind = K_INSTCALL;
            e->defs = sym->path;
            e->ndefs = sym->npath;
            e->segs = NEWN(Seg, sym->npath);
            e->nseg = sym->npath;
        }
        else e->kind = K_CALL;
        return;
    }
    case X_FORALL: case X_EXISTS: case X_CHOOSE: case X_FILTER: case X_MAP: case X_FCN:
    case X_TFORALL: case X_TEXISTS: {
        Scope *inner = sc;
        resolve_bounds(e, &inner);
        resolve_args(e->args, e->n, inner);
        check_temporal(e);
        return;
    }
    case X_LET: {
        Scope *inner = sc;
        for (int i = 0; i < e->ndefs; i++)
            if (e->defs[i]->recursive) inner = bind(inner, e->defs[i]->name, e->defs[i]);
        for (int i = 0; i < e->ndefs; i++) {
            Def *d = e->defs[i];
            d->local = 2;   /* a LET definition: bound in the environment */
            resolve_def(d, inner);
            if (!d->recursive) inner = bind(inner, d->name, d);
        }
        resolve_args(e->args, e->n, inner);
        return;
    }
    case X_EXCEPT:
        resolve_args(e->args, e->n, sc);
        for (int i = 0; i < e->n - 1; i++) resolve_args(e->paths[i].keys, e->paths[i].n, sc);
        return;
    default:
        resolve_args(e->args, e->n, sc);
        if (e->kind == X_RECORD || e->kind == X_RCDSET) PUSH(cur_module->records, cur_module->nrecords, e);
        return;
    }
}

static void resolve_def(Def *d, Scope *sc) {
    d->mod = cur_module;
    Scope *inner = sc;
    for (int i = 0; i < d->nparams; i++) {
        d->params[i]->var_index = -1;
        inner = bind(inner, d->params[i]->name, d->params[i]);
    }
    if (d->kind == D_FCN) {
        Expr tmp;
        memset(&tmp, 0, sizeof tmp);
        tmp.bounds = d->bounds;
        tmp.nb = d->nb;
        resolve_bounds(&tmp, &inner);
        inner = bind(inner, d->name, d);
    }
    if (d->kind == D_INST) {
        int name = (int)(intptr_t)d->target;
        Module *t = load_module(name, cur_module);
        Module *saved = cur_module;
        resolve_module(t);
        cur_module = saved;
        d->target = t;
        Def **decls = NEWN(Def *, t->ndecls);
        Expr **exprs = NEWN(Expr *, t->ndecls);
        for (int i = 0; i < t->ndecls; i++) {
            Def *decl = t->decls[i];
            decls[i] = decl;
            for (int j = 0; j < d->nsubst; j++)
                if (d->subst_decl[j]->name == decl->name) exprs[i] = d->subst_expr[j];
            if (!exprs[i]) {
                Expr *ref = NEW(Expr);
                if (d->where) *ref = *d->where;
                ref->kind = decl->arity && !scope_lookup(inner, decl->name) ? X_OPREF : X_NAME;   /* Op(_) <- Op */
                ref->nseg = 1;
                ref->segs = NEW(Seg);
                ref->segs->name = decl->name;
                ref->op = decl->name;
                if (!scope_lookup(inner, decl->name) && !module_lookup(cur_module, decl->name))
                    semantic_error(d->where, "The constant or variable %s of module %s is not defined in the instantiating module.",
                                   S(decl->name), S(t->name));
                exprs[i] = ref;
            }
            resolve_expr(exprs[i], inner);
        }
        d->nsubst = t->ndecls;
        d->subst_decl = decls;
        d->subst_expr = exprs;
        return;
    }
    int open = d->kind == D_FCN && nopen_defs < 64;
    if (open) open_defs[nopen_defs++] = d;
    if (d->body) resolve_expr(d->body, inner);
    nopen_defs -= open;
}

/* SANY's linter: a warning for a record field named as a definition or
   declaration of the module, unless a record with the same fields has
   one built from a declaration, a parameter or a bound identifier. */
static Buf lint;

static int from_decls(Expr *e, List *seen) {
    if (!e) return 0;
    if (e->kind == K_BOUND || e->kind == K_PARAMCALL || e->kind == K_DECL || e->kind == K_BOOLEAN) return 1;
    if ((e->kind == K_CALL || e->kind == K_INSTCALL) && e->def) {
        Def *d = e->def;
        if (d->kind == D_CONST || d->kind == D_VAR || d->kind == D_PARAM) return 1;
        const char *std = d->mod && d->mod->standard ? S(d->mod->name) : "";
        if ((!strcmp(std, "Integers") && d->name == intern("Int")) || (!strcmp(std, "Naturals") && d->name == intern("Nat"))) return 1;
        int visited = 0;
        for (int i = 0; i < seen->n && !visited; i++) visited = (Def *)seen->v[i] == d;
        if (!visited) {
            list_add(seen, (Value *)d);
            if (from_decls(d->body, seen)) return 1;
            for (int i = 0; i < d->nb; i++) if (from_decls(d->bounds[i].set, seen)) return 1;
        }
    }
    for (int i = 0; i < e->n; i++) if (from_decls(e->args[i], seen)) return 1;
    for (int i = 0; i < e->nb; i++) if (from_decls(e->bounds[i].set, seen)) return 1;
    if (e->kind == X_LET) for (int i = 0; i < e->ndefs; i++) if (from_decls(e->defs[i]->body, seen)) return 1;
    if (e->kind == X_LAMBDA && from_decls(e->def->body, seen)) return 1;
    if (e->kind == X_EXCEPT)
        for (int i = 0; i < e->n - 1; i++)
            for (int k = 0; k < e->paths[i].n; k++) if (from_decls(e->paths[i].keys[k], seen)) return 1;
    if (e->kind == K_INSTCALL)
        for (int i = 0; i < e->nseg; i++)
            for (int k = 0; k < e->segs[i].n; k++) if (from_decls(e->segs[i].args[k], seen)) return 1;
    return 0;
}

static int same_fields(Expr *a, Expr *b) {
    if (a->nseg != b->nseg) return 0;
    for (int i = 0; i < a->nseg; i++) {
        int found = 0;
        for (int j = 0; j < b->nseg && !found; j++) found = a->segs[i].name == b->segs[j].name;
        if (!found) return 0;
    }
    return 1;
}

/* m and the modules it extends, transitively. */
static void extended_set(Module *m, List *out) {
    for (int i = 0; i < out->n; i++) if ((Module *)out->v[i] == m) return;
    list_add(out, (Value *)m);
    for (int i = 0; i < m->nextends; i++) extended_set(load_module(m->extends[i], m), out);
}

static void lint_records(Module *m) {
    if (m->standard || !m->nrecords) return;
    List mods = {0};
    extended_set(m, &mods);
    for (int r = 0; r < m->nrecords; r++) {
        Expr *rec = m->records[r];
        int understood = 0;
        for (int k = 0; k < mods.n && !understood; k++) {
            Module *x = (Module *)mods.v[k];
            for (int i = 0; i < x->nrecords && !understood; i++)
                if (same_fields(x->records[i], rec))
                    for (int f = 0; f < x->records[i]->n && !understood; f++) {
                        List seen = {0};
                        understood = from_decls(x->records[i]->args[f], &seen);
                    }
        }
        for (int f = 0; f < rec->nseg && !understood; f++) {
            Seg *field = &rec->segs[f];
            Sym *sym = module_lookup(m, field->name);
            if (!sym) continue;
            Def *d = sym->def;
            Expr at = d->kind == D_CONST || d->kind == D_VAR ? *d->where : def_span(d);
            Buf there = {0};
            file_loc_text(&there, &at);
            const char *n = S(field->name);
            buf_printf(&lint, "line %d, col %d to line %d, col %d of module %s\n\n"
                       "The field name \"%s\" in the record constructor is identical to the existing definition or declaration\n"
                       "named %s, located at %s.\n"
                       "The field in the record will not take the value of the %s definition or declaration.\n"
                       "In TLA+, field names in records are strings, regardless of any similarly named declarations or definitions.\n"
                       "Therefore, DOMAIN [%s |-> ...] = {\"%s\"} holds true.\n\n\n",
                       field->line, field->col, field->line, field->col + (int)strlen(n) - 1, S(m->name), n, n, there.s, n, n, n);
            free(there.s);
        }
    }
}

static void resolve_module(Module *m) {
    if (m->resolved == 1) {
        printf("Circular dependency among .tla files: module %s depends on itself.\n", S(m->name));
        printf("Error: Parsing or semantic analysis failed.\n");
        exit(MANYAN_ERROR_PARSE);
    }
    if (m->resolved) return;
    m->resolved = 1;
    Module *saved = cur_module;
    for (int i = 0; i < m->nextends; i++) {
        Module *x = load_module(m->extends[i], m);
        resolve_module(x);
    }
    cur_module = m;
    for (int i = 0; i < m->nextends; i++) {
        Module *x = load_module(m->extends[i], m);
        for (int k = 0; k < x->nsyms; k++)
            if (!x->syms[k].local && !inherited_conflict(m, x->syms[k].def, NULL))
                add_sym(m, x->syms[k].name, x->syms[k].def, x->syms[k].path, x->syms[k].npath, 0, NULL);
        for (int k = 0; k < x->ndecls; k++) add_decl(m, x->decls[k]);
    }
    /* A name is defined before it is used; RECURSIVE declares a definition to come. */
    for (int i = 0; i < m->nunits; i++) {
        Unit *u = &m->units[i];
        cur_module = m;
        if (u->kind == 0) {
            Def *d = u->def;
            if (d->kind == D_CONST || d->kind == D_VAR) {
                d->mod = m;
                check_outer(m, d);
                add_sym(m, d->name, d, NULL, 0, 0, d->where);
                add_decl(m, d);
            } else if (d->kind == D_OP || d->kind == D_FCN || d->kind == D_INST) {
                resolve_def(d, NULL);
                check_outer(m, d);
                add_sym(m, d->name, d, NULL, 0, u->local, d->where);
            } else {
                resolve_def(d, NULL);
            }
        } else if (u->kind == 4 && u->def->body) {
            /* A theorem's or assumption's name is an operator without parameters. */
            Def *d = NEW(Def);
            *d = *u->def;
            d->kind = D_OP;
            d->level = d->var_index = -1;
            resolve_def(d, NULL);
            add_sym(m, d->name, d, NULL, 0, 0, NULL);
        } else if (u->kind == 4 && u->def->kind == D_RECURSIVE) {
            for (int k = i + 1; k < m->nunits; k++)
                if (m->units[k].kind == 0 && m->units[k].def->name == u->def->name &&
                    (m->units[k].def->kind == D_OP || m->units[k].def->kind == D_FCN)) {
                    m->units[k].def->recursive = 1;
                    add_sym(m, u->def->name, m->units[k].def, NULL, 0, m->units[k].local, m->units[k].def->where);
                    break;
                }
        } else if (u->kind == 1) {
            Def *d = u->def;
            resolve_def(d, NULL);
            cur_module = m;
            Module *t = d->target;
            for (int k = 0; k < t->nsyms; k++) {
                Sym *s = &t->syms[k];
                if (s->local || s->def->kind == D_CONST || s->def->kind == D_VAR) continue;
                if (inherited_conflict(m, s->def, d)) continue;
                Def **path = NEWN(Def *, s->npath + 1);
                path[0] = d;
                if (s->npath) memcpy(path + 1, s->path, sizeof(Def *) * (size_t)s->npath);
                add_sym(m, s->name, s->def, path, s->npath + 1, u->local, NULL);
            }
        } else if (u->kind == 2 && !u->def) {   /* a named one is resolved with its name */
            resolve_expr(u->expr, NULL);
        } else if (u->kind == 3) {
            u->module->nouter_syms = m->nsyms;
            resolve_module(u->module);
        }
    }
    for (int i = 0; i < m->nunits; i++) {
        Unit *u = &m->units[i];
        if (u->kind == 2) {
            check_levels(u->expr, 3);
            int l = expr_level(u->expr);
            if (l) semantic_error(u->where, "Level error: assumptions must be level 0 (Constant), \nbut this one has level %d.", l);
        } else if (u->kind == 4 && u->def->body) check_levels(u->def->body, 3);
        else if (u->kind == 1 || (u->kind == 0 && u->def->kind != D_CONST && u->def->kind != D_VAR)) check_def_levels(u->def);
    }
    if (!m->outer) { print_warnings(m); lint_records(m); }
    m->resolved = 2;
    cur_module = saved;
}

/* Level checking (§5.8). Each parameter of a definition, and each
   declaration of a module, may be used only where its argument or
   substitute may have some level; an operator applied to arguments of
   higher levels than its parameters allow is an error. */

static int level_max(Def *d) { return d->level_max ? d->level_max - 1 : 3; }

/* Argument i of op in e, where its level may be at most cap; e itself may be at most max. */
static void check_argument(Expr *e, const char *op, int i, Expr *a, int cap, int max) {
    if (!a) return;
    if (expr_level(a) > cap)
        semantic_error(e, "Level error in applying operator %s:\nThe level of argument %d exceeds the maximum level allowed by the operator.", op, i + 1);
    check_levels(a, cap < max ? cap : max);
}

/* The operands of e, the first of level at most first, the others at most rest. */
static void check_operands(Expr *e, int first, int rest, int max) {
    for (int i = 0; i < e->n; i++) check_argument(e, S(e->op), i, e->args[i], i ? rest : first, max);
}

/* SANY's name for a built-in operator whose arguments may be at most
   actions; the body of a function constructor or a quantifier may be
   temporal, as their bounds may not. */
static const char *sany_op(Expr *e) {
    switch (e->kind) {
    case K_EQ: return "=";
    case K_NEQ: return "/=";
    case K_IN: return "\\in";
    case K_NOTIN: return "\\notin";
    case K_CUP: return "\\union";
    case K_CAP: return "\\intersect";
    case K_SETMINUS: return "\\";
    case K_SUBSETEQ: return "\\subseteq";
    case K_SUBSET: return "SUBSET";
    case K_UNION: return "UNION";
    case K_DOMAIN: return "DOMAIN";
    case K_TIMES: return "$CartesianProd";
    case X_SETENUM: return "$SetEnumerate";
    case X_TUPLE: return "$Tuple";
    case X_RCDSET: return "$SetOfRcds";
    case X_FCNSET: return "$SetOfFcns";
    case X_APPLY: return "$FcnApply";
    case X_DOT: return "$RcdSelect";
    case X_EXCEPT: return "$Except";
    case X_CHOOSE: return e->bounds[0].set ? "$BoundedChoose" : "$UnboundedChoose";
    case X_FILTER: return "$SubsetOf";
    case X_MAP: return "$SetOfAll";
    case X_FCN: return "$FcnConstructor";
    case X_FORALL: return "$BoundedForall";
    case X_EXISTS: return "$BoundedExists";
    default: return NULL;
    }
}

/* SANY's name for a connective that may not join a temporal formula and an action. */
static const char *sany_connective(int kind) {
    switch (kind) {
    case K_AND: return "\\land";
    case K_OR: return "\\lor";
    case K_IMPLIES: return "=>";
    case K_EQUIV: return "\\equiv";
    default: return NULL;
    }
}

/* Checks e, where its level may be at most max, and records that limit for
   the parameters and declarations it uses. */
static void check_levels(Expr *e, int max) {
    if (!e) return;
    Def *d = e->def;
    switch (e->kind) {
    case K_BOUND: case K_DECL:
        if (max < level_max(d)) d->level_max = max + 1;
        return;
    case K_PRIME: case K_UNCHANGED: check_operands(e, 1, 1, max); return;
    case K_ENABLED: check_operands(e, 2, 2, 2); return;   /* a state predicate of any action */
    case K_CDOT: check_operands(e, 2, 2, max); return;
    case X_SQACT: case X_ANGLEACT: check_operands(e, 2, 1, max); return;   /* [A]_v */
    case X_WF: case X_SF: check_operands(e, 1, 2, max); return;            /* WF_v(A) */
    case K_CALL: case K_INSTCALL:
        check_def_levels(d);
        for (int i = 0; i < e->n; i++)
            check_argument(e, S(d->name), i, e->args[i], i < d->nparams ? level_max(d->params[i]) : 3, max);
        for (int k = 0; e->kind == K_INSTCALL && k < e->ndefs; k++) {
            Def *in = e->defs[k];
            check_def_levels(in);
            for (int i = 0; i < e->segs[k].n && i < in->nparams; i++)
                check_argument(e, S(in->name), i, e->segs[k].args[i], level_max(in->params[i]), max);
        }
        return;
    case X_LET:
        for (int i = 0; i < e->ndefs; i++) check_def_levels(e->defs[i]);
        check_levels(e->args[0], max);
        return;
    case X_LAMBDA: check_def_levels(d); return;
    default: {
        const char *op = sany_op(e), *conn = sany_connective(e->kind);
        int inner = op && max > 2 ? 2 : max;
        for (int i = 0; i < e->nb; i++) {
            Bound *b = &e->bounds[i];
            if (op && b->set && expr_level(b->set) > 2) {
                Expr at = {.mod = e->mod, .l1 = b->line, .c1 = b->col, .l2 = b->line, .c2 = b->col + (int)strlen(S(b->names[0])) - 1};
                semantic_error(e, "Level error in applying operator %s:\nThe level of the range for the bounded variable %s \nexceeds the maximum level allowed by the operator.", op, loc_str(&at));
            }
            check_levels(b->set, inner);
        }
        for (int i = 0; e->kind == X_EXCEPT && i < e->n - 1; i++) {
            Path *p = &e->paths[i];
            Expr at = *e->args[i + 1];   /* the update, from its ! to its value's end */
            at.l1 = p->line;
            at.c1 = p->col;
            for (int k = 0; k < p->n; k++) check_argument(&at, "$Seq", k, p->keys[k], 2, max);
        }
        if (conn) {
            int temporal = 0, action = 0;
            for (int i = 0; i < e->n; i++) { int l = expr_level(e->args[i]); temporal |= l == 3; action |= l == 2; }
            if (temporal && action) semantic_error(e, "%s has both temporal formula and action as arguments.", conn);
        }
        int free = e->kind == X_FCN || e->kind == X_FORALL || e->kind == X_EXISTS;
        for (int i = 0; i < e->n; i++)
            if (op && !free) check_argument(e, op, i, e->args[i], 2, max);
            else check_levels(e->args[i], max);
        return;
    }
    }
}

/* A definition, once: its body, or an instance's substitutions, each of a
   level its declaration allows. */
static void check_def_levels(Def *d) {
    if (d->level_checked) return;
    d->level_checked = 1;
    if (d->kind == D_INST) {
        for (int i = 0; i < d->nsubst; i++) {
            Def *decl = d->subst_decl[i];
            Expr *x = d->subst_expr[i];
            if (expr_level(x) > level_max(decl))
                semantic_error(d->where, "Level error in instantiating module '%s':\nThe level of the expression or operator substituted for '%s' \nmust be at most %d.",
                               S(d->target->name), S(decl->name), level_max(decl));
            check_levels(x, level_max(decl));
        }
        return;
    }
    for (int i = 0; i < d->nb; i++) check_levels(d->bounds[i].set, 3);
    check_levels(d->body, 3);
}

/* The level of an expression (0 constant, 1 state, 2 action, 3 temporal). */

/* A parameter whose uses are given level 4, to find whether the level of
   an argument for it reaches the level of a call. */
static Def *level_probe;

/* Levels as TLC bounds them to decide what to evaluate once: every
   argument of a call counts, used or not. */
static int every_argument;
static Value *n_tlcget(Expr *call, Value **a, Ctx c);
static Value *n_trace(Expr *call, Value **a, Ctx c);
static Value *n_counterexample(Expr *call, Value **a, Ctx c);

static int def_level(Def *d) {
    if (every_argument ? d->level_bound > 0 : d->level >= 0 && (d->local != 2 || d->level_probe == level_probe))
        return every_argument ? d->level_bound - 1 : d->level;
    if (d->level_busy) return 0;
    d->level_busy = 1;
    int l = 0;
    if (d->kind == D_VAR || (every_argument && (d->native == n_tlcget || d->native == n_trace || d->native == n_counterexample)))
        l = 1;   /* the minLevel of TLCGet, Trace and CounterExample */
    else if (d->kind == D_OP || d->kind == D_FCN) {
        if (d->body) l = expr_level(d->body);
        for (int i = 0; i < d->nb; i++) if (d->bounds[i].set) { int b = expr_level(d->bounds[i].set); if (b > l) l = b; }
    } else if (d->kind == D_INST) {
        for (int i = 0; i < d->nsubst; i++)
            if (d->subst_expr[i]->kind != X_OPREF) { int b = expr_level(d->subst_expr[i]); if (b > l) l = b; }
    }
    d->level_busy = 0;
    if (every_argument) d->level_bound = l + 1;
    else if (l < 4) {   /* else the probe reached it */
        d->level = l;
        d->level_probe = level_probe;   /* a LET definition may use the probe */
    }
    return l;
}

static int max_level(Expr **args, int n);

/* The highest level of the substitutions for the declarations e names,
   through the definitions it calls, where e is seen through the n
   INSTANCEs of chain, outermost first: as SANY, an instance's definition
   is of the level of what it uses. */
static unsigned level_walks;   /* subst_level's walks, each marking the definitions it enters */
static int subst_level(Expr *e, Def **chain, int n, unsigned walk) {
    if (!e) return 0;
    Def *in = chain[n - 1];
    int l = 0, k;
    if (e->kind == K_DECL)
        for (int i = 0; i < in->nsubst; i++)
            if (in->subst_decl[i] == e->def) {
                Expr *x = in->subst_expr[i];
                k = n == 1 ? expr_level(x) : subst_level(x, chain, n - 1, ++level_walks);
                if (k > l) l = k;
            }
    if ((e->kind == K_CALL || e->kind == K_INSTCALL || e->kind == X_OPREF) && e->def->level_walk != walk) {
        Def *d = e->def;
        d->level_walk = walk;
        if ((k = subst_level(d->body, chain, n, walk)) > l) l = k;
        for (int i = 0; i < d->nb; i++) if ((k = subst_level(d->bounds[i].set, chain, n, walk)) > l) l = k;
    }
    if (e->kind == K_INSTCALL)
        for (int j = 0; j < e->ndefs; j++)
            for (int i = 0; i < e->defs[j]->nsubst; i++) if ((k = subst_level(e->defs[j]->subst_expr[i], chain, n, walk)) > l) l = k;
    for (int i = 0; i < e->n; i++) if ((k = subst_level(e->args[i], chain, n, walk)) > l) l = k;
    for (int i = 0; i < e->nb; i++) if ((k = subst_level(e->bounds[i].set, chain, n, walk)) > l) l = k;
    if (e->kind == X_EXCEPT)
        for (int i = 0; i < e->n - 1; i++)
            for (int j = 0; j < e->paths[i].n; j++) if ((k = subst_level(e->paths[i].keys[j], chain, n, walk)) > l) l = k;
    if (e->kind == X_LET) for (int i = 0; i < e->ndefs; i++) if ((k = subst_level(e->defs[i]->body, chain, n, walk)) > l) l = k;
    if (e->kind == X_LAMBDA && (k = subst_level(e->def->body, chain, n, walk)) > l) l = k;
    for (int i = 0; i < e->nseg; i++)
        for (int j = 0; j < e->segs[i].n; j++) if ((k = subst_level(e->segs[i].args[j], chain, n, walk)) > l) l = k;
    return l;
}

/* The level of a call of d: an argument counts when its parameter is used
   outside ENABLED, as SANY finds the level parameters of a definition. */
static int args_level(Def *d, Expr **args, int n) {
    if (every_argument) return max_level(args, n);
    if (!d->level_mask && d->body) {
        d->level_mask = ~0u;   /* a recursive call: every argument counts */
        unsigned m = 0;
        Def *outer = level_probe;
        for (int i = 0; i < d->nparams && i < 31; i++) {
            level_probe = d->params[i];
            if (expr_level(d->body) == 4) m |= 1u << i;
        }
        level_probe = outer;
        d->level_mask = 1 | m << 1;
    }
    int l = 0;
    for (int i = 0; i < n; i++)
        if (!d->body || i >= 31 || d->level_mask >> (i + 1) & 1) { int a = expr_level(args[i]); if (a > l) l = a; }
    return l;
}

static int max_level(Expr **args, int n) {
    int l = 0;
    for (int i = 0; i < n; i++) if (args[i]) { int a = expr_level(args[i]); if (a > l) l = a; }
    return l;
}

/* Whether e's level depends on a constant or variable: SANY's
   levelParams are not empty. A prime or a temporal operator fixes the
   level of what it applies to; an operator's argument counts if its
   parameter does. TLC says more about an invariant that is no state
   predicate when they are not empty. */
static Def *param_probe;
static int level_params(Expr *e) {
    if ((e->kind == K_BOUND || e->kind == K_PARAMCALL) && e->def == param_probe) return 1;
    switch (e->kind) {
    case K_DECL: return 1;
    case K_PRIME: case K_UNCHANGED: case X_SQACT: case X_ANGLEACT: case K_ENABLED:
    case K_ALWAYS: case K_EVENTUALLY: case K_LEADSTO: case K_WHILE: case X_WF: case X_SF:
    case X_TFORALL: case X_TEXISTS: case X_LAMBDA: case X_OPREF:
        return 0;
    case K_CALL: case K_INSTCALL: {
        Def *d = e->def;
        if (!d->body) break;
        if (d->level_busy) return 0;
        d->level_busy = 1;
        int found = level_params(d->body);
        Def *outer = param_probe;
        for (int i = 0; i < e->n && i < d->nparams && !found; i++) {
            param_probe = d->params[i];
            found = level_params(d->body) && (param_probe = outer, level_params(e->args[i]));
        }
        param_probe = outer;
        d->level_busy = 0;
        return found;
    }
    }
    for (int i = 0; i < e->n; i++) if (level_params(e->args[i])) return 1;
    for (int i = 0; i < e->nb; i++) if (e->bounds[i].set && level_params(e->bounds[i].set)) return 1;
    if (e->kind == X_EXCEPT)
        for (int i = 0; i < e->n - 1; i++)
            for (int k = 0; k < e->paths[i].n; k++) if (level_params(e->paths[i].keys[k])) return 1;
    return 0;
}

static int expr_level(Expr *e) {
    if ((e->kind == K_BOUND || e->kind == K_PARAMCALL) && level_probe && e->def == level_probe) return 4;
    int l = e->kind == K_CALL || e->kind == K_INSTCALL ? args_level(e->def, e->args, e->n) : max_level(e->args, e->n);
    for (int i = 0; i < e->nb; i++) if (e->bounds[i].set) { int b = expr_level(e->bounds[i].set); if (b > l) l = b; }
    switch (e->kind) {
    case K_DECL: return e->def->kind == D_VAR ? 1 : 0;
    case K_PRIME: case K_UNCHANGED: case X_SQACT: case X_ANGLEACT: case K_CDOT: return l < 2 ? 2 : l;
    case K_ENABLED: return 1;
    case K_ALWAYS: case K_EVENTUALLY: case K_LEADSTO: case X_WF: case X_SF: case K_WHILE:
    case X_TFORALL: case X_TEXISTS:
        return 3;
    case K_CALL: case K_PARAMCALL: {
        int d = def_level(e->def);
        return d > l ? d : l;
    }
    case K_INSTCALL: {
        int d = def_level(e->def);
        int coarse = d;
        for (int i = 0; i < e->ndefs; i++) { int p = def_level(e->defs[i]); if (p > coarse) coarse = p; }
        if (coarse > d) {   /* only the substitutions it uses */
            Def *def = e->def;
            unsigned walk = def->level_walk = ++level_walks;
            int p = subst_level(def->body, e->defs, e->ndefs, walk);
            for (int i = 0; i < def->nb; i++) { int b = subst_level(def->bounds[i].set, e->defs, e->ndefs, walk); if (b > p) p = b; }
            if (p > d) d = p;
        }
        for (int i = 0; i < e->nseg; i++) { int a = max_level(e->segs[i].args, e->segs[i].n); if (a > d) d = a; }
        return d > l ? d : l;
    }
    case X_LET:
        for (int i = 0; i < e->ndefs; i++) { int d = def_level(e->defs[i]); if (d > l) l = d; }
        return l;
    case X_EXCEPT:
        for (int i = 0; i < e->n - 1; i++) { int k = max_level(e->paths[i].keys, e->paths[i].n); if (k > l) l = k; }
        return l;
    case X_LAMBDA: return expr_level(e->def->body);
    case X_OPREF: return def_level(e->def);
    default: return l;
    }
}

/* ---------------------------------------------------------------- evaluator */

static int nvars;
static Def **vars;              /* the state variables, in TLC's order */
static Value **cur_state;       /* the state being read */
static Value **next_state;      /* the next state an action assigns; NULL entries unassigned */
static Value **gen_target;      /* the state being assigned */
static int primed;              /* reading the next state */
static int gen_init;            /* assigning unprimed variables: an initial predicate */
static long state_reads;        /* incremented by each read of a variable */
static long moving_reads;       /* by each read of one that may change: primed, or of the initial state being found */
static Value *at_value;         /* @ in an EXCEPT */
static int keep_lazy;           /* TLC's KeepLazy: evaluating a function to apply it (§6.6) */
static int64_t cur_level;       /* TLCGet("level") */
static int eval_depth;

/* A definition's body is entered: only calls nest without bound. Past
   the bound, TLC's Java stack has overflowed. */
static void deeper(void) {
    if (++eval_depth <= (stack_limit ? stack_limit : 5000)) return;
    eval_depth = 0;
    error_reset();
    buf_puts(&error_message, stack_overflow);
    stackless = 2;
    raise_error();
}

static Value *eval_body(Expr *body, Ctx c) {
    deeper();
    Value *v = eval(body, c);
    eval_depth--;
    return v;
}

static Value *boolean_set;

static Env *mk_binding(Def *d, Value *v, Env *next) {
    Env *b = NEW(Env);
    b->def = d; b->v = v; b->next = next;
    b->perm = arena == &perm_arena;
    return b;
}

/* The variables of bounds, a tuple pattern counting one. */
static int bounds_total(Bound *bs, int nb) {
    int total = 0;
    for (int i = 0; i < nb; i++) total += bs[i].tuple ? 1 : bs[i].n;
    return total;
}

/* The order in which TLC enumerates the domain of a function of several
   bounds, sorted in keys: the first bound varies fastest, so the tuples
   compare from their last part. */
static Value **order_keys;
static int params_cmp(const void *x, const void *y) {
    Value *a = order_keys[*(const int *)x], *b = order_keys[*(const int *)y];
    for (int i = a->n - 1; i >= 0; i--) {
        int c = vcmp(a->u.fcn.vals[i], b->u.fcn.vals[i]);
        if (c) return c;
    }
    return 0;
}

static int *params_order(Value **keys, int n) {
    int *at = NEWN(int, n);
    for (int i = 0; i < n; i++) at[i] = i;
    order_keys = keys;
    qsort(at, (size_t)n, sizeof *at, params_cmp);
    return at;
}


/* The domain of [x \in S, <<y, z>> \in T |-> e]: the bound set, or the
   product of one set per variable (a tuple pattern is one). */
static Value *bounds_domain(Bound *bs, int nb, Ctx c) {
    int total = 0, k = 0;
    for (int i = 0; i < nb; i++) {
        if (!bs[i].set) fail("TLC cannot handle the unbounded quantifier or CHOOSE over %s.", S(bs[i].names[0]));
        total += bs[i].tuple ? 1 : bs[i].n;
    }
    Value *dom = mk_lazy(L_TIMES);
    dom->n = total;
    dom->u.l.names = NEWN(Value *, 2 * total);
    for (int i = 0; i < nb; i++) {
        Value *set = eval(bs[i].set, c);
        for (int j = 0; j < (bs[i].tuple ? 1 : bs[i].n); j++) dom->u.l.names[total + k++] = set;
    }
    return total == 1 ? dom->u.l.names[1] : dom;
}

/* Whether TLC computes a function over a domain bounds_domain made at
   once: if each bound's set is reducible (§6.6). */
static int bounds_reducible(Value *dom, int total) {
    if (total == 1) return reducible(dom);
    for (int k = 0; k < total; k++) if (!reducible(dom->u.l.names[total + k])) return 0;
    return 1;
}

/* Binds the variables of the bounds to the parts of a domain element. */
static Env *bind_key(Bound *bs, int nb, Value *key, Env *env, Expr *where) {
    int total = bounds_total(bs, nb), k = 0;
    for (int i = 0; i < nb; i++) {
        Bound *b = &bs[i];
        for (int j = 0; j < (b->tuple ? 1 : b->n); j++, k++) {
            Value *part = total == 1 ? key : fcn_apply(key, mk_int(k + 1), where);
            if (!b->tuple) { env = mk_binding(b->defs[j], part, env); continue; }
            for (int m = 0; m < b->n; m++) env = mk_binding(b->defs[m], fcn_apply(part, mk_int(m + 1), where), env);
        }
    }
    return env;
}

/* In a simulation a state may hold a lazy value, which outlives the states
   it was made in; it is evaluated in those states, as TLC does. */
static int simulating;

static Value **snapshot(Value **st) {
    return st ? memcpy(NEWN(Value *, nvars), st, sizeof(Value *) * (size_t)nvars) : NULL;
}

/* Copies: the states being generated change as generation goes on. */
static Value ***made_in(void) {
    if (!simulating) return NULL;
    Value ***s = NEWN(Value **, 2);
    s[0] = snapshot(cur_state);
    s[1] = snapshot(next_state);
    return s;
}

/* A function kept as its definition: [x \in S |-> e] (expr) or a
   function definition (def), over an infinite domain or made lazy (§6.6). */
static Value *mk_lambda(Value *dom, Expr *e, Def *d, Ctx c) {
    Value *f = NEW(Value);
    f->kind = V_LAMBDA;
    f->u.l.a = dom;
    f->u.l.expr = e;
    f->u.l.b = at_value;
    f->u.l.binder = d;
    f->u.l.env = c.env;
    f->u.l.inst = c.inst;
    f->keep = keep_lazy || (d && d->self);
    f->perm = arena == &perm_arena;
    f->u.l.made_in = made_in();
    return f;
}

static Expr *fcndef_bind(Def *d, Value *a, Ctx *c, Expr *where);
static int bind_arg(Bound *bs, int nb, Value *dom, Value *a, Env **env, int *argno);
static _Noreturn void lambda_outside(Value *f, Value *a, int why, int argno, Expr *where);

static Value *lambda_body(Value *f, Value *a);

static Value *lambda_apply(Value *f, Value *a) {
    for (int i = f->n - 1; i >= 0; i--)
        if (veq(f->u.l.names[2 * i], a)) return f->u.l.names[2 * i + 1];
    if (!f->u.l.made_in) return lambda_body(f, a);
    Value **cur = cur_state, **next = next_state;
    cur_state = f->u.l.made_in[0];
    next_state = f->u.l.made_in[1];
    Value *v = lambda_body(f, a);
    cur_state = cur;
    next_state = next;
    return v;
}

/* The body of lazy function f, its bound names given a in *c; where is
   the function, when computing states. */
static Expr *lambda_bind(Value *f, Value *a, Ctx *c, Expr *where) {
    *c = (Ctx){f->u.l.env, f->u.l.inst};
    if (f->u.l.binder) return fcndef_bind(f->u.l.binder, a, c, where);
    Expr *e = f->u.l.expr;
    int argno, why = bind_arg(e->bounds, e->nb, f->u.l.a, a, &c->env, &argno);
    if (why) lambda_outside(f, a, why, argno, where);
    return e->args[0];
}

static Value *eval_body(Expr *body, Ctx c);

static Value *lambda_body(Value *f, Value *a) {
    Ctx c;
    Expr *body = lambda_bind(f, a, &c, NULL);
    Value *saved = at_value;
    at_value = f->u.l.b;
    Value *v = eval_body(body, c);
    at_value = saved;
    return v;
}

/* Whether TLC keeps the domain of [x \in dom |-> e] as an interval. */
static int interval_domain(Value *dom, Bound *bs, int nb) {
    return dom->kind == V_INTERVAL && nb == 1 && bs[0].n == 1 && !bs[0].tuple;
}

/* The function a lazy one is, which it becomes in place where the arenas
   allow; one over an infinite domain stays as it is. */
static __attribute__((cold)) Value *realize_lambda(Value *f) {
    if (set_is_infinite(f->u.l.a)) return f;
    Arena *saved = keeping(f->perm);
    Value *dom = enumerate(f->u.l.a);
    Value *g = mk_fcn(dom->n);
    memcpy(g->u.fcn.keys, dom->u.set.elems, sizeof(Value *) * (size_t)dom->n);
    Def *d = f->u.l.binder;
    int params = d ? bounds_total(d->bounds, d->nb) > 1 : bounds_total(f->u.l.expr->bounds, f->u.l.expr->nb) > 1;
    int *at = params ? params_order(g->u.fcn.keys, dom->n) : NULL;
    int keep = keep_lazy;
    keep_lazy = f->keep;
    for (int j = 0; j < dom->n; j++) {
        int i = at ? at[j] : j;
        g->u.fcn.vals[i] = lambda_apply(f, dom->u.set.elems[i]);
    }
    keep_lazy = keep;
    g->made = MADE_LAMBDA;
    g->range = interval_domain(f->u.l.a, d ? d->bounds : f->u.l.expr->bounds, d ? d->nb : f->u.l.expr->nb) && dom->n;
    if (may_keep(f)) { *f = *g; g = f; }
    arena = saved;
    return g;
}

static Env *mk_thunk(Def *d, Expr *e, Ctx c, Env *next) {
    Env *b = NEW(Env);
    b->def = d; b->e = e; b->ctx_env = c.env; b->ctx_inst = c.inst; b->next = next;
    b->perm = arena == &perm_arena;
    return b;
}

static Env *env_find(Env *env, Def *d) {
    for (; env; env = env->next) if (env->def == d) return env;
    return NULL;
}

static int level_in(Expr *e, Ctx c);

/* The level of a parameter op applied to args in c: that of the operator
   or argument it stands for, and of every argument, as TLC levels it
   with its level parameters. */
static int applied_level(Expr *op, Ctx oc, Expr **args, int n, Ctx c) {
    int l = 0;
    for (Env *b; op && (op->kind == K_PARAMCALL || op->kind == K_BOUND) && (b = env_find(oc.env, op->def));) {
        if (b->e) { op = b->e; oc = (Ctx){b->ctx_env, b->ctx_inst}; continue; }
        if (b->v && b->v->kind == V_OPER) l = def_level(b->v->u.op.def);
        op = NULL;
    }
    if (op) l = level_in(op, oc);   /* the expression it stands for: an operator's name, or a value */
    for (int i = 0; i < n; i++) { int a = level_in(args[i], c); if (a > l) l = a; }
    return l;
}

/* e's level in c, where a parameter has its argument's level: TLC levels
   a temporal formula in the context it expands it in (§10.5). */
static int level_in(Expr *e, Ctx c) {
    int l = expr_level(e);
    if (l >= 3 || !c.env) return l;
    if ((e->kind == K_BOUND || e->kind == K_PARAMCALL) && env_find(c.env, e->def)) {
        int a = applied_level(e, c, e->args, e->n, c);
        return a > l ? a : l;
    }
    for (int i = 0; i < e->n; i++) if (e->args[i]) { int a = level_in(e->args[i], c); if (a > l) l = a; }
    for (int i = 0; i < e->nb; i++) if (e->bounds[i].set) { int a = level_in(e->bounds[i].set, c); if (a > l) l = a; }
    return l;
}

/* An argument for parameter d: a thunk, or the value of a bound name that
   already has one that no state changes, as forcing the thunk would give. */
static Env *mk_arg(Def *d, Expr *e, Ctx c, Env *next) {
    if (e->kind == K_BOUND) {
        Env *b = env_find(c.env, e->def);
        if (b && b->v && !b->stateful) return mk_binding(d, b->v, next);
    }
    return mk_thunk(d, e, c, next);
}

/* The value of a binding, evaluated once where that is safe: a value read
   from no state at all, or from the current state by a binding that lives
   no longer than one state's expansion, as the scratch arena does. */
static Value *force(Env *b) {
    if (b->v && !(primed && b->stateful)) return b->v;
    long reads = state_reads, moving = moving_reads;
    Ctx c = {b->ctx_env, b->ctx_inst};
    Arena *saved = keeping(b->perm);
    Value *v = eval(b->e, c);
    if (b->perm == (arena == &perm_arena)) {
        held_by(b);
        if (reads == state_reads) { b->v = v; b->stateful = 0; }
        else if (!b->perm && moving == moving_reads && !primed) { b->v = v; b->stateful = 1; }
    }
    arena = saved;
    return v;
}

static Value *mk_oper(Def *d, Ctx c) {
    Value *v = NEW(Value);
    v->kind = V_OPER;
    v->u.op.def = d;
    v->u.op.env = c.env;
    v->u.op.inst = c.inst;
    return v;
}

/* An integer TLC computes: of 32 bits; of 64 for symbolic checking, as
   its solver's. */
static int64_t check_int(int64_t v, int64_t a, int64_t b, const char *op) {
    if (!symbolic_mode && (v > 2147483647LL || v < -2147483648LL))
        fail_module("Overflow when computing %lld%s%lld", (long long)a, op, (long long)b);
    return v;
}

static __attribute__((cold)) _Noreturn void int_overflow(int64_t x, int64_t y, char op) {
    fail_module("Overflow when computing %lld%c%lld", (long long)x, op, (long long)y);
}

static int64_t int_op(int64_t x, int64_t y, char op) {
    int64_t v;
    int over = op == '+' ? __builtin_add_overflow(x, y, &v) : op == '-' ? __builtin_sub_overflow(x, y, &v) : __builtin_mul_overflow(x, y, &v);
    if (over || (!symbolic_mode && v != (int32_t)v)) int_overflow(x, y, op);
    return v;
}

static int64_t int_arg(Value *v, int which, const char *op) {
    if (v->kind != V_INT)
        fail_module("The %s argument of %s should be an integer, but instead it is:\n%s", which == 1 ? "first" : "second", op, pretty(v));
    return v->u.i;
}

/* The Java class TLC keeps a value in, which its casting errors name. */
static const char *java_class(Value *v) {
    switch (v->kind) {
    case V_BOOL: return "BoolValue";
    case V_INT: return "IntValue";
    case V_STR: return "StringValue";
    case V_MODEL: return "ModelValue";
    case V_TUPLE: return "TupleValue";
    case V_FCN: return v->made == MADE_RECORD ? "RecordValue" : "FcnRcdValue";
    case V_SET: return "SetEnumValue";
    case V_INTERVAL: return "IntervalValue";
    case V_LAMBDA: return "FcnLambdaValue";
    case V_OPER: return v->u.op.table ? "OpRcdValue" : "OpLambdaValue";
    default: break;
    }
    switch (v->lazy) {
    case L_SUBSET: return "SubsetValue";
    case L_FCNSET: return "SetOfFcnsValue";
    case L_RCDSET: return "SetOfRcdsValue";
    case L_FILTER: return "SetPredValue";
    case L_TIMES: return "SetOfTuplesValue";
    case L_UNION: return "UnionValue";
    case L_CUP: return "SetCupValue";
    case L_CAP: return "SetCapValue";
    case L_DIFF: return "SetDiffValue";
    default: return "UserValue";
    }
}

/* An argument of an arithmetic operator, which TLC casts to an integer. */
static int64_t int_cast(Value *v) {
    if (v->kind != V_INT) fail("Cannot cast tlc2.value.impl.%s to tlc2.value.impl.IntValue", java_class(v));
    return v->u.i;
}

static Value *eval_operator_arg(Expr *a, Ctx c);
static Value *apply_oper(Value *op, Value **args, int n, Expr *where);
static Value *call_def(Def *d, Expr **args, int n, Ctx c, Expr *call);
static int enabled(Expr *a, Ctx c);

/* The value of a constant or variable, through the substitutions of the
   instances the context is in (§4.3). */
/* The substitution of instance id for declaration d, -1 if none. An
   instance substitutes each declaration of its module, so the index is
   kept by module. */
static int subst_index(Def *id, Def *d) {
    if (!id->target) return -1;
    if (d->subst_in != id->target) {
        d->subst_in = id->target;
        d->subst_at = -1;
        for (int i = 0; i < id->nsubst; i++) if (id->subst_decl[i] == d) d->subst_at = i;
    }
    return d->subst_at;
}

/* The expression an instance substitutes for d, if any; c becomes the
   context it is in. */
static Expr *substitute(Def *d, Ctx *c) {
    for (Inst *in = c->inst; in; in = in->parent) {
        int i = subst_index(in->def, d);
        if (i >= 0) { *c = (Ctx){in->env, in->parent}; return in->def->subst_expr[i]; }
    }
    return NULL;
}

/* ENABLED marks the instance chain where it is evaluated. As in TLC, a
   variable reached from there is not substituted (§6.9). */
static Def enabled_mark;
static int enabled_slot(Def *d);

/* The value of substitution i of instance in, in the current state:
   kept while the state's values are, as TLC keeps a LazyValue for the
   states it computed it in. Kept in the search, for a substitution of
   state level but a variable. */
static __attribute__((noinline)) Value *substitution_value(Inst *in, int i) {
    Def *id = in->def;
    Expr *x = id->subst_expr[i];
    Ctx outer = {in->env, in->parent};
    if (primed || gen_init || !cur_state || arena != &scratch_arena) return eval(x, outer);
    if (!id->subst_kept) id->subst_kept = xcalloc((size_t)id->nsubst, 1);
    if (!id->subst_kept[i]) id->subst_kept[i] = x->kind != K_DECL && expr_level(x) == 1 ? 1 : 2;
    if (id->subst_kept[i] == 2) return eval(x, outer);
    if (!in->state || in->resets != scratch_resets || memcmp(in->state, cur_state, sizeof(Value *) * (size_t)nvars)) {
        held_by(in);
        in->resets = scratch_resets;
        in->state = NEWN(Value *, nvars);
        memcpy(in->state, cur_state, sizeof(Value *) * (size_t)nvars);
        in->kept = NEWN(Value *, id->nsubst);
    }
    if (in->kept[i]) return in->kept[i];
    Value *v = eval(x, outer);
    held_by(in);
    return in->kept[i] = v;
}

/* The value of d through the substitutions of c's instances, or NULL if
   none substitutes it. */
static Value *decl_value(Def *d, Ctx c, Expr *where);
static __attribute__((noinline)) Value *substituted_value(Def *d, Ctx c, Expr *where) {
    for (Inst *in = c.inst; in; in = in->parent) {
        if (in->def == &enabled_mark) {   /* before a substitution: by name, as ENABLED assigns it (§6.9) */
            if (!primed || d->kind != D_VAR || d->var_index >= 0) continue;
            int slot = enabled_slot(d);
            if (slot < 0 || !next_state[slot])
                fail_runtime(where, MANYAN_ERROR_CONFIG, "In evaluation, the identifier %s is either undefined or not an operator.", S(d->name));
            return next_state[slot];
        }
        int i = subst_index(in->def, d);
        if (i >= 0) {
            Expr *x = in->def->subst_expr[i];
            Ctx outer = {in->env, in->parent};
            if (x->kind == X_OPREF) return x->def->kind == D_CONST ? decl_value(x->def, outer, where) : mk_oper(x->def, outer);
            return d->arity ? eval_operator_arg(x, outer) : substitution_value(in, i);
        }
    }
    return NULL;
}

static Value *decl_value(Def *d, Ctx c, Expr *where) {
    if (c.inst) {
        Value *v = substituted_value(d, c, where);
        if (v) return v;
    }
    if (d->kind == D_VAR) {
        if (d->var_index < 0) fail_at(where, "The variable %s is not a variable of the specification.", S(d->name));
        state_reads++;
        if (primed || (gen_init && cur_state == gen_target)) moving_reads++;
        if (primed) {
            if (!next_state || !next_state[d->var_index])
                fail_runtime(where, MANYAN_ERROR_CONFIG, "In evaluation, the identifier %s is either undefined or not an operator.", S(d->name));
            return next_state[d->var_index];
        }
        if (!cur_state || !cur_state[d->var_index])
            fail_runtime(where, MANYAN_ERROR_CONFIG, "In evaluation, the identifier %s is either undefined or not an operator.", S(d->name));
        return cur_state[d->var_index];
    }
    if (d->replacement) return call_def(d->replacement, NULL, 0, (Ctx){NULL, NULL}, where);
    if (!d->value) fail_at(where, "The constant parameter %s is not assigned a value by the configuration file.", S(d->name));
    return d->value;
}

/* The definition a constant operator stands for, by the substitution of
   an instance the context is in or by the configuration, with the context
   it is in; or NULL. */
static Def *const_operator(Def *d, Ctx c, Ctx *at) {
    for (Inst *in = c.inst; in; in = in->parent) {
        int i = subst_index(in->def, d);
        if (i >= 0) {
            Expr *x = in->def->subst_expr[i];
            *at = (Ctx){in->env, in->parent};
            if (x->kind != X_OPREF) return NULL;
            return x->def->kind == D_CONST ? const_operator(x->def, *at, at) : x->def;
        }
    }
    return d->replacement;
}

/* Bindings of `x \in S, <<a, b>> \in T`: calls fn for each, in TLC's
   order, until it returns nonzero. */
typedef int (*BindFn)(Ctx c, void *data);

/* TLC's error for a quantifier over s: Nat, Int and Seq(S) explain
   themselves after the bound's location. */
static _Noreturn void non_enumerable_bound(Value *s, Expr *bound) {
    const char *infinite = s->kind != V_LAZY ? NULL : s->lazy == L_NAT ? "Nat" : s->lazy == L_INT ? "Int" : NULL;
    if (!infinite && !(s->kind == V_LAZY && s->lazy == L_SEQ))
        fail_at(bound, "TLC encountered a non-enumerable quantifier bound\n%s.", pretty(s));
    Buf b = {0};
    const char *v = pretty(s);
    buf_printf(&b, "TLC encountered the non-enumerable quantifier bound\n%s", v);
    loc_line(&b, bound);
    if (infinite)
        buf_printf(&b, "\nThe set %s contains infinitely many elements. As a result, TLC cannot evaluate expressions that\n"
                   "universally (\\A) or existentially (\\E) quantify over %s, because this would require checking an\n"
                   "infinite number of cases. Note that TLC handles set membership like T \\subseteq %s for any finite set T.",
                   infinite, v, infinite);
    else
        buf_printf(&b, "\nIn TLA+, Seq(S) represents the set of all finite sequences whose elements come from the set S. Even when S\n"
                   "is a finite set, the number of possible sequences in Seq(S) is unbounded because sequences can have any\n"
                   "finite length (e.g., length 0, 1, 2, and so on). As a result, TLC cannot evaluate expressions that\n"
                   "universally (\\A) or existentially (\\E) quantify over %s, because this would require checking an\n"
                   "infinite number of cases. Note that for a finite set of sequences s, TLC handles s \\subseteq Seq(S).\n"
                   "See https://explain.tlapl.us/seq-unenumerable for additional details.", v);
    fail("%s", buf_take(&b));
}

/* The set a bound ranges over, enumerated. */
static Value *bound_value(Bound *b, Ctx c) {
    if (!b->set) fail("TLC cannot handle the unbounded quantifier or CHOOSE over %s.", S(b->names[0]));
    Value *s = eval(b->set, c);
    if (!is_set(s) || user_set(s)) non_enumerable_bound(s, b->set);
    return s;
}

static Value *bound_set(Bound *b, Ctx c) { return enumerate(bound_value(b, c)); }

/* As TLC, the sets are enumerated first, and the first variable varies
   fastest. */
static int for_bindings(Bound *bs, int nb, Ctx c, BindFn fn, void *data) {
    if (nb == 1 && bs[0].n == 1 && !bs[0].tuple) {
        /* x \in S, the common case; an interval, as TLC, one by one, once
           TLC has its size. */
        Value *s = bound_value(&bs[0], c);
        if (s->kind == V_INTERVAL) {
            interval_size(s);
            for (int64_t x = s->u.range.lo; x <= s->u.range.hi; x++)
                if (fn((Ctx){mk_binding(bs[0].defs[0], mk_int(x), c.env), c.inst}, data)) return 1;
            return 0;
        }
        s = enumerate(s);
        for (int i = 0; i < s->n; i++)
            if (fn((Ctx){mk_binding(bs[0].defs[0], s->u.set.elems[i], c.env), c.inst}, data)) return 1;
        return 0;
    }
    int total = bounds_total(bs, nb);
    if (total == 0) return fn(c, data);
    Bound **owner = NEWN(Bound *, total);
    Value **sets = NEWN(Value *, total);
    int *slot = NEWN(int, total), *index = NEWN(int, total);
    int k = 0;
    for (int i = 0; i < nb; i++) {
        Value *s = bound_set(&bs[i], c);
        for (int j = 0; j < (bs[i].tuple ? 1 : bs[i].n); j++) {
            owner[k] = &bs[i]; slot[k] = j; sets[k] = s; index[k] = 0;
            if (!s->n) return 0;
            k++;
        }
    }
    for (;;) {
        Env *env = c.env;
        for (k = 0; k < total; k++) {
            Bound *b = owner[k];
            Value *v = sets[k]->u.set.elems[index[k]];
            if (!b->tuple) { env = mk_binding(b->defs[slot[k]], v, env); continue; }
            if (!is_fcn(v) || !fcn_is_tuple(v) || v->n != b->n)
                fail("Argument mismatch in operator application.%%1");   /* sic: TLC's message leaves its parameter out */
            for (int j = 0; j < b->n; j++) env = mk_binding(b->defs[j], v->u.fcn.vals[j], env);
        }
        if (fn((Ctx){env, c.inst}, data)) return 1;
        for (k = 0; k < total && ++index[k] == sets[k]->n; k++) index[k] = 0;
        if (k == total) return 0;
    }
}

typedef struct { Expr *body; int value; Expr *where; } QuantData;

/* v, the body of the quantifier or CHOOSE e: TLC's error unless boolean. */
static int expected_bool(Value *v, Expr *e) {
    if (v->kind != V_BOOL) {
        fail("TLC expected a boolean value, but did not find one. %s", node_str(e));
    }
    return (int)v->u.i;
}

/* The body of quantifier q in c, dropping what computing it made where
   that is allowed. */
static int quant_holds(QuantData *q, Ctx c) {
    Region *r = region_open();
    int holds = expected_bool(eval(q->body, c), q->where);
    region_close(r);
    return holds;
}

static int forall_fn(Ctx c, void *data) {
    QuantData *q = data;
    if (!quant_holds(q, c)) { q->value = 0; return 1; }
    return 0;
}

static int exists_fn(Ctx c, void *data) {
    QuantData *q = data;
    if (quant_holds(q, c)) { q->value = 1; return 1; }
    return 0;
}

typedef struct { Expr *body; List out; } MapData;

static int map_fn(Ctx c, void *data) {
    MapData *d = data;
    list_add(&d->out, eval(d->body, c));
    return 0;
}

/* Whether v satisfies the predicate of a lazy filter. */
static Value *filter_member_test(Value *s, Value *v) {
    Expr *e = s->u.l.expr;
    Bound *b = &e->bounds[0];
    Env *env = s->u.l.env;
    if (b->tuple) {
        if (!is_fcn(v) || v->n != b->n) return FALSEV;
        for (int j = 0; j < b->n; j++) env = mk_binding(b->defs[j], v->u.fcn.vals[j], env);
    } else {
        env = mk_binding(b->defs[0], v, env);
    }
    Ctx c = {env, s->u.l.inst};
    Value **cur = cur_state, **next = next_state;
    if (s->u.l.made_in) cur_state = s->u.l.made_in[0], next_state = s->u.l.made_in[1];
    Region *r = region_open();
    Value *holds = eval(e->args[0], c);
    if (holds->kind != V_BOOL)
        fail_at(e->args[0], "Attempted to evaluate an expression of form {x \\in S : P(x)} when P was %s.", kind_string(holds));
    region_close(r);
    cur_state = cur;
    next_state = next;
    return holds;
}

/* A function definition f[x \in S] == e: its body, x given a in *c. */
static Expr *fcndef_bind(Def *d, Value *a, Ctx *c, Expr *where) {
    Env *env = NULL;
    if (d->local == 2) {
        Env *b = env_find(c->env, d);
        env = b ? b->ctx_env : c->env;
    }
    Value *dom = bounds_domain(d->bounds, d->nb, (Ctx){env, c->inst});
    int argno, why = bind_arg(d->bounds, d->nb, dom, a, &env, &argno);
    if (why) lambda_outside(mk_lambda(dom, NULL, d, *c), a, why, argno, where);
    c->env = env;
    return d->body;
}

/* The value of function definition d at a. */
static Value *fcndef_apply(Def *d, Value *a, Ctx c) {
    Expr *body = fcndef_bind(d, a, &c, NULL);
    return eval_body(body, c);
}

/* [x \in S |-> e], or the function definition d, computed in full over
   dom; an error meanwhile is one TLC cannot fingerprint at `where`. */
static Value *fcn_in_full(Value *dom, Expr *e, Def *d, Ctx c, Expr *where) {
    fp_enter(where);
    int range = interval_domain(dom, d ? d->bounds : e->bounds, d ? d->nb : e->nb);
    dom = enumerate(dom);
    Value *f = mk_fcn(dom->n);
    memcpy(f->u.fcn.keys, dom->u.set.elems, sizeof(Value *) * (size_t)dom->n);
    int params = d ? bounds_total(d->bounds, d->nb) > 1 : bounds_total(e->bounds, e->nb) > 1;
    int *at = params ? params_order(f->u.fcn.keys, dom->n) : NULL;
    for (int j = 0; j < dom->n; j++) {
        int i = at ? at[j] : j;
        Value *k = dom->u.set.elems[i];
        f->u.fcn.vals[i] = d ? fcndef_apply(d, k, c)
                             : eval(e->args[0], (Ctx){bind_key(e->bounds, e->nb, k, c.env, e), c.inst});
    }
    fp_leave(where);
    if (!d) f->made = MADE_LAMBDA;
    f->range = range && dom->n;
    return f;
}

static Value *fcndef_value(Def *d, Ctx c) {
    int n = nframes;
    if (tracking) frame_push(d->where);   /* TLC evaluates the definition's constructor */
    Value *dom = bounds_domain(d->bounds, d->nb, c), *v;
    if (d->self || keep_lazy || !bounds_reducible(dom, bounds_total(d->bounds, d->nb))) v = mk_lambda(dom, NULL, d, c);
    else v = fcn_in_full(dom, NULL, d, c, d->where);
    nframes = n;
    return v;
}

static int nowarning;   /* TLC's warnings off (-nowarning) */
static int keep_going;   /* -continue: a violated invariant or action property is reported, and the search goes on */
static int te_spec;      /* TLC sets up a trace exploration spec: not with -continue or -noGenerateSpecTE */

/* Prints one of TLC's warnings; as TLC, the first of a run says how to
   turn them off. */
static int warned;
static void warning(const char *text) {
    if (nowarning) return;
    printf("Warning: %s\n", text);
    if (!warned++) printf("(Use the -nowarning option to disable this warning.)\n");
    fflush(stdout);
}

/* TLC's warning that an EXCEPT names a key outside the domain, each
   message once: the first, with the -nowarning line, is another. */
static void warn_except(Expr *e) {
    static char **seen;
    static int nseen;
    if (nowarning) return;
    if (in_worker) worker_cannot();   /* the search prints in order */
    Buf b = {0};
    buf_puts(&b, warned ? "+" : "-");
    buf_puts(&b, "The EXCEPT was applied to non-existing fields of the value at\n");
    loc_text(&b, e);
    for (int i = 0; i < nseen; i++)
        if (!strcmp(seen[i], b.s)) { free(b.s); return; }
    seen = xrealloc(seen, sizeof(char *) * (size_t)(nseen + 1));
    seen[nseen++] = b.s;
    warning(b.s + 1);
}

static Value *except_update(Value *f, Path *p, int i, Expr *val, Ctx c, Expr *where) {
    Value *key = p->fields[i] >= 0 ? mk_str(p->fields[i]) : eval(p->keys[i], c);
    if (!is_fcn(f) && f->kind != V_LAMBDA)
        fail("Attempted to apply EXCEPT construct to the value %s.", pretty(f));
    if (f->kind == V_TUPLE && key->kind != V_INT) fail("Attempted to access tuple at a non integral index: %s", pretty(key));
    if (f->kind == V_FCN && f->made == MADE_RECORD && key->kind != V_STR) fail("Attempted to access record by a non-string argument: %s", pretty(key));
    int k = f->kind == V_LAMBDA ? -1 : fcn_index(f, key);
    if (f->kind != V_LAMBDA && k < 0) { warn_except(where->args[0]); return f; }
    Value *old = k >= 0 ? f->u.fcn.vals[k] : fcn_apply(f, key, where);
    Value *nv;
    if (i + 1 < p->n) {
        nv = except_update(old, p, i + 1, val, c, where);
    } else {
        Value *saved = at_value;
        at_value = old;
        nv = eval(val, c);
        at_value = saved;
    }
    return fcn_update(f, k, key, nv);
}

static int eval_bool(Expr *e, Ctx c) {
    Value *v = eval(e, c);
    if (v->kind != V_BOOL)
        fail_at(e, "A non-boolean expression (%s) was used as a condition.", kind_name(v));
    return (int)v->u.i;
}

static const char *article_kind(Value *v) {
    switch (v->kind) {
    case V_INT: return "an integer";
    case V_STR: return "a string";
    case V_MODEL: return "a model value";
    case V_TUPLE: case V_FCN: return "a function";
    default: return is_set(v) ? "a set" : "a value";
    }
}

static Value *junction(Expr *e, Ctx c, int and) {
    for (int i = 0; i < e->n; i++) {
        Value *v = eval(e->args[i], c);
        if (v->kind != V_BOOL)
            fail_at(e, "Attempted to evaluate an expression of form %s when %s was\n%s.",
                    and ? "P /\\ Q" : "P \\/ Q", i == 0 ? "P" : "Q", article_kind(v));
        if (v->u.i != and) return v;
    }
    return BOOLV(and);
}

/* The instances an instance call goes through, each with its parameters. */
static Inst *instance_chain(Expr *e, Ctx c) {
    if (e->inst) return e->inst;
    int fixed = !c.inst;
    for (int i = 0; i < e->ndefs; i++) fixed &= !e->defs[i]->nparams && e->defs[i]->local != 2;
    Arena *saved = arena;
    if (fixed) arena = &perm_arena;
    Inst *inst = c.inst;
    for (int i = 0; i < e->ndefs; i++) {
        Def *id = e->defs[i];
        Env *env = NULL;
        Seg *s = &e->segs[i];
        for (int k = 0; k < id->nparams && k < s->n; k++) env = mk_thunk(id->params[k], s->args[k], c, env);
        if (id->local == 2) { Env *b = env_find(c.env, id); if (b) env = b->ctx_env; }
        Inst *in = NEW(Inst);
        in->def = id;
        in->env = env;
        in->parent = inst;
        inst = in;
    }
    if (fixed) e->inst = inst, arena = saved;
    return inst;
}



static __attribute__((noinline)) Value *ev_bound(Expr *e, Ctx c) {
    Env *b = env_find(c.env, e->def);
    if (!b) fail_runtime(e, MANYAN_ERROR_CONFIG, "In evaluation, the identifier %s is either undefined or not an operator.", S(e->def->name));
    return force(b);
}

/* The arguments of a call of a standard module's common operators, which
   take values only: evaluated in c, with no arena for them. */
static int plain_args(Def *d, Expr *e, Ctx c, Value **vals) {
    if (!d->native || d->lazy || e->n > 4 || e->n != d->nparams) return 0;
    for (int i = 0; i < e->n; i++) if (d->params[i]->arity) return 0;
    for (int i = 0; i < e->n; i++) vals[i] = eval(e->args[i], c);
    return 1;
}

/* x op y of Naturals' operators on two integers, computed here; any other
   arguments, or an overflow, by the native, which reports it. */
static Value *int_call(Def *d, Expr *e, Ctx c) {
    Value *vals[2] = {eval(e->args[0], c), eval(e->args[1], c)};
    if (vals[0]->kind == V_INT && vals[1]->kind == V_INT) {
        int64_t x = vals[0]->u.i, y = vals[1]->u.i, v;
        switch (d->intop) {
        case '<': return BOOLV(x < y);
        case 'l': return BOOLV(x <= y);
        case '>': return BOOLV(x > y);
        case 'g': return BOOLV(x >= y);
        case '+': if (!__builtin_add_overflow(x, y, &v) && (symbolic_mode || v == (int32_t)v)) return mk_int(v); break;
        case '-': if (!__builtin_sub_overflow(x, y, &v) && (symbolic_mode || v == (int32_t)v)) return mk_int(v); break;
        case '*': if (!__builtin_mul_overflow(x, y, &v) && (symbolic_mode || v == (int32_t)v)) return mk_int(v); break;
        }
    }
    return call_native(d, e, vals, c);
}

static __attribute__((noinline)) Value *ev_call(Expr *e, Ctx c) {
    Def *d = e->def;
    if (d->kind == D_VAR && !d->replacement) return decl_value(d, c, e);
    if (d->intop && e->n == 2 && !d->replacement) return int_call(d, e, c);
    Value *vals[4];
    if (!d->replacement && plain_args(d, e, c, vals)) return call_native(d, e, vals, c);
    return call_def(d, e->args, e->n, c, e);
}

static __attribute__((noinline)) Value *ev_instcall(Expr *e, Ctx c) {
    Def *d = e->def;
    if (d->replacement) return call_def(d, e->args, e->n, c, e);   /* by the configuration, an operator of the root module */
    Inst *inst = instance_chain(e, c);
    Ctx ic = {c.env, inst};
    if (d->kind == D_CONST || d->kind == D_VAR) return decl_value(d, ic, e);
    if (d->lazy) {
        Value *v = call_native(d, e, NULL, c);
        if (v) return v;   /* NULL: as TLC's evaluation methods, it leaves this call to the definition */
    }
    if (e->n == 0) { Ctx bare = {NULL, inst}; return call_def(d, NULL, 0, bare, e); }
    /* The arguments are evaluated in the caller's context. */
    Value *few[4], **vals = e->n <= 4 ? few : NEWN(Value *, e->n);
    if (plain_args(d, e, c, vals)) return call_native(d, e, vals, ic);
    Env *env = NULL;
    for (int k = 0; k < e->n && k < d->nparams; k++) {
        if (d->params[k]->arity) env = mk_binding(d->params[k], eval_operator_arg(e->args[k], c), env);
        else env = mk_thunk(d->params[k], e->args[k], c, env);
    }
    if (d->native && !d->lazy) {
        for (int k = 0; k < e->n; k++) vals[k] = force(env_find(env, d->params[k]));
        return call_native(d, e, vals, ic);
    }
    Ctx body = {env, inst};
    return eval_body(d->body, body);
}

static __attribute__((noinline)) Value *ev_paramcall(Expr *e, Ctx c) {
    Value *op;
    if (e->def->kind == D_PARAM) {
        Env *b = env_find(c.env, e->def);
        if (!b) fail_at(e, "Unbound operator parameter %s.", S(e->def->name));
        op = force(b);
    } else {
        op = decl_value(e->def, c, e);
    }
    if (op->kind != V_OPER) return op;   /* as TLC, a value applied is the value */
    Def *d = op->u.op.def->replacement ? op->u.op.def->replacement : op->u.op.def;
    if (d->kind == D_OP && !d->native && d->nparams == e->n) {   /* as TLC, a definition takes its arguments lazily */
        Ctx oc = {op->u.op.env, op->u.op.inst};
        Env *b = d->local == 2 ? env_find(oc.env, d) : NULL;
        Env *env = b ? b->ctx_env : oc.env;
        for (int i = 0; i < e->n; i++)
            env = d->params[i]->arity ? mk_binding(d->params[i], eval_operator_arg(e->args[i], c), env)
                                      : mk_arg(d->params[i], e->args[i], c, env);
        return eval_body(d->body, (Ctx){env, oc.inst});
    }
    Value **vals = NEWN(Value *, e->n);
    for (int i = 0; i < e->n; i++) vals[i] = eval(e->args[i], c);
    return apply_oper(op, vals, e->n, e);
}

static __attribute__((noinline)) Value *ev_not(Expr *e, Ctx c) {
    Value *v = eval(e->args[0], c);
    if (v->kind != V_BOOL) fail_at(e, "Attempted to apply the operator ~ to a non-boolean\n(%s)", kind_string(v));
    return BOOLV(!v->u.i);
}

static __attribute__((noinline)) Value *ev_implies(Expr *e, Ctx c) {
    Value *a = eval(e->args[0], c);
    if (a->kind != V_BOOL) fail_at(e, "Attempted to evaluate an expression of form P => Q when P was\n%s.", article_kind(a));
    if (!a->u.i) return TRUEV;
    Value *b = eval(e->args[1], c);
    if (b->kind != V_BOOL) fail_at(e, "Attempted to evaluate an expression of form P => Q when Q was\n%s.", article_kind(b));
    return b;
}

static __attribute__((noinline)) Value *ev_equiv(Expr *e, Ctx c) {
    Value *a = eval(e->args[0], c), *b = eval(e->args[1], c);
    if (a->kind != V_BOOL || b->kind != V_BOOL) fail_at(e, "Attempted to evaluate an expression of form P <=> Q when P or Q was not a boolean.");
    return BOOLV(a->u.i == b->u.i);
}

/* The left side first, as TLC: C leaves the order of arguments open. */
static __attribute__((noinline)) Value *ev_eq(Expr *e, Ctx c) {
    Value *a = eval(e->args[0], c), *b = eval(e->args[1], c);
    return BOOLV(veq(a, b));
}

static __attribute__((noinline)) Value *ev_neq(Expr *e, Ctx c) {
    Value *a = eval(e->args[0], c), *b = eval(e->args[1], c);
    return BOOLV(!veq(a, b));
}

/* <<x1, ..., xn>> \in s, the xi atoms and s enumerated, by set_member's
   probes without making the tuple; -1 if a probe is not of a tuple of atoms
   of the same kinds, which vcmp compares. */
static int tuple_member(Value **xs, int n, Value *s) {
    int lo = 0, hi = s->n;
    while (lo < hi) {
        int mid = (lo + hi) >> 1, c = 0;
        Value *t = s->u.set.elems[mid];
        if (t->kind != V_TUPLE || t->n != n) return -1;
        for (int i = 0; i < n && !c; i++) {
            Value *y = t->u.fcn.vals[i];
            if (y->kind != xs[i]->kind) return -1;
            c = (xs[i]->u.i > y->u.i) - (xs[i]->u.i < y->u.i);
        }
        if (!c) return 1;
        if (c < 0) hi = mid; else lo = mid + 1;
    }
    return 0;
}

static __attribute__((noinline)) Value *ev_in(Expr *e, Ctx c) {
    Expr *x = e->args[0];
    Value *v, *s, *xs[4];
    int in = -1;
    if (x->kind == X_TUPLE && x->n <= 4) {
        int atoms = 1;
        for (int i = 0; i < x->n; i++) atoms &= (xs[i] = eval(x->args[i], c))->kind <= V_MODEL;
        s = eval(e->args[1], c);
        if (atoms && s->kind == V_SET && !s->u.set.product && !(s->n && s->u.set.elems[0]->kind == V_MODEL))
            in = tuple_member(xs, x->n, s);
        if (in < 0) {
            v = mk_tuple(x->n);
            for (int i = 0; i < x->n; i++) v->u.fcn.vals[i] = xs[i];
            v->u.fcn.source = source(x);
        }
    } else {
        v = eval(x, c);
        s = eval(e->args[1], c);
    }
    if (in < 0) in = set_member(v, s);
    return BOOLV(e->kind == K_IN ? in : !in);
}

static __attribute__((noinline)) Value *ev_cup(Expr *e, Ctx c) {
    Value *a = eval(e->args[0], c), *b = eval(e->args[1], c);
    if (e->kind == K_SUBSETEQ) {
        if (!is_set(a) || user_set(a)) fail_at(e, "Attempted to evaluate an expression of form S \\subseteq T, but S was not enumerable.");
        return BOOLV(subseteq(a, b));
    }
    Value *r = e->kind == K_CUP ? set_union(a, b) : e->kind == K_CAP ? set_inter(a, b) : set_minus(a, b);
    if (r != a && r != b && r->kind == V_LAZY && r->lazy >= L_CUP) r->u.l.expr = source(e);
    return r;
}

static Value *subset_of(Expr *e, Ctx c) {
    Value *s = mk_lazy(L_SUBSET);
    s->u.l.expr = source(e);
    s->u.l.a = eval(e->args[0], c);
    if (!is_set(s->u.l.a)) fail_at(e, "Attempted to compute SUBSET of the non-set:\n%s", pretty(s->u.l.a));
    return s;
}

static __attribute__((noinline)) Value *ev_union(Expr *e, Ctx c) {
    Expr *x = e->args[0];
    Value *s;
    int hold = 0;   /* TLC combines only sets of their elements; it keeps another UNION as it is */
    if (x->kind == X_SETENUM) {
        /* TLC sorts a set's elements only once it must, as Nat and {-1}
           cannot be: UNION {{-1}, Nat} is a set. */
        if (tracking && !x->made) frame_push(x);   /* TLC evaluates the set */
        s = mk_set(x->n);
        for (int i = 0; i < x->n; i++) s->u.set.elems[i] = eval(x->args[i], c);
        s->u.set.source = source(x);
    } else {
        s = eval(x, c);
        hold = s->kind != V_SET || s->made == MADE_HELD;
        s = enumerate(s);
    }
    for (int i = 0; i < s->n; i++) hold |= s->u.set.elems[i]->kind != V_SET || s->u.set.elems[i]->made == MADE_HELD;
    if (hold) {
        Value *u = mk_lazy(L_UNION);
        u->u.l.a = s;
        u->u.l.expr = source(e);
        u->n = x->kind == X_SETENUM;   /* its sets, to be sorted */
        return u;
    }
    if (x->kind == X_SETENUM) s = set_normalize(s);
    List l = {0};
    for (int i = 0; i < s->n; i++)
        for (int j = 0; j < s->u.set.elems[i]->n; j++) list_add(&l, s->u.set.elems[i]->u.set.elems[j]);
    return list_set(&l);
}

static __attribute__((noinline)) Value *ev_domain(Expr *e, Ctx c) {
    Value *f = eval(e->args[0], c);
    if (!is_fcn(f) && f->kind != V_LAMBDA) fail_at(e, "Attempted to apply the operator DOMAIN to a non-function\n(%s)", kind_string(f));
    return fcn_domain(f);
}

static __attribute__((noinline)) Value *ev_prime(Expr *e, Ctx c) {
    if (primed) return eval(e->args[0], c);
    primed = 1;
    Value *v = eval(e->args[0], c);
    primed = 0;
    return v;
}

/* Whether e' = e. */
static int kept(Expr *e, Ctx c) {
    Value *now = eval(e, c);
    int saved = primed;
    primed = 1;
    Value *then = eval(e, c);
    primed = saved;
    return veq(now, then);
}

static __attribute__((noinline)) Value *ev_unchanged(Expr *e, Ctx c) { return BOOLV(kept(e->args[0], c)); }

/* Whether e has one value wherever it is evaluated outside an instance:
   it is made of literals, constants, constant definitions and the
   operators of the arithmetic, sequence and set modules. */
static int fixed_expr(Expr *e) {
    if (e->fixed) return e->fixed == 1;
    Def *d = e->def && e->def->replacement ? e->def->replacement : e->def;
    int f = 0;
    switch (e->kind) {
    case X_NUM: case X_STR: case X_BOOL: f = 1; break;
    case K_DECL: f = d->kind == D_CONST; break;
    case X_SETENUM: case X_TUPLE: case K_TIMES: case K_SUBSET: case X_FCNSET: case X_RCDSET: f = 1; break;
    case K_CALL:
        if (d->native) {
            const char *m = S(d->mod->name);
            f = !strcmp(m, "Naturals") || !strcmp(m, "Integers") || !strcmp(m, "Sequences") || !strcmp(m, "FiniteSets");
        } else {
            f = d->kind == D_OP && !d->nparams && d->local != 2 && d->cache;
        }
        break;
    }
    for (int i = 0; i < e->n && f; i++) f = fixed_expr(e->args[i]);
    e->fixed = f ? 1 : 2;
    return f;
}

/* The set make makes of e: in the search, where e is fixed, once, in the
   permanent arena, naming e as its source as a set made anew would. */
static Value *ev_fixed(Expr *e, Ctx c, Value *(*make)(Expr *, Ctx)) {
    static int fixing;   /* making a fixed set, whose fixed parts are made so too */
    if (c.inst) return make(e, c);
    if (e->value) return e->value;   /* replaying too, in the permanent arena */
    if ((arena != &scratch_arena && !fixing) || !fixed_expr(e)) return make(e, c);
    Arena *saved = arena;
    int was = fixing;
    sigjmp_buf *outer = handler, here;
    handler = &here;
    if (sigsetjmp(here, 0)) { handler = outer; arena = saved; fixing = was; raise_error(); }
    arena = &perm_arena;
    fixing = 1;
    Value *t = make(e, c);
    (t->kind == V_LAZY ? t : t->u.set.product)->u.l.expr = e;
    handler = outer;
    arena = saved;
    fixing = was;
    return e->value = t;
}

static Value *product(Expr *e, Ctx c);
static Value *rcdset_of(Expr *e, Ctx c);
static Value *fcnset_of(Expr *e, Ctx c);

static __attribute__((noinline)) Value *ev_times(Expr *e, Ctx c) { return ev_fixed(e, c, product); }
static __attribute__((noinline)) Value *ev_subset(Expr *e, Ctx c) { return ev_fixed(e, c, subset_of); }
static __attribute__((noinline)) Value *ev_rcdset(Expr *e, Ctx c) { return ev_fixed(e, c, rcdset_of); }
static __attribute__((noinline)) Value *ev_fcnset(Expr *e, Ctx c) { return ev_fixed(e, c, fcnset_of); }

static Value *product(Expr *e, Ctx c) {
    Value *s = mk_lazy(L_TIMES);
    s->u.l.expr = source(e);
    s->n = e->n;
    s->u.l.names = NEWN(Value *, 2 * e->n);
    for (int i = 0; i < e->n; i++) {
        Value *a = eval(e->args[i], c);
        if (!is_set(a)) fail_at(e, "Attempted to compute the cartesian product with the non-set:\n%s", pretty(a));
        s->u.l.names[e->n + i] = a;
    }
    fp_enter(s->u.l.expr);   /* sizing its parts, as TLC enumerating it */
    int expand = expandable(s);
    fp_leave(s->u.l.expr);
    if (!expand) return s;
    Value *t = held(enumerate(s));
    t->u.set.product = s;   /* as TLC, RandomElement draws each part */
    return t;
}

static __attribute__((noinline)) Value *ev_setenum(Expr *e, Ctx c) {
    if (e->value) return e->value;
    int literal = e->n > 0;
    for (int i = 0; i < e->n && literal; i++)
        literal = e->args[i]->kind == e->args[0]->kind && (e->args[i]->kind == X_STR || e->args[i]->kind == X_NUM);
    if (literal) {   /* its elements compare without error */
        Arena *saved = arena;
        arena = &perm_arena;
        List l = {0};
        for (int i = 0; i < e->n; i++) list_add(&l, eval(e->args[i], c));
        e->value = list_set(&l);
        e->value->u.set.source = e;
        arena = saved;
        return e->value;
    }
    List l = {0};
    for (int i = 0; i < e->n; i++) list_add(&l, eval(e->args[i], c));
    fp_enter(e);   /* comparing its elements */
    Value *s = list_set(&l);
    fp_leave(e);
    s->u.set.source = source(e);
    return s;
}

static __attribute__((noinline)) Value *ev_tuple(Expr *e, Ctx c) {
    Value *t = mk_tuple(e->n);
    for (int i = 0; i < e->n; i++) t->u.fcn.vals[i] = eval(e->args[i], c);
    t->u.fcn.source = source(e);
    return t;
}

static __attribute__((noinline)) Value *ev_record(Expr *e, Ctx c) {
    List keys = {0}, vals = {0};
    for (int i = 0; i < e->n; i++) { list_add(&keys, mk_str(e->segs[i].name)); list_add(&vals, eval(e->args[i], c)); }
    Value *r = mk_fcn_from(&keys, &vals);
    r->made = MADE_RECORD;
    r->u.fcn.source = source(e);
    return r;
}

static Value *rcdset_of(Expr *e, Ctx c) {
    List keys = {0}, vals = {0};
    for (int i = 0; i < e->n; i++) {
        Value *s = eval(e->args[i], c);
        if (!is_set(s)) fail_at(e, "Attempted to construct a set of records with the non-set:\n%s", pretty(s));
        list_add(&keys, mk_str(e->segs[i].name));
        list_add(&vals, s);
    }
    Value *r = mk_fcn_from(&keys, &vals);
    Value *s = mk_lazy(L_RCDSET);
    s->u.l.expr = source(e);
    s->n = e->n;
    s->u.l.names = NEWN(Value *, 2 * e->n);
    for (int i = 0; i < e->n; i++) { s->u.l.names[i] = r->u.fcn.keys[i]; s->u.l.names[e->n + i] = r->u.fcn.vals[i]; }
    return s;
}

static Value *fcnset_of(Expr *e, Ctx c) {
    Value *s = mk_lazy(L_FCNSET);
    s->u.l.expr = source(e);
    s->u.l.a = eval(e->args[0], c);
    s->u.l.b = eval(e->args[1], c);
    if (!is_set(s->u.l.a) || !is_set(s->u.l.b)) fail_at(e, "Attempted to construct a set of functions with a non-set.");
    return s;
}

static __attribute__((noinline)) Value *ev_fcn(Expr *e, Ctx c) {
    Value *dom = bounds_domain(e->bounds, e->nb, c);
    if (keep_lazy || !bounds_reducible(dom, bounds_total(e->bounds, e->nb))) return mk_lambda(dom, e, NULL, c);
    return fcn_in_full(dom, e, NULL, c, e);
}

/* The function f[a] applies, evaluated lazily if lazy, and its argument
   *key; NULL for a function definition, applied without its value. in
   names what TLC is computing, for its message, NULL in an expression. */
static Value *apply_parts(Expr *e, Ctx c, int lazy, const char *in, Value **key) {
    Expr *fe = e->args[0];
    Value *f = NULL;
    if (fe->kind == K_DECL && fe->def->kind == D_VAR && !c.inst) f = decl_value(fe->def, c, fe);   /* a variable: no laziness to keep */
    else if (!(lazy && fe->kind == K_CALL && fe->def->kind == D_FCN && !fe->def->replacement && !fe->def->cache)) {
        int keep = keep_lazy;
        keep_lazy = lazy;
        f = eval(fe, c);
        keep_lazy = keep;
    }
    if (e->n == 2) *key = eval(e->args[1], c);
    else {
        *key = mk_tuple(e->n - 1);
        for (int i = 1; i < e->n; i++) (*key)->u.fcn.vals[i - 1] = eval(e->args[i], c);
    }
    if (f && !is_fcn(f) && f->kind != V_LAMBDA) {
        if (in) fail_at(e, "In computing %s, a non-function (%s) was applied as a function.", in, kind_string(f));
        fail_at(e, "A non-function (%s) was applied as a function.", kind_string(f));
    }
    return f;
}

static __attribute__((noinline)) Value *ev_apply(Expr *e, Ctx c) {
    Value *key, *f = apply_parts(e, c, 1, NULL, &key);   /* a function to apply stays lazy (§6.6) */
    return f ? fcn_apply(f, key, e) : fcndef_apply(e->args[0]->def, key, c);
}

static __attribute__((noinline)) Value *ev_dot(Expr *e, Ctx c) {
    Value *r = eval(e->args[0], c);
    if (!is_fcn(r)) fail_at(e, "Attempted to select field \"%s\" from a non-record value %s", S(e->op), pretty(r));
    Value *field = mk_str(e->op);
    if (r->made == MADE_RECORD) {
        int i = e->field;
        if (i < 0 || i >= r->n || r->u.fcn.keys[i] != field) e->field = i = fcn_index(r, field);
        if (i < 0) fail_at(e, "Attempted to select nonexistent field \"%s\" from the record\n%s", S(e->op), pretty(r));
        return r->u.fcn.vals[i];
    }
    if (r->kind == V_TUPLE) fail("Attempted to apply function with integer domain to the non-integer argument %s", pretty(field));
    /* TLC compares each element of the domain with the field, in order. */
    for (int i = 0; i < r->n; i++) if (veq(r->u.fcn.keys[i], field)) return r->u.fcn.vals[i];
    fail("Attempted to apply function:\n%s\nto argument %s, which is not in the domain of the function.",
         pretty(r), pretty(field));
}

static __attribute__((noinline)) Value *ev_except(Expr *e, Ctx c) {
    Value *f = eval(e->args[0], c);
    for (int i = 0; i < e->n - 1; i++) f = except_update(f, &e->paths[i], 0, e->args[i + 1], c, e);
    return f;
}

static __attribute__((noinline)) Value *ev_filter(Expr *e, Ctx c) {
    Bound *b = &e->bounds[0];
    Value *s = eval(b->set, c);
    Value *l = mk_lazy(L_FILTER);
    l->u.l.a = s;
    l->u.l.expr = e;
    l->u.l.env = c.env;
    l->u.l.inst = c.inst;
    l->u.l.made_in = made_in();
    /* As in TLC, a filter of a set of its elements or an interval is
       computed at once; another is lazy, membership evaluating the
       predicate on that element only. */
    return reducible(s) ? enumerate(l) : l;
}

static __attribute__((noinline)) Value *ev_map(Expr *e, Ctx c) {
    MapData d;
    memset(&d, 0, sizeof d);
    d.body = e->args[0];
    for_bindings(e->bounds, e->nb, c, map_fn, &d);
    return list_set(&d.out);
}

/* The values symbolic checking chose for an \E, as it replays a behavior:
   one for each name of its bounds, a tuple for a tuple's, in step 0
   (Init) or N, as for Gen; -1 for one out of the steps. */
typedef struct { Expr *e; int step; Value **vals; } Witness;
static Witness *witnesses;
static int nwitnesses;

/* The values symbolic checking chose for each call of Apalache's Gen, as
   it replays a behavior: a call's in step 0 (Init) or N (the Nth step),
   in the order they were made. */
typedef struct { Expr *e; int step, used; Value *v; } GenValue;
static GenValue *gen_values;
static int ngen_values, gen_step;

/* Whether d is the operator name of Apalache's module. */
static int apalache_op(Def *d, const char *name) {
    static int apalache;
    if (!apalache) apalache = intern("Apalache");
    return d->mod && d->mod->name == apalache && d->kind == D_OP && !strcmp(S(d->name), name);
}

/* Apalache's ApaFoldSet, or the same fold of its rewired community modules. */
static int is_fold_set(Def *d) {
    static int folds;
    if (!folds) folds = intern("__apalache_folds");
    return apalache_op(d, "ApaFoldSet") || (d->mod && d->mod->name == folds && !strcmp(S(d->name), "__ApalacheFoldSet"));
}

static int is_gen(Def *d) {
    static int gen;
    if (!gen) gen = intern("Gen");
    return d->name == gen && apalache_op(d, "Gen");
}

static Value *gen_value(Expr *call) {
    GenValue *any = NULL;
    for (int i = 0; i < ngen_values; i++) {
        GenValue *g = &gen_values[i];
        if (g->e != call) continue;
        if (g->step == gen_step && !g->used) { g->used = 1; return g->v; }
        if (!any) any = g;
    }
    if (!any) fail_at(call, "Symbolic checking chose no value for this Gen.");
    return any->v;
}

/* Whether a value chosen for \E e satisfies it in c: tried before its
   bounds, which may be infinite, are enumerated. */
static int witnessed(Expr *e, Ctx c) {
    for (int i = 0; i < nwitnesses; i++) {
        if (witnesses[i].e != e || (witnesses[i].step >= 0 && witnesses[i].step != gen_step)) continue;
        Value **v = witnesses[i].vals;
        Env *env = c.env;
        int in = 1;
        for (int k = 0; k < e->nb && in; k++) {
            Bound *b = &e->bounds[k];
            Value *s = eval(b->set, c);
            for (int j = 0; j < (b->tuple ? 1 : b->n) && in; j++, v++) {
                in = set_member(*v, s) && (!b->tuple || (is_fcn(*v) && fcn_is_tuple(*v) && (*v)->n == b->n));
                if (in && !b->tuple) env = mk_binding(b->defs[j], *v, env);
                for (int m = 0; in && b->tuple && m < b->n; m++) env = mk_binding(b->defs[m], (*v)->u.fcn.vals[m], env);
            }
        }
        if (in && expected_bool(eval(e->args[0], (Ctx){env, c.inst}), e)) return 1;
    }
    return 0;
}

static __attribute__((noinline)) Value *ev_forall(Expr *e, Ctx c) {
    QuantData q = {e->args[0], e->kind == X_FORALL, e};
    const char *op = e->kind == X_FORALL ? "\\A" : "\\E";
    for (int i = 0; i < e->nb; i++)
        if (!e->bounds[i].set)
            fail_at(e, "TLC attempted to evaluate an unbounded %s.\nMake sure that the expression is of form %s x \\in S: P(x).", op, op);
    if (nwitnesses && e->kind == X_EXISTS && witnessed(e, c)) return BOOLV(1);
    for_bindings(e->bounds, e->nb, c, e->kind == X_FORALL ? forall_fn : exists_fn, &q);
    return BOOLV(q.value);
}

static __attribute__((noinline)) Value *ev_choose(Expr *e, Ctx c) {
    Bound *b = &e->bounds[0];
    if (!b->set) fail_at(e, "TLC attempted to evaluate an unbounded CHOOSE.\nMake sure that the expression is of form CHOOSE x \\in S: P(x).");
    Value *s = eval(b->set, c);
    if (!is_set(s) || user_set(s))
        fail_at(e, "Attempted to compute the value of an expression of\nform CHOOSE x \\in S: P, but S was not enumerable.");
    s = enumerate(s);
    for (int i = 0; i < s->n; i++) {
        Value *x = s->u.set.elems[i];
        Env *env = c.env;
        if (!b->tuple) {
            env = mk_binding(b->defs[0], x, env);
        } else {
            if (!is_fcn(x) || !fcn_is_tuple(x) || x->n != b->n)
                fail_at(e, "Attempted to compute the value of an expression of form\n"
                           "CHOOSE <<x1, ... , xN>> \\in S: P, but S was not a set\nof N-tuples.");
            for (int j = 0; j < b->n; j++) env = mk_binding(b->defs[j], x->u.fcn.vals[j], env);
        }
        if (expected_bool(eval(e->args[0], (Ctx){env, c.inst}), e)) return x;
    }
    fail_at(e, "Attempted to compute the value of an expression of form\nCHOOSE x \\in S: P, but no element of S satisfied P.");
}

static __attribute__((noinline)) Value *ev_if(Expr *e, Ctx c) {
    Value *v = eval(e->args[0], c);
    if (v->kind != V_BOOL) fail_at(e, "A non-boolean expression (%s) was used as the condition of an IF.", kind_string(v));
    return eval(e->args[v->u.i ? 1 : 2], c);
}

static __attribute__((noinline)) Value *ev_case(Expr *e, Ctx c) {
    for (int i = 0; i + 1 < e->n; i += 2) {
        if (!e->args[i]) return eval(e->args[i + 1], c);
        Value *v = eval(e->args[i], c);
        if (v->kind != V_BOOL) {
            fail("A non-boolean expression (%s) was used as a condition of a CASE. %s", kind_string(v), node_str(e->args[i]));
        }
        if (v->u.i) return eval(e->args[i + 1], c);
    }
    fail_at(e, "Attempted to evaluate a CASE with no conditions true.");
}

/* The context of a LET's body. */
static Ctx let_env(Expr *e, Ctx c) {
    Env *env = c.env;
    for (int i = 0; i < e->ndefs; i++) env = mk_thunk(e->defs[i], e->defs[i]->body, c, env);
    /* The definitions see each other: close them over the new environment. */
    for (Env *b = env; b != c.env; b = b->next) b->ctx_env = env;
    return (Ctx){env, c.inst};
}

static __attribute__((noinline)) Value *ev_let(Expr *e, Ctx c) { return eval(e->args[0], let_env(e, c)); }

static __attribute__((noinline)) Value *ev_sqact(Expr *e, Ctx c) {
    /* [A]_v and <<A>>_v evaluated on a pair of states; as TLC, v only
       when A does not decide. */
    int sq = e->kind == X_SQACT;
    Value *a = eval(e->args[0], c);
    if (a->kind != V_BOOL) fail_at(e, "Attempted to evaluate an expression of form %s, but A was not a boolean.", sq ? "[A]_e" : "<A>_e");
    if (a->u.i == sq) return a;
    Value *now = eval(e->args[1], c);
    int saved = primed;
    primed = 1;
    Value *then = eval(e->args[1], c);
    primed = saved;
    return BOOLV(veq(now, then) == sq);
}

#define EVAL(name) static Value *name(Expr *e, Ctx c)
#define UNUSED_C (void)c
EVAL(ev_num) { UNUSED_C; return mk_int(e->num); }   /* larger ones are rejected before checking */
EVAL(ev_str) { UNUSED_C; return mk_str((int)e->num); }
EVAL(ev_bool) { UNUSED_C; return BOOLV(e->num); }
EVAL(ev_boolean) { UNUSED_C; (void)e; return boolean_set; }
EVAL(ev_stringset) { UNUSED_C; (void)e; return mk_lazy(L_STRING); }
EVAL(ev_at) {
    UNUSED_C;
    if (!at_value) fail_at(e, "@ used outside an EXCEPT.");
    return at_value;
}
EVAL(ev_decl) { return decl_value(e->def, c, e); }
EVAL(ev_and) { return junction(e, c, 1); }
EVAL(ev_or) { return junction(e, c, 0); }
EVAL(ev_enabled) { return BOOLV(enabled(e->args[0], c)); }
static Value *eval_cdot(Expr *e, Ctx c);
EVAL(ev_cdot) { return eval_cdot(e, c); }
EVAL(ev_lambda) { return mk_oper(e->def, c); }
EVAL(ev_opref) { return mk_oper(e->def, (Ctx){NULL, c.inst}); }
EVAL(ev_temporal) {
    UNUSED_C;
    const char *what = e->kind == K_ALWAYS ? "[]A" : e->kind == K_EVENTUALLY ? "<>A" : e->kind == K_LEADSTO ? "a ~> b"
                     : e->kind == K_WHILE ? "a -+-> formula" : e->kind == X_WF ? "WF" : e->kind == X_SF ? "SF"
                     : e->kind == X_TFORALL ? "\\AA" : "\\EE";
    fail_runtime(e, MANYAN_ERROR, "TLC encountered a temporal formula (%s) when evaluating a predicate or action.", what);
}
#undef UNUSED_C
#undef EVAL

/* The evaluator of each kind of expression (eval). */
static const EvalFn eval_kind[K_WHILE + 1] = {
    [X_NUM] = ev_num,
    [X_STR] = ev_str,
    [X_BOOL] = ev_bool,
    [X_NAME] = ev_temporal,
    [X_OP] = ev_temporal,
    [X_AT] = ev_at,
    [X_LAMBDA] = ev_lambda,
    [X_OPREF] = ev_opref,
    [X_SETENUM] = ev_setenum,
    [X_TUPLE] = ev_tuple,
    [X_RECORD] = ev_record,
    [X_RCDSET] = ev_rcdset,
    [X_FCNSET] = ev_fcnset,
    [X_FCN] = ev_fcn,
    [X_APPLY] = ev_apply,
    [X_DOT] = ev_dot,
    [X_EXCEPT] = ev_except,
    [X_FILTER] = ev_filter,
    [X_MAP] = ev_map,
    [X_FORALL] = ev_forall,
    [X_EXISTS] = ev_forall,
    [X_CHOOSE] = ev_choose,
    [X_IF] = ev_if,
    [X_CASE] = ev_case,
    [X_LET] = ev_let,
    [X_SQACT] = ev_sqact,
    [X_ANGLEACT] = ev_sqact,
    [X_WF] = ev_temporal,
    [X_SF] = ev_temporal,
    [X_TFORALL] = ev_temporal,
    [X_TEXISTS] = ev_temporal,
    [X_RESOLVED] = ev_temporal,
    [K_BOUND] = ev_bound,
    [K_DECL] = ev_decl,
    [K_CALL] = ev_call,
    [K_PARAMCALL] = ev_paramcall,
    [K_INSTCALL] = ev_instcall,
    [K_BOOLEAN] = ev_boolean,
    [K_STRINGSET] = ev_stringset,
    [K_AND] = ev_and,
    [K_OR] = ev_or,
    [K_NOT] = ev_not,
    [K_IMPLIES] = ev_implies,
    [K_EQUIV] = ev_equiv,
    [K_EQ] = ev_eq,
    [K_NEQ] = ev_neq,
    [K_IN] = ev_in,
    [K_NOTIN] = ev_in,
    [K_CUP] = ev_cup,
    [K_CAP] = ev_cup,
    [K_SETMINUS] = ev_cup,
    [K_SUBSETEQ] = ev_cup,
    [K_SUBSET] = ev_subset,
    [K_UNION] = ev_union,
    [K_DOMAIN] = ev_domain,
    [K_PRIME] = ev_prime,
    [K_UNCHANGED] = ev_unchanged,
    [K_ENABLED] = ev_enabled,
    [K_ALWAYS] = ev_temporal,
    [K_EVENTUALLY] = ev_temporal,
    [K_LEADSTO] = ev_temporal,
    [K_TIMES] = ev_times,
    [K_CDOT] = ev_cdot,
    [K_WHILE] = ev_temporal,
};

/* e's frame, unless manyan made e, and through an instance that substitutes
   the INSTANCE's, as TLC enters its substitutions. */
static void frames_push(Expr *e) {
    if (!e->made) frame_push(e);
    if (e->kind == K_INSTCALL && e->def->kind == D_OP)
        for (int i = 0; i < e->ndefs; i++) if (e->defs[i]->nsubst && e->defs[i]->where) frame_push(e->defs[i]->where);
}

static Value *eval_tracked(Expr *e, Ctx c) {
    int n = nframes;
    frames_push(e);
    Value *v = eval_kind[e->kind](e, c);
    nframes = n;
    return v;
}
/* eval_fns is eval_kind, or while tracking a table of eval_tracked: the
   hot path tests nothing. */
static EvalFn eval_tracking[K_WHILE + 1];
static const EvalFn *eval_fns = eval_kind;
static inline Value *eval(Expr *e, Ctx c) { return eval_fns[e->kind](e, c); }


/* An argument for an operator parameter: an operator. */
static Value *eval_operator_arg(Expr *a, Ctx c) {
    if (a->kind == X_LAMBDA || a->kind == X_OPREF) return eval(a, c);
    if (a->kind == K_CALL && a->n == 0) return mk_oper(a->def, (Ctx){a->def->local == 2 ? c.env : NULL, c.inst});
    if (a->kind == K_PARAMCALL && a->n == 0 && a->def->kind == D_PARAM) {
        Env *b = env_find(c.env, a->def);
        if (!b) fail_at(a, "Unbound operator parameter %s.", S(a->def->name));
        return force(b);
    }
    if (a->kind == K_PARAMCALL && a->n == 0) return decl_value(a->def, c, a);
    if (a->kind == K_INSTCALL && a->n == 0) {
        Inst *inst = c.inst;
        for (int i = 0; i < a->ndefs; i++) {
            Inst *in = NEW(Inst);
            in->def = a->defs[i];
            in->parent = inst;
            inst = in;
        }
        return mk_oper(a->def, (Ctx){NULL, inst});
    }
    return eval(a, c);
}

static Value *call_values(Def *d, Value **vals, int n, Ctx c, Expr *where) {
    if (d->native) return call_native(d, where, vals, c);
    Env *env = c.env;
    if (d->kind == D_FCN) return fcndef_apply(d, n == 1 ? vals[0] : NULL, c);
    for (int i = 0; i < n && i < d->nparams; i++) env = mk_binding(d->params[i], vals[i], env);
    Ctx inner = {env, c.inst};
    return eval_body(d->body, inner);
}

/* As TLC's OpRcdValue: the value of the first line whose arguments equal args. */
static Value *table_apply(Value *op, Value **args, int n) {
    Value *t = op->u.op.table;
    for (int i = 0; i < t->n; i++) {
        Value *line = t->u.fcn.vals[i];
        if (line->n - 1 != n) fail("Attempted to apply the operator %s\nwith wrong number of arguments.", pretty(op));
        int j = 0;
        while (j < n && veq(line->u.fcn.vals[j], args[j])) j++;
        if (j == n) return line->u.fcn.vals[n];
    }
    Buf b = {0};
    for (int i = 0; i < n; i++) { if (i) buf_puts(&b, ", "); print_value(&b, args[i]); }
    fail("Attempted to apply operator:\n%s\nto arguments (%s), which is undefined.", pretty(op), buf_take(&b));
}

static Value *apply_oper(Value *op, Value **args, int n, Expr *where) {
    if (op->u.op.table) return table_apply(op, args, n);
    Def *d = op->u.op.def;
    if (d->replacement) d = d->replacement;
    if (d->nparams != n && !d->native)
        fail_at(where, "The operator %s requires %d arguments.", S(d->name), d->nparams);
    Ctx c = {op->u.op.env, op->u.op.inst};
    if (d->local == 2 && !d->native) {
        Env *b = env_find(c.env, d);
        if (b) c.env = b->ctx_env;
    }
    return call_values(d, args, n, c, where);
}

/* TLC normalizes the value of a constant definition, as a state's. */
static void materialize(Value *v) {
    if (v->kind == V_LAZY) switch (v->lazy) {   /* a set TLC keeps: its parts */
    case L_UNION: v = union_sets(v); break;
    case L_CUP: case L_CAP: case L_DIFF: case L_FCNSET: materialize(v->u.l.b); /* fall through */
    case L_SUBSET: materialize(v->u.l.a); return;
    case L_TIMES: case L_RCDSET: for (int i = 0; i < v->n; i++) materialize(v->u.l.names[v->n + i]); return;
    }
    if (v->kind == V_SET) for (int i = 0; i < v->n; i++) materialize(v->u.set.elems[i]);
    if (!is_fcn(v)) return;
    if (v->made >= MADE_LAMBDA) v->made = MADE_PLAIN;
    for (int i = 0; i < v->n; i++) materialize(v->u.fcn.vals[i]);
}

/* v, made in another arena, as a value of this one; NULL past *budget
   values, or if it holds what keeps its context: an operator, a lazy
   function or a filter. A set keeps its sets, not what it cached. */
static Value **copy_values(Value **vs, int n, long *budget);

static Value *copy_value(Value *v, long *budget) {
    if (v->kind == V_BOOL || v->kind == V_STR) return v;
    if (--*budget < 0) return NULL;
    Value *c = NEW(Value);
    *c = *v;
    switch (v->kind) {
    case V_INT: case V_MODEL: case V_INTERVAL: return c;
    case V_SET:
        if (!(c->u.set.elems = copy_values(v->u.set.elems, v->n, budget))) return NULL;
        if (v->u.set.product && !(c->u.set.product = copy_value(v->u.set.product, budget))) return NULL;
        return c;
    case V_TUPLE: case V_FCN:
        if (v->kind == V_FCN && !(c->u.fcn.keys = copy_values(v->u.fcn.keys, v->n, budget))) return NULL;
        return (c->u.fcn.vals = copy_values(v->u.fcn.vals, v->n, budget)) ? c : NULL;
    case V_LAZY:
        c->perm = 1;
        c->u.l.b = c->u.l.set = NULL;   /* what it kept */
        switch (v->lazy) {
        case L_NAT: case L_INT: case L_STRING: case L_ANY: return c;
        case L_TIMES: case L_RCDSET: return (c->u.l.names = copy_values(v->u.l.names, 2 * v->n, budget)) ? c : NULL;
        case L_CUP: case L_CAP: case L_DIFF: case L_FCNSET: if (!(c->u.l.b = copy_value(v->u.l.b, budget))) return NULL; break;
        case L_UNION: case L_SEQ: case L_SUBSET: break;
        default: return NULL;
        }
        return (c->u.l.a = copy_value(v->u.l.a, budget)) ? c : NULL;
    default: return NULL;
    }
}

/* An array of values, any of them NULL, copied. */
static Value **copy_values(Value **vs, int n, long *budget) {
    Value **c = alloc_raw(sizeof(Value *) * (size_t)n);
    for (int i = 0; i < n; i++)
        if (!(c[i] = vs[i] ? copy_value(vs[i], budget) : NULL) && vs[i]) return NULL;
    return c;
}


static Value *def_value(Def *d);

static Value *call_def(Def *d, Expr **args, int n, Ctx c, Expr *call) {
    if (d->replacement) d = d->replacement;
    if (d->kind == D_CONST || d->kind == D_VAR) return decl_value(d, c, call);
    if (d->value) return d->value;
    if (ngen_values && is_gen(d)) return gen_value(call);
    if (d->kind == D_FCN) {
        if (d->local != 2 && d->level == 0 && d->cache) return d->cache;
        Value *v = fcndef_value(d, c);
        return v;
    }
    if (d->kind == D_PARAM) {
        Env *b = env_find(c.env, d);
        return force(b);
    }
    if (n < d->nparams && n == 0) return mk_oper(d, (Ctx){d->local == 2 ? c.env : NULL, c.inst});
    if (d->local == 2) {
        /* A LET definition: its parameters, then its closure. */
        Env *b = env_find(c.env, d);
        if (!b) fail_at(call, "Unbound LET definition %s.", S(d->name));
        if (d->nparams == 0) return force(b);
        Env *env = b->ctx_env;
        for (int i = 0; i < n; i++) {
            if (d->params[i]->arity) env = mk_binding(d->params[i], eval_operator_arg(args[i], c), env);
            else env = mk_arg(d->params[i], args[i], c, env);
        }
        Ctx inner = {env, b->ctx_inst};
        return eval_body(d->body, inner);
    }
    if (d->native && d->lazy) {
        Value *v = call_native(d, call, NULL, c);
        if (v) return v;   /* NULL: as TLC's evaluation methods, it leaves this call to the definition */
    } else if (d->native) {
        Value **vals = NEWN(Value *, n);
        for (int i = 0; i < n; i++)
            vals[i] = d->params[i]->arity ? eval_operator_arg(args[i], c) : eval(args[i], c);
        return call_native(d, call, vals, c);
    }
    Inst *in = c.inst;
    while (in && in->def == &enabled_mark) in = in->parent;
    if (n == 0 && !in) {   /* a definition of the spec, computed once if constant */
        if (d->cache) return d->cache;
        if (def_level(d) == 0 && !keep_lazy && !d->uncached) return d->cache = def_value(d);
    }
    Env *env = NULL;
    for (int i = 0; i < n; i++) {
        if (d->params[i]->arity) env = mk_binding(d->params[i], eval_operator_arg(args[i], c), env);
        else env = mk_arg(d->params[i], args[i], c, env);
    }
    Ctx inner = {env, c.inst};
    return eval_body(d->body, inner);
}

/* ---------------------------------------------------------------- standard modules */

#define NATIVE(name) static Value *name(Expr *call, Value **a, Ctx c)

static Value *api_call(Def *d, Expr *call, Value **args, Ctx c);

static Value *call_native(Def *d, Expr *call, Value **args, Ctx c) {
    if (java_depth < 64) java_frames[java_depth] = d->java;
    java_depth++;
    Value *v = d->api ? api_call(d, call, args, c) : d->native(call, args, c);
    java_depth--;
    return v;
}
#define UNUSED (void)call; (void)a; (void)c

/* ---------------------------------------------------------------- native operators of manyan.h */

struct ManyanCall { Expr *call; Value **args; Ctx c; };

NATIVE(n_defined) { UNUSED; return NULL; }   /* marks a Def whose native is d->api */

static const char *java_class(Value *v);

/* Each argument cast to its parameter's class, as Java invokes TLC's
   method: a StringValue parameter takes only a string; a Value, anything. */
static void java_cast(const char *java, Value **args, int n) {
    const char *p = strchr(java, '(');
    for (int i = 0; p && i < n; i++, p = strchr(p, ',')) {
        const char *t = ++p, *end = t + strcspn(t, ",)");
        if (strncmp(t, "tlc2.value.impl.", 16) || (end - t == 21 && !strncmp(t + 16, "Value", 5))) continue;
        const char *cls = java_class(args[i]);
        if ((size_t)(end - t - 16) != strlen(cls) || strncmp(t + 16, cls, strlen(cls)))
            fail("Cannot cast tlc2.value.impl.%s to %.*s", cls, (int)(end - t), t);
    }
}

static Value *api_call(Def *d, Expr *call, Value **args, Ctx c) {
    for (int i = 0; args && i < d->nparams; i++) args[i] = realize(args[i]);
    if (args) java_cast(d->java, args, d->nparams);
    ManyanCall tc = {call, args, c};
    return d->api(&tc, args);
}

static struct { const char *module, *name; int arity; ManyanNative fn; const char *java; } *defined;
static int ndefined;

int manyan_define(const char *module, const char *name, int arity, ManyanNative fn, const char *java) {
    void *grown = realloc(defined, sizeof *defined * (size_t)(ndefined + 1));
    if (!grown) return -1;
    defined = grown;
    defined[ndefined].module = module, defined[ndefined].name = name, defined[ndefined].arity = arity;
    defined[ndefined].fn = fn, defined[ndefined++].java = java;
    return 0;
}

ManyanKind manyan_kind(Value *v) {
    switch (v->kind) {
    case V_BOOL: return MANYAN_BOOL;
    case V_INT: return MANYAN_INT;
    case V_STR: return MANYAN_STRING;
    case V_MODEL: return MANYAN_MODEL;
    case V_TUPLE: return MANYAN_TUPLE;
    case V_FCN: case V_LAMBDA: return MANYAN_FUNCTION;
    default: return is_set(v) ? MANYAN_SET : MANYAN_OTHER;
    }
}

Value *manyan_bool(int b) { return BOOLV(b); }
Value *manyan_int(int64_t i) { return mk_int(i); }
Value *manyan_string(const char *s, size_t n) { return mk_str(intern_n(s, (int)n)); }

Value *manyan_tuple(size_t n, Value *const *elems) {
    Value *t = mk_tuple((int)n);
    for (size_t i = 0; i < n; i++) t->u.fcn.vals[i] = elems[i];
    return t;
}

Value *manyan_function(size_t n, Value *const *keys, Value *const *values) {
    List k = {(Value **)keys, (int)n, (int)n}, v = {(Value **)values, (int)n, (int)n};
    return mk_fcn_from(&k, &v);
}

Value *manyan_record(size_t n, Value *const *names, Value *const *values) {
    Value *r = manyan_function(n, names, values);
    r->made = MADE_RECORD;
    return r;
}

Value *manyan_set(size_t n, Value *const *elems) {
    List l = {0};
    for (size_t i = 0; i < n; i++) list_add(&l, elems[i]);
    return list_set(&l);
}

int manyan_is_true(Value *v) { return v->kind == V_BOOL && v->u.i; }
int64_t manyan_int_value(Value *v) { return v->u.i; }

const char *manyan_string_value(Value *v, size_t *len) {
    if (len) *len = (size_t)strs[v->u.i].len;
    return S(v->u.i);
}

size_t manyan_size(Value *v) { return (size_t)v->n; }
Value *manyan_key(Value *v, size_t i) { return v->kind == V_TUPLE ? mk_int((int64_t)i + 1) : v->u.fcn.keys[i]; }
Value *manyan_value(Value *v, size_t i) { return realize(v->u.fcn.vals[i]); }

Value *manyan_field(Value *r, const char *name) {
    int i = is_fcn(r) ? fcn_index(r, mk_str(intern(name))) : -1;
    return i < 0 ? NULL : realize(r->u.fcn.vals[i]);
}

Value *manyan_elements(Value *s) { return is_set(s) && enumerable(s) ? enumerate(s) : NULL; }
Value *manyan_element(Value *s, size_t i) { return realize(s->u.set.elems[i]); }
int manyan_compare(Value *a, Value *b) { return vcmp(a, b); }
void *manyan_alloc(size_t n) { return alloc(n); }

/* Java's String.format(f, args), each argument a string: %s and %S, with
   flag -, a width and a precision, %b, %h, %n and %%, an argument by its
   index or in turn. Any other conversion of a string is Java's exception,
   whose message it gives, its class in cls; NULL if none. */
static const char *java_format(Buf *b, const char *f, int n, const char *const *args, const char **cls) {
    static char msg[64];
    int next = 0;
    for (const char *p = f; *p; p++) {
        if (*p != '%') { buf_add(b, p, 1); continue; }
        const char *spec = p++;
        long index = 0;
        int left = 0, width = 0, prec = -1;
        const char *q = p;
        for (; isdigit((unsigned char)*q); q++) if (index <= INT32_MAX) index = index * 10 + (*q - '0');
        if (*q == '$' && q > p) {
            if (index > INT32_MAX) {
                *cls = "java.util.IllegalFormatArgumentIndexException";
                return "Format argument index: (not representable as int)";
            }
            p = q + 1;
        }
        else index = 0;
        for (; *p && strchr("-#+ 0,(<", *p); p++) left |= *p == '-';
        while (isdigit((unsigned char)*p)) width = width * 10 + (*p++ - '0');
        if (*p == '.') for (prec = 0, p++; isdigit((unsigned char)*p); p++) prec = prec * 10 + (*p - '0');
        char c = *p;
        if (c == '%' || c == 'n') { buf_puts(b, c == '%' ? "%" : "\n"); continue; }
        if (!c || !strchr("sSbBhHdoxXeEfgGaAcCtT", c)) {
            snprintf(msg, sizeof msg, "Conversion = '%c'", c ? c : '%');
            *cls = "java.util.UnknownFormatConversionException";
            return msg;
        }
        int i = index ? (int)index - 1 : next++;
        if (i >= n) {
            snprintf(msg, sizeof msg, "Format specifier '%.*s'", (int)(p - spec + 1), spec);
            *cls = "java.util.MissingFormatArgumentException";
            return msg;
        }
        if (!strchr("sSbBhH", c)) {
            snprintf(msg, sizeof msg, "%c != java.lang.String", tolower((unsigned char)c));
            *cls = "java.util.IllegalFormatConversionException";
            return msg;
        }
        Buf t = {0};
        if (c == 's' || c == 'S') buf_puts(&t, args[i]);
        else if (c == 'b' || c == 'B') buf_puts(&t, "true");
        else {
            uint32_t h = 0;   /* Java's String.hashCode */
            for (const char *k = args[i]; *k; k++) h = 31 * h + (unsigned char)*k;
            buf_printf(&t, "%x", h);
        }
        int len = prec >= 0 && (size_t)prec < t.n ? prec : (int)t.n;
        if (isupper((unsigned char)c)) for (int k = 0; k < len; k++) t.s[k] = (char)toupper((unsigned char)t.s[k]);
        buf_printf(b, left ? "%-*.*s" : "%*.*s", width, len, t.s ? t.s : "");
        free(t.s);
    }
    return NULL;
}

const char *manyan_print(Value *v) { return pretty(v); }
const char *manyan_to_string(Value *v) { return value_str(v); }
const char *manyan_class(Value *v) { return java_class(v); }

/* A record's field i as TLC keeps it before it normalizes the record, as
   its Java sees it: as written; a state's of Trace in the order of its
   variables, after _action if it has one. Stored in a state, it is
   normalized: in order. */
size_t manyan_kept(Value *v, size_t i) {
    if (v->kind != V_FCN || v->made != MADE_RECORD) return i;
    Expr *e = v->u.fcn.source;
    size_t a = v->range && v->n > nvars;   /* _action first, as TLC */
    int name = v->range ? (i < a ? intern("_action") : vars[i - a]->name) : e && e->kind == X_RECORD && e->n == v->n ? e->segs[i].name : -1;
    if (name < 0) return i;
    for (int k = 0; k < v->n; k++) if (v->u.fcn.keys[k]->u.i == name) return (size_t)k;
    return i;
}

Value *manyan_format(ManyanCall *call, const char *fmt, size_t n, const char *const *args) {
    Buf b = {0};
    const char *cls, *why = java_format(&b, fmt, (int)n, args, &cls);
    if (why) { free(b.s); manyan_throw(call, "%s", why); }
    Value *v = mk_str(intern(b.s ? b.s : ""));
    free(b.s);
    return v;
}

Value *manyan_arg(ManyanCall *call, int i) { return realize(call->args ? call->args[i] : eval(call->call->args[i], call->c)); }

void manyan_fail(ManyanCall *call, const char *fmt, ...) {
    (void)call;
    va_list ap;
    va_start(ap, fmt);
    vfail(NULL, 1, MANYAN_ERROR, fmt, ap);
}

void manyan_throw(ManyanCall *call, const char *fmt, ...) {
    (void)call;
    va_list ap;
    va_start(ap, fmt);
    vfail(NULL, 0, MANYAN_ERROR, fmt, ap);
}


NATIVE(n_nat) { UNUSED; return mk_lazy(L_NAT); }
NATIVE(n_int) { UNUSED; return mk_lazy(L_INT); }
NATIVE(n_plus) { UNUSED; int64_t x = int_cast(a[0]), y = int_cast(a[1]); return mk_int(int_op(x, y, '+')); }
NATIVE(n_minus) { UNUSED; int64_t x = int_cast(a[0]), y = int_cast(a[1]); return mk_int(int_op(x, y, '-')); }
NATIVE(n_times) { UNUSED; int64_t x = int_cast(a[0]), y = int_cast(a[1]); return mk_int(int_op(x, y, '*')); }
NATIVE(n_lt) { UNUSED; int64_t x = int_arg(a[0], 1, "<"), y = int_arg(a[1], 2, "<"); return BOOLV(x < y); }
NATIVE(n_gt) { UNUSED; int64_t x = int_arg(a[0], 1, ">"), y = int_arg(a[1], 2, ">"); return BOOLV(x > y); }
NATIVE(n_leq) { UNUSED; int64_t x = int_arg(a[0], 1, "<="), y = int_arg(a[1], 2, "<="); return BOOLV(x <= y); }
NATIVE(n_geq) { UNUSED; int64_t x = int_arg(a[0], 1, ">="), y = int_arg(a[1], 2, ">="); return BOOLV(x >= y); }
NATIVE(n_neg) { UNUSED; int64_t x = int_cast(a[0]); return mk_int(int_op(0, x, '-')); }

NATIVE(n_pow) {
    UNUSED;
    int64_t x = int_cast(a[0]), y = int_cast(a[1]);
    if (y < 0) fail_module("The second argument of ^ should be a natural number, but instead it is:\n%lld", (long long)y);
    if (x == 0 && y == 0) fail_module("0^0 is undefined.");
    int64_t r = 1;
    for (int64_t i = 0; i < y; i++) {
        r *= x;
        if (r > 2147483647LL || r < -2147483648LL) fail_module("Overflow when computing %lld^%lld", (long long)x, (long long)y);
    }
    return mk_int(r);
}

NATIVE(n_div) {
    UNUSED;
    int64_t x = int_cast(a[0]), y = int_cast(a[1]);
    if (y == 0) fail_module("The second argument of \\div is 0.");
    int64_t q = x / y;
    if ((x % y != 0) && ((x < 0) != (y < 0))) q--;
    return mk_int(check_int(q, x, y, "\\div"));
}

NATIVE(n_mod) {
    UNUSED;
    int64_t x = int_cast(a[0]), y = int_cast(a[1]);
    if (y <= 0) fail_module("The second argument of %% should be a positive number, but instead it is:\n%lld", (long long)y);
    int64_t r = x % y;
    if (r < 0) r += y;
    return mk_int(r);
}

NATIVE(n_range) {
    UNUSED;
    return mk_interval(int_cast(a[0]), int_cast(a[1]));
}

/* A sequence: a function on 1..n. */
static Value *seq_arg(Value *v, const char *error) {
    v = realize(v);
    if (is_fcn(v) && (fcn_is_tuple(v) || v->n == 0)) return v;
    fail_module("%s:\n%s", error, pretty(v));
}

#define NOT_SEQ(arg, op) "The " arg " of " op " should be a sequence, but instead it is"

static Value *seq_of(Value *f) {
    if (f->kind == V_TUPLE) return f;
    Value *t = mk_tuple(f->n);
    for (int i = 0; i < f->n; i++) t->u.fcn.vals[i] = f->u.fcn.vals[i];
    return t;
}

NATIVE(n_seq) { UNUSED; Value *s = mk_lazy(L_SEQ); s->u.l.a = a[0]; return s; }

NATIVE(n_len) {
    UNUSED;
    if (a[0]->kind == V_STR) return mk_int(strs[a[0]->u.i].len);
    return mk_int(seq_arg(a[0], NOT_SEQ("argument", "Len"))->n);
}

/* s \o t for a string s. */
static Value *str_concat(Value *s, Value *t) {
    if (t->kind != V_STR) fail_module("Evaluating an expression of the form t \\o s when s is not a string:\n%s", pretty(t));
    Buf b = {0};
    buf_puts(&b, S(s->u.i));
    buf_puts(&b, S(t->u.i));
    int id = intern_n(b.s ? b.s : "", (int)b.n);
    free(b.s);
    return mk_str(id);
}

NATIVE(n_concat) {
    UNUSED;
    if (a[0]->kind == V_STR) return str_concat(a[0], a[1]);
    Value *x = seq_arg(a[0], "Evaluating an expression of the form s \\o t when s is not a sequence"),
          *y = seq_arg(a[1], "Evaluating an expression of the form t \\o s when s is not a sequence");
    Value *t = mk_tuple(x->n + y->n);
    for (int i = 0; i < x->n; i++) t->u.fcn.vals[i] = x->u.fcn.vals[i];
    for (int i = 0; i < y->n; i++) t->u.fcn.vals[x->n + i] = y->u.fcn.vals[i];
    return t;
}

NATIVE(n_append) {
    UNUSED;
    Value *x = seq_arg(a[0], "Evaluating an expression of the form Append(s, v) when s is not a sequence");
    Value *t = mk_tuple(x->n + 1);
    for (int i = 0; i < x->n; i++) t->u.fcn.vals[i] = x->u.fcn.vals[i];
    t->u.fcn.vals[x->n] = a[1];
    if (x->u.fcn.hash) t->u.fcn.hash = x->u.fcn.hash + pair_hash(t, x->n, a[1]);
    return t;
}

NATIVE(n_head) {
    UNUSED;
    Value *x = seq_arg(a[0], NOT_SEQ("argument", "Head"));
    if (x->n == 0) fail_module("Attempted to apply Head to the empty sequence.");
    return x->u.fcn.vals[0];
}

NATIVE(n_tail) {
    UNUSED;
    int str = a[0]->kind == V_STR;   /* TLC's Len, Tail, SubSeq and \o take a string as its characters */
    Value *x = str ? NULL : seq_arg(a[0], NOT_SEQ("argument", "Tail"));
    int len = str ? strs[a[0]->u.i].len : x->n;
    if (len == 0) fail_module("Attempted to apply Tail to the empty sequence.");
    if (str) return substr(a[0], 1, len - 1);
    Value *t = mk_tuple(x->n - 1);
    for (int i = 1; i < x->n; i++) t->u.fcn.vals[i - 1] = x->u.fcn.vals[i];
    return t;
}

NATIVE(n_subseq) {
    UNUSED;
    int str = a[0]->kind == V_STR;
    Value *x = str ? NULL : seq_arg(a[0], NOT_SEQ("first argument", "SubSeq"));
    for (int i = 1; i < 3; i++)
        if (a[i]->kind != V_INT)
            fail_module("The %s argument of SubSeq should be a natural number, but instead it is:\n%s", i == 1 ? "second" : "third", pretty(a[i]));
    int64_t m = a[1]->u.i, n = a[2]->u.i, len = str ? strs[a[0]->u.i].len : x->n;
    if (m > n) return str ? substr(a[0], 0, 0) : mk_tuple(0);
    int second = m < 1 || m > len;
    if (second || n > len)
        fail_module("The %s argument of SubSeq must be in the domain of its first argument:\n%s\n, but instead it is\n%lld",
                    second ? "second" : "third", pretty(a[0]), (long long)(second ? m : n));
    if (str) return substr(a[0], (int)m - 1, (int)(n - m + 1));
    Value *t = mk_tuple((int)(n - m + 1));
    for (int64_t i = m; i <= n; i++) t->u.fcn.vals[i - m] = x->u.fcn.vals[i - 1];
    return t;
}

NATIVE(n_selectseq) {
    UNUSED;
    Value *x = seq_arg(a[0], NOT_SEQ("first argument", "SelectSeq"));
    List l = {0};
    for (int i = 0; i < x->n; i++) {
        Value *r = apply_oper(a[1], &x->u.fcn.vals[i], 1, call);
        if (r->kind != V_BOOL) fail_module("The second argument of SelectSeq should be a operator, but instead it is:\n%s", pretty(r));
        if (r->u.i) list_add(&l, x->u.fcn.vals[i]);
    }
    Value *t = mk_tuple(l.n);
    for (int i = 0; i < l.n; i++) t->u.fcn.vals[i] = l.v[i];
    return t;
}

/* TLC's isFinite, which IsFiniteSet asks: a function is a finite set,
   another value an error, and some sets cannot tell. */
static int tlc_finite(Value *s) {
    static const char *what[] = {[V_BOOL] = "boolean", [V_INT] = "integer", [V_STR] = "string", [V_MODEL] = "model value"};
    Value *a = s->u.l.a, *b = s->u.l.b;
    switch (s->kind) {
    case V_BOOL: case V_INT: case V_STR: case V_MODEL:
        fail("Attempted to check if the %s %s is a finite set.", what[s->kind], pretty(s));
    case V_LAMBDA: fail("Attempted to check if the function:\n%s\nis a finite set.", pretty(s));
    case V_LAZY: break;
    default: return 1;
    }
    switch (s->lazy) {
    case L_FILTER:
        if (!tlc_finite(a))
            fail("Attempted to check if expression of form {x \\in S : p(x)} is a finite set, but cannot check if S:\n%s\nis finite.", pretty(a));
        return 1;
    case L_CAP: case L_DIFF:
        if (s->lazy == L_DIFF ? tlc_finite(a) : tlc_finite(a) || tlc_finite(b)) return 1;
        if (s->lazy == L_CAP || !tlc_finite(b)) fail("Attempted to check if the set %sis finite.", pretty(s));
        return 0;
    case L_CUP: return tlc_finite(a) && tlc_finite(b);
    case L_SUBSET: return tlc_finite(a);
    case L_TIMES: case L_RCDSET: {   /* finite when a part is empty, or all are finite */
        int all = 1;
        for (int i = 0; i < s->n; i++) {
            Value *part = s->u.l.names[s->n + i];
            if (!tlc_finite(part)) all = 0;
            else if (set_size(union_cache(part)) == 0) return 1;
        }
        return all;
    }
    case L_FCNSET: {   /* [S -> T]: also when S or T is empty, or T has one element */
        int dom = tlc_finite(a);
        if (dom && set_size(union_cache(a)) == 0) return 1;
        int range = tlc_finite(b);
        return range && (dom || set_size(union_cache(b)) <= 1);
    }
    case L_SEQ: return tlc_finite(a) && set_size(union_cache(a)) == 0;
    case L_UNION:
        union_sets(s);
        for (int i = 0; i < s->u.l.a->n; i++) if (!tlc_finite(s->u.l.a->u.set.elems[i])) return 0;
        return 1;
    default: return !set_is_infinite(s);
    }
}

NATIVE(n_isfinite) { UNUSED; return BOOLV(tlc_finite(a[0])); }

NATIVE(n_cardinality) {
    UNUSED;
    if (!is_set(a[0]) || user_set(a[0])) fail_module("Attempted to compute cardinality of the value\n%s", pretty(a[0]));
    if (set_is_infinite(a[0])) count_infinite(a[0]);
    int64_t n = set_size(union_cache(a[0]));
    if (n < 0)
        fail("Overflow when computing the number of elements in%s%s",
                    a[0]->lazy == L_TIMES ? " " : ":\n", pretty(a[0]));
    return mk_int(n);
}

/* v, as TLC prints it: it enumerates an infinite S \cup T or S \ T
   inside, which fails. */
static Value *printable(Value *v) {
    if (v->kind == V_LAZY && v->lazy >= L_UNION) enumerate(v);
    if (v->kind == V_SET) for (int i = 0; i < v->n; i++) printable(v->u.set.elems[i]);
    if (is_fcn(v)) for (int i = 0; i < v->n; i++) printable(v->u.fcn.vals[i]);
    return v;
}

static FILE *user_file;   /* where Print writes, -userFile; NULL for standard output */
static int reprinting;    /* a constant computed again, which has printed */

NATIVE(n_print) {
    UNUSED;
    printable(a[0]), printable(a[1]);
    if (in_worker) worker_cannot();   /* the search prints in order */
    FILE *out = user_file ? user_file : stdout;
    if (!reprinting) fprintf(out, "%s  %s\n", pretty(a[0]), pretty(a[1]));
    fflush(out);
    return a[1];
}

NATIVE(n_printt) {
    UNUSED;
    if (in_worker) worker_cannot();
    FILE *out = user_file ? user_file : stdout;
    if (!reprinting) fprintf(out, "%s\n", pretty(printable(a[0])));
    fflush(out);
    return TRUEV;
}

NATIVE(n_assert) {
    UNUSED;
    if (a[0]->kind == V_BOOL && a[0]->u.i) return TRUEV;
    error_reset();
    buf_printf(&error_message, "The first argument of Assert evaluated to FALSE; the second argument was:\n%s", pretty(a[1]));
    error_status = MANYAN_VIOLATION_ASSERT;
    error_module = 1;
    raise_error();
}

NATIVE(n_javatime) { UNUSED; return mk_int((int64_t)time(NULL) & 0x7fffffff); }

static void encode(Buf *b, Value *v);
static Value *decode(const char **p);

/* TLCSet's registers, each its value encoded, as values do not outlive
   the state being expanded. */
static Buf *registers;
static int nregisters;
static int starting;   /* the model is being read: TLC's checker, which TLCGet asks, does not exist yet */
static int64_t search_counter(const char *key);
static int checking_posts;   /* the search is over: its count of states generated is TLC's */
static long sim_traces;   /* the behavior a simulation generates, from 1; 0 for the initial states */
static Value *search_config(void);
static Value *tlc_revision(void);
static Value *sim_stats(void);
static Value *action_record(Value **st);
static Value *action_value(int act);

/* TLC's Java system properties, which TLCGet("-Dk") reads and TLCSet("-Dk", v)
   sets: pairs of k and its value, interned. A worker leaves them to manyan. */
static int *props, nprops;
static int *prop(const char *key) {
    if (strncmp(key, "-D", 2)) return NULL;
    if (in_worker) worker_cannot();
    for (int i = 0; i < nprops; i += 2) if (!strcmp(S(props[i]), key)) return &props[i + 1];
    props = xrealloc(props, sizeof(int) * (size_t)(nprops + 2));
    props[nprops] = intern(key), props[nprops + 1] = props[nprops];   /* unset, it is the key */
    return &props[(nprops += 2) - 1];
}

NATIVE(n_tlcget) {
    UNUSED;
    Value *k = a ? a[0] : eval(call->args[0], c);
    if (k->kind == V_STR) {
        const char *key = S(k->u.i);
        int *p = prop(key);
        if (p) return mk_str(*p);
        if (!strcmp(key, "level")) return mk_int(cur_level + primed);   /* primed, the next state's */
        if (!strcmp(key, "config") && !starting) return search_config();
        if (!strcmp(key, "revision")) return tlc_revision();
        if (!strcmp(key, "stats") && simulating) return sim_stats();
        if (!strcmp(key, "action")) return action_record(primed ? next_state : cur_state);
        if (!strcmp(key, "diameter") && simulating) return mk_int(sim_traces);   /* TLC's count of behaviors */
        int64_t n = starting ? -1 : search_counter(key);
        if (n < 0) fail("TLCGet(%s) was undefined.", key);
        return mk_int(n);
    }
    if (k->kind != V_INT || k->u.i < 0)
        fail("The argument of TLCGet should be a nonnegative integer, but instead it is:\n%s", pretty(k));
    if (starting || k->u.i >= nregisters || !registers[k->u.i].n) fail("TLCGet(%s) was undefined.", pretty(k));
    const char *p = registers[k->u.i].s;
    return decode(&p);
}

NATIVE(n_tlcset) {
    UNUSED;
    if (a[0]->kind == V_STR && !strcmp(S(a[0]->u.i), "exit")) {   /* the search stops after this state */
        if (a[1]->kind == V_BOOL && a[1]->u.i) {
            if (in_worker) worker_cannot();
            exit_requested = 1;
        }
        return TRUEV;
    }
    int *p = a[0]->kind == V_STR ? prop(S(a[0]->u.i)) : NULL;
    if (p) {
        *p = intern(pretty(a[1]));
        return TRUEV;
    }
    if (a[0]->kind != V_INT || a[0]->u.i < 0)
        fail_module("The first argument of TLCSet should be a nonnegative integer, but instead it is:\n%s", pretty(a[0]));
    int i = (int)a[0]->u.i;
    if (i >= nregisters) {
        registers = xrealloc(registers, sizeof(Buf) * (size_t)(i + 1));
        memset(registers + nregisters, 0, sizeof(Buf) * (size_t)(i + 1 - nregisters));
        nregisters = i + 1;
    }
    registers[i].n = 0;
    encode(&registers[i], a[1]);
    return TRUEV;
}

NATIVE(n_singleton) {
    UNUSED;
    Value *f = mk_fcn(1);
    f->u.fcn.keys[0] = a[0];
    f->u.fcn.vals[0] = a[1];
    return f;
}

NATIVE(n_merge) {
    UNUSED;
    for (int i = 0; i < 2; i++) {
        a[i] = realize(a[i]);
        if (a[i]->kind == V_LAMBDA) enumerate(a[i]->u.l.a);   /* TLC enumerates the domain, which fails */
        if (!is_fcn(a[i]))
            fail_module("The %s argument of @@ should be a function, but instead it is:\n%s", i ? "second" : "first", pretty(a[i]));
    }
    List keys = {0}, vals = {0};
    for (int i = 0; i < a[0]->n; i++) { list_add(&keys, fcn_key(a[0], i)); list_add(&vals, a[0]->u.fcn.vals[i]); }
    for (int i = 0; i < a[1]->n; i++) {
        Value *k = fcn_key(a[1], i);
        int seen = 0;
        for (int j = 0; j < a[0]->n && !seen; j++) seen = veq(k, fcn_key(a[0], j));
        if (!seen) { list_add(&keys, k); list_add(&vals, a[1]->u.fcn.vals[i]); }
    }
    return mk_fcn_from(&keys, &vals);
}

NATIVE(n_permutations) {
    UNUSED;
    Value *s = enumerate(a[0]);
    int n = s->n;
    if (n > 10) fail_module("Attempted to compute Permutations of a set with more than 10 elements.");
    List out = {0};
    int *p = NEWN(int, n);
    for (int i = 0; i < n; i++) p[i] = i;
    for (;;) {
        Value *f = mk_fcn(n);
        for (int i = 0; i < n; i++) { f->u.fcn.keys[i] = s->u.set.elems[i]; f->u.fcn.vals[i] = s->u.set.elems[p[i]]; }
        list_add(&out, f);
        int i = n - 2;
        while (i >= 0 && p[i] >= p[i + 1]) i--;
        if (i < 0) break;
        int j = n - 1;
        while (p[j] <= p[i]) j--;
        int t = p[i]; p[i] = p[j]; p[j] = t;
        for (int l = i + 1, r = n - 1; l < r; l++, r--) { t = p[l]; p[l] = p[r]; p[r] = t; }
    }
    return list_set(&out);
}

NATIVE(n_sortseq) {
    UNUSED;
    Value *x = seq_of(seq_arg(a[0], "The first argument of SortSeq should be a natural number, but instead it is"));   /* sic, as TLC */
    Value *t = mk_tuple(x->n);
    for (int i = 0; i < x->n; i++) t->u.fcn.vals[i] = x->u.fcn.vals[i];
    for (int i = 1; i < t->n; i++) {
        Value *v = t->u.fcn.vals[i];
        int j = i - 1;
        while (j >= 0) {
            Value *pair[2] = {v, t->u.fcn.vals[j]};
            Value *r = apply_oper(a[1], pair, 2, call);
            if (r->kind != V_BOOL) fail_module("The second argument of SortSeq should be a function, but instead it is:\n%s", pretty(r));
            if (!r->u.i) break;
            t->u.fcn.vals[j + 1] = t->u.fcn.vals[j];
            j--;
        }
        t->u.fcn.vals[j + 1] = v;
    }
    return t;
}

/* Bags, as TLC's Bags class: a bag is a function its toFcnRcd takes,
   NULL for another value, whose values it casts to integers. */
static Value *bag_fcn(Value *b) {
    b = realize(b);
    return is_fcn(b) ? b : NULL;
}

static int64_t bag_count(Value *v) {
    if (v->kind != V_INT)
        fail("class tlc2.value.impl.%s cannot be cast to class tlc2.value.impl.IntValue (tlc2.value.impl.%s and "
             "tlc2.value.impl.IntValue are in unnamed module of loader 'app')", java_class(v), java_class(v));
    return v->u.i;
}

static int is_bag(Value *f) {
    for (int i = 0; i < f->n; i++) if (f->u.fcn.vals[i]->kind != V_INT || f->u.fcn.vals[i]->u.i <= 0) return 0;
    return 1;
}

/* The elements of a set its toSetEnum takes, NULL for another value. */
static Value *bag_set(Value *s) { return is_set(s) && !set_is_infinite(s) ? enumerate(s) : NULL; }

static _Noreturn void bag_wrong(const char *op, const char *what, Value *v) {
    fail_module("Applying %s to the following value,\nwhich is not %s:\n%s", op, what, pretty(v));
}

/* Adds count n of e to the bag in keys and vals, as TLC merges bags. */
static void bag_add(List *keys, List *vals, Value *e, Value *n) {
    for (int j = 0; j < keys->n; j++)
        if (veq(e, keys->v[j])) {
            int64_t x = bag_count(vals->v[j]), y = bag_count(n);
            vals->v[j] = mk_int(int_op(x, y, '+'));
            return;
        }
    list_add(keys, e);
    list_add(vals, n);
}

/* The count of e in bag f, NULL if e is not in its domain. */
static Value *bag_copies(Value *e, Value *f, const char *op) {
    for (int i = 0; i < f->n; i++)
        if (veq(e, fcn_key(f, i))) {
            Value *n = f->u.fcn.vals[i];
            if (n->kind != V_INT) fail_module("The second argument of %s should be a bag, but instead it is:\n%s", op, pretty(f));
            return n;
        }
    return NULL;
}

NATIVE(n_emptybag) { UNUSED; return mk_fcn(0); }

NATIVE(n_isabag) {
    UNUSED;
    Value *f = bag_fcn(a[0]);
    return BOOLV(f && is_bag(f));
}

NATIVE(n_bagcardinality) {
    UNUSED;
    Value *f = bag_fcn(a[0]);
    if (!f) bag_wrong("BagCardinality", "a function with a finite domain", a[0]);
    int64_t n = 0;
    for (int i = 0; i < f->n; i++) {
        Value *k = f->u.fcn.vals[i];
        if (k->kind != V_INT || k->u.i <= 0) bag_wrong("BagCardinality", "a bag", a[0]);
        n = int_op(n, k->u.i, '+');
    }
    return mk_int(n);
}

NATIVE(n_bagin) {
    UNUSED;
    Value *f = bag_fcn(a[1]);
    if (!f) fail("Cannot read field \"values\" because \"fcn\" is null");
    Value *n = bag_copies(a[0], f, "BagIn");
    return BOOLV(n && n->u.i > 0);
}

NATIVE(n_copiesin) {
    UNUSED;
    Value *f = bag_fcn(a[1]);
    if (!f) fail("Cannot read field \"values\" because \"fcn\" is null");
    Value *n = bag_copies(a[0], f, "CopiesIn");
    return n ? n : mk_int(0);
}

NATIVE(n_bagcup) {
    UNUSED;
    List keys = {0}, vals = {0};
    for (int k = 0; k < 2; k++) {
        Value *f = bag_fcn(a[k]);
        if (!f) fail("Cannot invoke \"tlc2.value.impl.Value.toFcnRcd()\" because \"b\" is null");
        if (!is_bag(f)) fail_module("The %s argument of (+) should be a bag, but instead it is:\n%s", k ? "second" : "first", pretty(a[k]));
    }
    for (int k = 0; k < 2; k++) {
        Value *f = bag_fcn(a[k]);
        for (int i = 0; i < f->n; i++) bag_add(&keys, &vals, fcn_key(f, i), f->u.fcn.vals[i]);
    }
    return mk_fcn_from(&keys, &vals);
}

NATIVE(n_bagdiff) {
    UNUSED;
    Value *f[2];
    for (int k = 0; k < 2; k++)
        if (!(f[k] = bag_fcn(a[k])))
            fail_module("The %s argument of (-) should be a bag, but instead it is:\n%s", k ? "second" : "first", pretty(a[k]));
    List keys = {0}, vals = {0};
    for (int i = 0; i < f[0]->n; i++) {
        int64_t n = bag_count(f[0]->u.fcn.vals[i]);
        for (int j = 0; j < f[1]->n; j++)
            if (veq(fcn_key(f[0], i), fcn_key(f[1], j))) { n -= bag_count(f[1]->u.fcn.vals[j]); break; }
        if (n > 0) { list_add(&keys, fcn_key(f[0], i)); list_add(&vals, mk_int(n)); }
    }
    return mk_fcn_from(&keys, &vals);
}

NATIVE(n_bagunion) {
    UNUSED;
    Value *s = bag_set(a[0]);
    if (!s) bag_wrong("BagUnion", "a finite enumerable set", a[0]);
    if (s->n == 0) return mk_fcn(0);
    if (s->n == 1) return s->u.set.elems[0];
    List keys = {0}, vals = {0};
    for (int i = 0; i < s->n; i++) {
        Value *f = bag_fcn(s->u.set.elems[i]);
        if (!f) fail_module("Attempted to apply BagUnion to the following set, whose\nelement is not a bag:\n%s", pretty(a[0]));
        for (int j = 0; j < f->n; j++) bag_add(&keys, &vals, fcn_key(f, j), f->u.fcn.vals[j]);
    }
    return mk_fcn_from(&keys, &vals);
}

NATIVE(n_sqsubseteq) {
    UNUSED;
    Value *f[2];
    for (int k = 0; k < 2; k++)
        if (!(f[k] = bag_fcn(a[k]))) bag_wrong("\\sqsubseteq", "a function with a finite domain", a[k]);
    for (int i = 0; i < f[0]->n; i++) {
        int64_t n = bag_count(f[0]->u.fcn.vals[i]);
        for (int j = 0; j < f[1]->n; j++)
            if (veq(fcn_key(f[0], i), fcn_key(f[1], j))) { n -= bag_count(f[1]->u.fcn.vals[j]); break; }
        if (n > 0) return FALSEV;
    }
    return TRUEV;
}

NATIVE(n_bagofall) {
    UNUSED;
    Value *f = bag_fcn(a[1]);
    if (!f) fail_module("The second argument of BagOfAll should be a function with a finite domain, but instead it is:\n%s", pretty(a[1]));
    List keys = {0}, vals = {0};
    for (int i = 0; i < f->n; i++) {
        Value *d = fcn_key(f, i);
        bag_add(&keys, &vals, apply_oper(a[0], &d, 1, call), f->u.fcn.vals[i]);
    }
    return mk_fcn_from(&keys, &vals);
}

NATIVE(n_bagtoset) {
    UNUSED;
    Value *f = bag_fcn(a[0]);
    if (!f) bag_wrong("BagToSet", "a function with a finite domain", a[0]);
    return fcn_domain(f);
}

NATIVE(n_settobag) {
    UNUSED;
    Value *s = bag_set(a[0]);
    if (!s) bag_wrong("BagToSet", "a function with a finite domain", a[0]);   /* sic */
    Value *f = mk_fcn(s->n);
    for (int i = 0; i < s->n; i++) { f->u.fcn.keys[i] = s->u.set.elems[i]; f->u.fcn.vals[i] = mk_int(1); }
    return f;
}

/* java.util.Random, the generator TLC draws from. */
typedef struct { uint64_t s; } JRandom;
#define JRANDOM(seed) {((uint64_t)(seed) ^ 0x5DEECE66DULL) & ((1ULL << 48) - 1)}

static void jr_seed(JRandom *r, int64_t seed) { *r = (JRandom)JRANDOM(seed); }

static int32_t jr_next(JRandom *r, int bits) {
    r->s = (r->s * 0x5DEECE66DULL + 0xB) & ((1ULL << 48) - 1);
    return (int32_t)(uint32_t)(r->s >> (48 - bits));
}

static int64_t jr_long(JRandom *r) {
    uint64_t hi = (uint64_t)(int64_t)jr_next(r, 32);
    return (int64_t)((hi << 32) + (uint64_t)(int64_t)jr_next(r, 32));
}

static double jr_double(JRandom *r) { return (double)(((int64_t)jr_next(r, 26) << 27) + jr_next(r, 27)) * 0x1.0p-53; }

/* Below bound, as nextInt(bound). */
static int jr_int(JRandom *r, int bound) {
    int32_t x = jr_next(r, 31), m = bound - 1;
    if (!(bound & m)) return (int)(((int64_t)bound * x) >> 31);
    for (int32_t u = x; (int32_t)((uint32_t)u - (uint32_t)(x = u % bound) + (uint32_t)m) < 0; u = jr_next(r, 31)) {}
    return x;
}

/* What RandomElement and the Randomization module draw from: TLC's
   RandomEnumerableValues, java.util.Random seeded with the seed. A
   simulation draws as TLC's threads do, from one for the model and the
   initial states and another for the behaviors. Model checking draws
   again for Init and for each state expanded, xored with the state's
   fingerprint so that a trace can be rebuilt; manyan's fingerprints are not
   TLC's, so there the draws are not TLC's. */
static JRandom draw_model, draw_behaviors, *drawing = &draw_model;
static int64_t draw_seed;
static Value **draw_from;   /* the state expanded, NULL for Init */
static int draw_due;        /* to seed at the next draw */
static uint64_t fingerprint(Value **st);

/* The generator as Init begins. TLC's main thread generates Init from the
   generator it made at its first draw, which a draw at startup made before
   the checker that would seed it for each state: Init goes on from the
   startup's draws. */
static JRandom init_draws;

static void draw_restart(Value **from) {
    draw_from = from;
    draw_due = from != NULL;
    if (!from) draw_model = init_draws;
}

static JRandom *draws(void) {
    if (in_worker && !draw_from) worker_cannot();   /* Init's draws go on in order */
    if (draw_due) jr_seed(drawing, draw_seed ^ (int64_t)(draw_from ? fingerprint(draw_from) : 0));
    draw_due = 0;
    return drawing;
}

/* A set of functions, records or tuples: TLC draws an element of each
   part's set. Its parts' sets, in its element's order, for n_parts. */
static int is_product(Value *s) { return s->kind == V_LAZY && (s->lazy == L_FCNSET || s->lazy == L_RCDSET || s->lazy == L_TIMES); }

static Value **product_parts(Value *s, int *n) {
    if (s->lazy != L_FCNSET) { *n = s->n; return s->u.l.names + s->n; }
    *n = enumerate(s->u.l.a)->n;
    Value **sets = NEWN(Value *, *n);
    for (int i = 0; i < *n; i++) sets[i] = s->u.l.b;
    return sets;
}

/* The element of product s whose parts are vals. */
static Value *product_element(Value *s, Value **vals) {
    Value *dom = s->lazy == L_FCNSET ? enumerate(s->u.l.a) : NULL;
    int n = dom ? dom->n : s->n;
    Value *t = s->lazy == L_TIMES ? mk_tuple(n) : mk_fcn(n);
    for (int i = 0; i < n; i++) {
        if (s->lazy != L_TIMES) t->u.fcn.keys[i] = dom ? dom->u.set.elems[i] : s->u.l.names[i];
        t->u.fcn.vals[i] = vals[i];
    }
    if (s->lazy == L_RCDSET) t->made = MADE_RECORD;
    if (s->lazy == L_FCNSET) t->range = s->u.l.a->kind == V_INTERVAL && n;
    return t;
}

/* A set to draw by index from: an interval as it is, as its i-th element
   lo + i need not be made; another enumerated. */
static Value *indexed(Value *s) {
    if (s->kind != V_INTERVAL) return enumerate(s);
    interval_size(s);
    return s;
}
static Value *element_at(Value *s, int64_t i) { return s->kind == V_INTERVAL ? mk_int(s->u.range.lo + i) : s->u.set.elems[i]; }

static Value *random_element(Value *s) {
    if (s->kind == V_SET && s->u.set.product) s = s->u.set.product;
    /* a set TLC cannot enumerate, as Nat, or functions from one */
    if (user_set(s) || (s->kind == V_LAZY && s->lazy == L_FCNSET && user_set(s->u.l.a)))
        fail_module("Applying RandomElement to the following value,\nwhich is not a finite set:\n%s", pretty(s));
    if (is_product(s) && !(s->lazy == L_FCNSET && set_is_infinite(s->u.l.a))) {
        int n;
        Value **sets = product_parts(s, &n), **vals = NEWN(Value *, n);
        for (int i = 0; i < n; i++) vals[i] = random_element(sets[i]);
        return product_element(s, vals);
    }
    Value *e = indexed(s);
    if (!e->n) fail_module("Attempted to compute RandomElement of the empty set.");
    return element_at(e, (int)(jr_double(draws()) * e->n));
}

NATIVE(n_randomelement) { UNUSED; return random_element(a[0]); }

/* The i-th of the 1341 primes from 1277011 on, TLC's RandomGenerator's. */
static int tlc_prime(int i) {
    static int primes[1341];
    if (!primes[0])
        for (int p = 1277011, k = 0; k < 1341; p += 2) {
            int prime = 1;
            for (int d = 3; d * d <= p && prime; d += 2) prime = p % d != 0;
            if (prime) primes[k++] = p;
        }
    return primes[i];
}

/* The increment of TLC's draws: one of its primes, at random. */
static int64_t random_prime(JRandom *r) {
    int i = 1341;
    while (i == 1341) i = (int)(jr_double(r) * 1341);
    return tlc_prime(i);
}

/* The modulus m and multiplier a of TLC's draws from n elements, for a
   period of m: the least m >= max(n, 9), not divisible by 4, with a square
   factor; a is 1 more than the product of m's prime factors. */
static void draw_params(int64_t n, int64_t *m, int64_t *a) {
    for (n = n < 9 ? 9 : n;; n++) {
        if (n % 4 == 0) continue;
        int64_t r = n, product = 1;
        int square = 0;
        for (int64_t p = 2; p * p <= r; p++) {
            if (r % p) continue;
            product *= p;
            r /= p;
            square |= r % p == 0;
            while (r % p == 0) r /= p;
        }
        if (r > 1) product *= r;
        if (square) { *m = n, *a = product + 1; return; }
    }
}

/* The elements of S in TLC's random order, as its draws of k of them
   (RandomSubset) and -generate's of all: indices from a linear
   congruential generator of a random seed and a random prime increment,
   whose period visits each index once. A set of functions, records or
   tuples is indexed in the mixed radix of its parts, the last the least
   significant; one too large for an int index has indices apart by a
   63-bit step from a random long. */
__extension__ typedef __int128 Big;
#define HUGE_INDEX ((Big)1 << 126)   /* above every index drawn */
typedef struct {
    Value *s, *e, **sets, **vals;   /* the set; it indexed, or the parts of a product */
    int n;
    Big size, idx, start;
    int64_t m, mult, inc, i;
} Order;

static void order_begin(Order *o, Value *s) {
    if (s->kind == V_SET && s->u.set.product) s = s->u.set.product;
    if (set_is_infinite(s)) count_infinite(s);   /* TLC counts the set first */
    *o = (Order){.s = s, .size = 1};
    if (is_product(s)) {
        Value **sets = product_parts(s, &o->n);
        o->sets = NEWN(Value *, o->n);
        o->vals = NEWN(Value *, o->n);
        for (int i = 0; i < o->n; i++) {
            o->sets[i] = indexed(sets[i]);
            o->size = o->size > HUGE_INDEX / (o->sets[i]->n + 1) ? HUGE_INDEX : o->size * o->sets[i]->n;
        }
    } else {
        o->e = indexed(s);
        o->size = o->e->n;
    }
    JRandom *r = draws();
    if (o->size > 2147483647) {
        int64_t l = jr_long(r);
        o->start = l < 0 && l != INT64_MIN ? -l : l;
    } else if (o->size > 0) {
        draw_params((int64_t)o->size, &o->m, &o->mult);
        o->start = jr_int(r, (int)o->size);
        o->inc = random_prime(r);
    }
    o->idx = o->start;
}

/* The next element: after the last, the first again. */
static Value *order_next(Order *o) {
    if (o->size > 2147483647) o->idx = ((Big)(INT64_MAX - 24) * o->i++ + o->start) % o->size;
    else do o->idx = (o->mult * o->idx + o->inc) % o->m; while (o->idx >= o->size);
    if (o->e) return element_at(o->e, (int64_t)o->idx);
    Big scale = 1;   /* of the last part, the least significant */
    for (int j = o->n - 1; j >= 0; j--) {
        int mod = o->sets[j]->n;
        o->vals[j] = element_at(o->sets[j], (int64_t)(o->idx / scale % mod));
        scale = scale > HUGE_INDEX / (mod + 1) ? HUGE_INDEX : scale * mod;
    }
    return product_element(o->s, o->vals);
}

NATIVE(n_randomsubset) {
    UNUSED;
    if (a[0]->kind != V_INT)
        fail_module("The first argument of RandomSubset should be a nonnegative integer, but instead it is:\n%s", pretty(a[0]));
    if (!is_set(a[1]) || set_is_infinite(a[1]))
        fail_module("The second argument of RandomSubset should be a a finite set, but instead it is:\n%s", pretty(a[1]));
    if (a[0]->u.i < 0) fail("%d", (int)a[0]->u.i);   /* Java's NegativeArraySizeException, sizing the subset */
    Order o;
    order_begin(&o, a[1]);
    List l = {0};
    for (int64_t i = 0; o.size > 0 && i < a[0]->u.i; i++) list_add(&l, order_next(&o));
    return list_set(&l);
}

/* k subsets of S, as TLC draws them: each element in with probability
   n / Cardinality(S). */
NATIVE(n_randomsetofsubsets) {
    UNUSED;
    for (int i = 0; i < 2; i++)
        if (a[i]->kind != V_INT || a[i]->u.i < 0)
            fail_module("The %s argument of RandomSetOfSubsets should be a nonnegative integer, but instead it is:\n%s",
                        i ? "second" : "first", pretty(a[i]));
    if (!is_set(a[2]) || set_is_infinite(a[2]))
        fail_module("The third argument of RandomSetOfSubsets should be a finite set, but instead it is:\n%s", pretty(a[2]));
    Value *s = enumerate(a[2]);
    int64_t k = a[0]->u.i, n = a[1]->u.i;
    if (s->n < 63 && k > ((int64_t)1 << s->n))
        fail_module("The first argument of RandomSetOfSubsets should be a nonnegative integer that is smaller than "
                    "the subset's size of 2^%d, but instead it is:\n%lld", s->n, (long long)k);
    if (n > s->n)
        fail_module("The second argument of RandomSetOfSubsets should be a nonnegative integer in range "
                    "0..Cardinality(S), but instead it is:\n%s", pretty(a[1]));
    double p = (double)n / s->n;
    JRandom *r = draws();
    List l = {0};
    for (int64_t j = 0; j < k; j++) {
        List sub = {0};
        for (int i = 0; i < s->n; i++) if (jr_double(r) < p) list_add(&sub, s->u.set.elems[i]);
        list_add(&l, list_set(&sub));
    }
    return list_set(&l);
}

NATIVE(n_any) { UNUSED; return mk_lazy(L_ANY); }

NATIVE(n_tostring) {
    UNUSED;
    char *s = value_str(printable(a[0]));
    return mk_str(intern(s));
}

NATIVE(n_tlceval) { UNUSED; return a[0]; }

/* TLCExt's operators. */
NATIVE(n_asserterror);   /* after the evaluation's saved state */

/* TLCCache(expression, closure): a constant expression's value is kept for
   each value of closure, as TLC keeps it in a table at the expression. One
   of a state is kept in the state, which the search's states cannot: TLC
   evaluates the closure and the expression, then the definition evaluates
   the expression again. A simulation's states can: an initial state keeps
   it for good, a later one for its behavior. One of an action is the
   definition's. */
static inline uint64_t elem_hash(Value *v);
static struct { Expr *e; Value **st; uint64_t key; Value *value; int behavior; } *tlc_cache;
static int ntlc_cache;
static Value **sim_initial;   /* the behavior's initial state, NULL before the first */

static void tlc_cache_add(Expr *x, Value **st, uint64_t key, Value *v, int behavior) {
    tlc_cache = xrealloc(tlc_cache, sizeof *tlc_cache * (size_t)(ntlc_cache + 1));
    tlc_cache[ntlc_cache].e = x, tlc_cache[ntlc_cache].st = st, tlc_cache[ntlc_cache].key = key;
    tlc_cache[ntlc_cache].value = v, tlc_cache[ntlc_cache++].behavior = behavior;
}

/* A behavior from initial state st begins: the last one's states are gone. */
static void tlc_cache_behavior(Value **st) {
    int n = 0;
    for (int i = 0; i < ntlc_cache; i++) if (!tlc_cache[i].behavior) tlc_cache[n++] = tlc_cache[i];
    ntlc_cache = n;
    sim_initial = st;
}

NATIVE(n_tlccache) {
    UNUSED;
    if (a) return a[0];
    Expr *x = call->args[0];
    int level = expr_level(x);
    if (level > 1) return eval(x, c);
    uint64_t key = elem_hash(eval(call->args[1], c));
    Value **st = level ? cur_state : NULL;
    if (st && !simulating) eval(x, c);
    if (st && (!simulating || gen_init)) return eval(x, c);
    for (int i = 0; i < ntlc_cache; i++)
        if (tlc_cache[i].e == x && tlc_cache[i].st == st && tlc_cache[i].key == key) return tlc_cache[i].value;
    if (in_worker) worker_cannot();
    Value *v = eval(x, c);
    if (st && sim_initial && st != sim_initial) {   /* the behavior's arena keeps it */
        tlc_cache_add(x, st, key, v, 1);
        return v;
    }
    Arena *saved = arena;
    arena = &perm_arena;
    long budget = INT64_MAX;
    Value *kept = copy_value(v, &budget);
    arena = saved;
    if (!kept) return v;
    tlc_cache_add(x, st, key, kept, 0);
    return kept;
}

NATIVE(n_tlcmodelvalue) {
    UNUSED;
    if (a[0]->kind != V_STR) fail_module("The argument of ModelValue should be a string, but instead it is:\n%s", pretty(a[0]));
    return mk_model((int)a[0]->u.i);
}

/* TLCGetOrDefault(i, d): register i, or d when nothing is kept there. */
NATIVE(n_tlcgetordefault) {
    UNUSED;
    if (a[0]->kind != V_INT || starting || a[0]->u.i < 0 || a[0]->u.i >= nregisters || !registers[a[0]->u.i].n) return a[1];
    const char *p = registers[a[0]->u.i].s;
    return decode(&p);
}

static Value *trace_value(void);
NATIVE(n_trace) { UNUSED; return trace_value(); }

/* TLCExt's operators that need TLC's own traces, fingerprints or successors. */
static _Noreturn void unsupported(const char *op) {
    if (in_worker) worker_cannot();
    fflush(stdout);
    fprintf(stderr, "manyan: %s is not supported\n", op);
    exit(MANYAN_ERROR);
}
#define UNSUPPORTED(fn, op) NATIVE(fn) { UNUSED; unsupported(op); }
/* TLCExt's CounterExample: in a postcondition checked after an error,
   the behavior TLC reports it with (post_behavior), else none. Its
   states are numbered from 1, and each step names its action; a lasso's
   last state steps back to state loop (from 1), by loop_act. Its states
   are the ALIAS's where TLC gives them so, aliased: 1 evaluated as the
   error is reported, as TLC does for a trace even with no postcondition;
   2 when CounterExample is, where TLC uses those it printed. */
static struct { Value ***st, **rec; int *act, n, loop, loop_act, aliased; Value *value; } post_trace;
static void post_behavior(Value ***st, const int *act, int n, int loop, int loop_act, int aliased);
static Value *counter_example(void);
static Value *counter_trace(Value *ce);
NATIVE(n_counterexample) { UNUSED; return counter_example(); }
NATIVE(n_totrace) { UNUSED; return counter_trace(a[0]); }
NATIVE(n_picksuccessor);   /* after the search */
static int npicked_explored;
UNSUPPORTED(n_tlcfp, "TLCFP")

/* TLCDefer(e): TRUE. A simulation evaluates e once it picks the successor
   being made, where e was met, as TLC's worker calls the callable its
   working state keeps: the last one met, from where the successor before
   was emitted. Model checking keeps none. */
typedef struct { Expr *e; Ctx c; Value **st; int primed; } Defer;
static Defer sim_defer;
NATIVE(n_tlcdefer) {
    UNUSED;
    if (!a && simulating && !gen_init)
        sim_defer.e = call->args[0], sim_defer.c = c, sim_defer.st = cur_state, sim_defer.primed = next_state != NULL;
    return TRUEV;
}

/* TLCEvalDefinition(name): the body of the root module's definition of
   that name without parameters, as written: the configuration replaces
   it, or TLC's Java gives it, only where it is called by name. */
static Value *fcndef_value(Def *d, Ctx c);
static Module *root;
NATIVE(n_tlcevaldefinition) {
    UNUSED;
    if (a) return TRUEV;
    Value *v = eval(call->args[0], c);
    if (v->kind != V_STR)
        fail("The argument of TLCEvalDefinition should be a string, but instead it is:\n%s", pretty(v));
    Module *m = root;
    Inst *inst = NULL;
    Def *d = NULL;
    for (const char *s = S((int)v->u.i), *bang; s; s = bang ? bang + 1 : NULL) {
        bang = strchr(s, '!');
        Sym *sym = m ? module_lookup(m, bang ? intern_n(s, (int)(bang - s)) : intern(s)) : NULL;
        d = sym && (m == root || !sym->local) ? sym->def : NULL;
        for (int k = 0; d && k < sym->npath; k++) {
            Inst *in = NEW(Inst);
            in->def = sym->path[k], in->parent = inst, inst = in;
        }
        if (d && bang && d->kind == D_INST && !d->nparams) {
            Inst *in = NEW(Inst);
            in->def = d, in->parent = inst, inst = in;
            m = d->target;
        } else if (bang) d = NULL;
        if (!d) break;
    }
    if (!d || (d->kind != D_OP && d->kind != D_FCN && d->kind != D_RECURSIVE))
        fail("The argument of TLCEvalDefinition should be a name of a definition reachable from the root module, but instead it is:\n%s", pretty(v));
    if (d->nparams) {
        Buf b = {0};
        for (int i = 0; i < d->nparams; i++) buf_printf(&b, "%s%s", i ? ", " : "", S(d->params[i]->name));
        fail("The argument of TLCEvalDefinition should be a a zero-arity definition, but instead it is:\n%s(%s)", S(d->name), b.s);
    }
    Ctx dc = {NULL, inst};
    return d->kind == D_FCN ? fcndef_value(d, dc) : eval_body(d->body, dc);
}

/* Java's names of TLC's value classes, for its methods' signatures. */
#define J_V "tlc2.value.impl.Value"
#define J_I "tlc2.value.impl.IntValue"
#define J_IV "tlc2.value.impl.IntervalValue"
#define J_B "tlc2.value.IBoolValue"
/* An evaluation method's, which takes its arguments unevaluated. */
#define J_EVAL "tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context," \
               "tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel"

/* Each native operator, with the Java method TLC implements it by. */
static const struct { const char *module, *name; Native fn; const char *ret, *method; } natives[] = {
    {"Naturals", "Nat", n_nat, J_V, "Nat()"},
    {"Naturals", "+", n_plus, J_I, "Plus(" J_I "," J_I ")"},
    {"Naturals", "-", n_minus, J_I, "Minus(" J_I "," J_I ")"},
    {"Naturals", "*", n_times, J_I, "Times(" J_I "," J_I ")"},
    {"Naturals", "^", n_pow, J_I, "Expt(" J_I "," J_I ")"},
    {"Naturals", "<", n_lt, J_B, "LT(" J_V "," J_V ")"},
    {"Naturals", ">", n_gt, J_B, "GT(" J_V "," J_V ")"},
    {"Naturals", "\\leq", n_leq, J_B, "LE(" J_V "," J_V ")"},
    {"Naturals", "\\geq", n_geq, J_B, "GEQ(" J_V "," J_V ")"},
    {"Naturals", "%", n_mod, J_I, "Mod(" J_I "," J_I ")"},
    {"Naturals", "\\div", n_div, J_I, "Divide(" J_I "," J_I ")"},
    {"Naturals", "..", n_range, J_IV, "DotDot(" J_I "," J_I ")"},
    {"Integers", "Int", n_int, J_V, "Int()"},
    {"Integers", "-.", n_neg, J_I, "Neg(" J_I ")"},
    {"Sequences", "Seq", n_seq, J_V, "Seq(" J_V ")"},
    {"Sequences", "Len", n_len, J_I, "Len(" J_V ")"},
    {"Sequences", "\\o", n_concat, J_V, "Concat(" J_V "," J_V ")"},
    {"Sequences", "Append", n_append, J_V, "Append(" J_V "," J_V ")"},
    {"Sequences", "Head", n_head, J_V, "Head(" J_V ")"},
    {"Sequences", "Tail", n_tail, J_V, "Tail(" J_V ")"},
    {"Sequences", "SubSeq", n_subseq, J_V, "SubSeq(" J_V "," J_V "," J_V ")"},
    {"Sequences", "SelectSeq", n_selectseq, J_V, "SelectSeq(" J_V "," J_V ")"},
    {"FiniteSets", "IsFiniteSet", n_isfinite, J_B, "IsFiniteSet(" J_V ")"},
    {"FiniteSets", "Cardinality", n_cardinality, J_I, "Cardinality(" J_V ")"},
    {"Bags", "EmptyBag", n_emptybag, J_V, "EmptyBag()"},
    {"Bags", "IsABag", n_isabag, J_B, "IsABag(" J_V ")"},
    {"Bags", "BagCardinality", n_bagcardinality, J_I, "BagCardinality(" J_V ")"},
    {"Bags", "BagIn", n_bagin, J_B, "BagIn(" J_V "," J_V ")"},
    {"Bags", "CopiesIn", n_copiesin, J_I, "CopiesIn(" J_V "," J_V ")"},
    {"Bags", "\\oplus", n_bagcup, J_V, "BagCup(" J_V "," J_V ")"},
    {"Bags", "\\ominus", n_bagdiff, J_V, "BagDiff(" J_V "," J_V ")"},
    {"Bags", "BagUnion", n_bagunion, J_V, "BagUnion(" J_V ")"},
    {"Bags", "\\sqsubseteq", n_sqsubseteq, J_B, "SqSubseteq(" J_V "," J_V ")"},
    {"Bags", "BagOfAll", n_bagofall, J_V, "BagOfAll(" J_V "," J_V ")"},
    {"Bags", "BagToSet", n_bagtoset, J_V, "BagToSet(" J_V ")"},
    {"Bags", "SetToBag", n_settobag, J_V, "SetToBag(" J_V ")"},
    {"TLCExt", "AssertError", n_asserterror, "synchronized " J_V, "assertError(" J_EVAL ")"},
    {"TLCExt", "TLCCache", n_tlccache, J_V, "tlcEval2(" J_EVAL ")"},
    {"TLCExt", "TLCModelValue", n_tlcmodelvalue, "synchronized " J_V, "tlcModelValue(" J_V ")"},
    {"TLCExt", "TLCGetOrDefault", n_tlcgetordefault, J_V, "tlcGetOrDefault(" J_V "," J_V ")"},
    {"TLCExt", "Trace", n_trace, J_V, "getTrace(" J_EVAL ")"},
    {"TLCExt", "CounterExample", n_counterexample, J_V, "error(" J_EVAL ")"},
    {"TLCExt", "ToTrace", n_totrace, J_V, "lassoOrdinal(" J_V ")"},
    {"TLCExt", "TLCDefer", n_tlcdefer, J_V, "tlcDefer(" J_EVAL ")"},
    {"TLCExt", "PickSuccessor", n_picksuccessor, "synchronized " J_V, "pickSuccessor(" J_EVAL ")"},
    {"TLCExt", "TLCFP", n_tlcfp, J_V, "tlcFingerprint(" J_V ")"},
    {"TLCExt", "TLCEvalDefinition", n_tlcevaldefinition, J_V, "tlcDefByName(" J_EVAL ")"},
    {"TLC", "Print", n_print, J_V, "Print(" J_V "," J_V ")"},
    {"TLC", "PrintT", n_printt, J_V, "PrintT(" J_V ")"},
    {"TLC", "Assert", n_assert, J_V, "Assert(" J_V "," J_V ")"},
    {"TLC", "JavaTime", n_javatime, J_V, "JavaTime()"},
    {"TLC", "TLCGet", n_tlcget, J_V, "TLCGetSet.TLCGetEval(" J_EVAL ")"},
    {"TLC", "TLCSet", n_tlcset, J_V, "TLCSet(" J_V "," J_V ")"},
    {"TLC", ":>", n_singleton, J_V, "MakeFcn(" J_V "," J_V ")"},
    {"TLC", "@@", n_merge, J_V, "CombineFcn(" J_V "," J_V ")"},
    {"TLC", "Permutations", n_permutations, J_V, "Permutations(" J_V ")"},
    {"TLC", "SortSeq", n_sortseq, J_V, "SortSeq(" J_V "," J_V ")"},
    {"TLC", "RandomElement", n_randomelement, J_V, "RandomElement(" J_V ")"},
    {"TLC", "Any", n_any, J_V, "Any()"},
    {"Randomization", "RandomSubset", n_randomsubset, J_V, "RandomSubset(" J_V "," J_V ")"},
    {"Randomization", "RandomSetOfSubsets", n_randomsetofsubsets, J_V, "RandomSetOfSubsets(" J_V "," J_V "," J_V ")"},
    {"TLC", "ToString", n_tostring, J_V, "ToString(" J_V ")"},
    {"TLC", "TLCEval", n_tlceval, J_V, "TLCEval(" J_V ")"},
    {NULL, NULL, NULL, NULL, NULL}};

/* The number of arguments of a native's Java method; an evaluation
   method's operator takes any number, -1. */
static int native_arity(const char *method) {
    if (strstr(method, "ExprOrOpArgNode[]")) return -1;
    const char *p = strchr(method, '(');
    int n = p[1] != ')';
    for (; *p; p++) n += *p == ',';
    return n;
}

static char native_intop(Native f) {
    return f == n_lt ? '<' : f == n_leq ? 'l' : f == n_gt ? '>' : f == n_geq ? 'g'
         : f == n_plus ? '+' : f == n_minus ? '-' : f == n_times ? '*' : 0;
}

/* Attaches the native operators to the modules of the standard modules'
   names, as TLC loads its classes by the module's name: one the user
   supplies too, where an operator of the native's arity is the native. */
static void bind_natives(void) {
    for (int i = 0; i < nmodules; i++) {
        Module *m = modules[i];
        for (int u = 0; u < m->nunits; u++) {
            Def *d = m->units[u].def;
            if (m->units[u].kind != 0 || !d) continue;
            for (int k = 0; natives[k].module; k++)
                if (strcmp(natives[k].module, S(m->name)) == 0 && strcmp(natives[k].name, S(d->name)) == 0
                    && (native_arity(natives[k].method) < 0 || d->nparams == native_arity(natives[k].method))) {
                    d->native = natives[k].fn;
                    d->lazy = native_arity(natives[k].method) < 0;
                    d->intop = native_intop(d->native);
                    /* TLC loads Integers for the trace spec it sets up, which
                       -continue skips, and then takes Naturals' operators from
                       its class; a method may name its own class in tlc2.module,
                       or a class elsewhere in full. */
                    const char *m = natives[k].method;
                    const char *cls = !strcmp(natives[k].module, "Naturals") && !keep_going ? "Integers" : natives[k].module;
                    int named = memchr(m, '.', (size_t)(strchr(m, '(') - m)) != NULL, full = !strncmp(m, "tlc2.", 5);
                    Buf b = {0};
                    buf_printf(&b, "public static %s %s%s%s%s", natives[k].ret, full ? "" : "tlc2.module.",
                               named ? "" : cls, named ? "" : ".", m);
                    d->java = buf_take(&b);
                }
            for (int k = 0; k < ndefined; k++)
                if (!strcmp(defined[k].module, S(m->name)) && !strcmp(defined[k].name, S(d->name))
                    && (defined[k].arity == MANYAN_LAZY || d->nparams == defined[k].arity)) {
                    d->native = n_defined, d->api = defined[k].fn;
                    d->lazy = defined[k].arity == MANYAN_LAZY;
                    d->java = defined[k].java;
                }
        }
    }
}

/* ---------------------------------------------------------------- generator */

/* TLC's random generator of behaviors, counting its doubles (aril). */
static JRandom rng;
static int64_t rng_aril;

static void rng_seed(int64_t seed) {
    jr_seed(&rng, seed);
    rng_aril = 0;
}

/* An index below n, as TLC draws one: floor(nextDouble() * n). */
static int rng_index(int n) {
    rng_aril++;
    return (int)(jr_double(&rng) * n);   /* >= 0: truncation is floor */
}

/* One of TLC's primes, its step through the actions. */
static int rng_prime(void) {
    int i = 1341;
    while (i == 1341) i = rng_index(1341);
    return tlc_prime(i);
}

/* The generator enumerates the assignments an initial predicate or an
   action allows (§10.2, §10.3). Conjuncts still to be satisfied wait in a
   continuation. */
typedef struct Cont { Expr *e; Ctx c; struct Cont *next; int unchanged; } Cont;   /* unchanged: the conjunct is UNCHANGED e */

static int (*gen_emit)(void);   /* called with each complete assignment; nonzero stops */
static long generated;          /* states generated, as TLC counts them */

/* -generate: TLC builds a behavior's successor by random choices, of a
   disjunct, a binding or a value, each ending once a successor is kept. */
static int generating;
static int sim_succ_emit(void);
static int sim_kept(void);
static int choosing(void) { return generating && gen_emit == sim_succ_emit; }

static inline int gen(Expr *e, Ctx c, Cont *k);
static int gen_unchanged(Expr *e, Ctx c, Cont *k);

static _Noreturn void not_boolean(Expr *e, Value *v);
static int enabled_emit(void);

static int gen_cont(Cont *k) {
    if (!k) return gen_emit();
    int assigned = 1;
    for (int i = 0; i < nvars && assigned; i++) assigned = gen_target[i] != NULL;
    if (!assigned || gen_emit == enabled_emit) return k->unchanged ? gen_unchanged(k->e, k->c, k->next) : gen(k->e, k->c, k->next);
    /* Once every variable has a value, TLC evaluates the remaining
       conjuncts as formulas, but not in ENABLED: a disjunction stops at
       its first true disjunct. */
    for (; k; k = k->next) {
        Value *v = k->unchanged ? BOOLV(kept(k->e, k->c)) : eval(k->e, k->c);
        if (v->kind != V_BOOL) not_boolean(k->e, v);
        if (!v->u.i) return 0;
    }
    return gen_emit();
}

/* Init sliced among the workers. Each alternative of the first
   slice_depth choices of a path (an element of x \in S, a disjunct, a
   binding of \E) is numbered in the order one process takes them, and the
   states found under one are its slice. A process takes the alternatives
   of the slice_depth-th choice, and keeps the states, only of the slices
   in [slice_lo, slice_hi). Counting, it takes them all, but stops at the
   choice after, noting that there is one. */
static int slicing, slice_counting, slice_deeper, slice_depth, choice_depth;
static long slice_seq, slice_lo, slice_hi;

static int slice_owned(void) { return slice_seq >= slice_lo && slice_seq < slice_hi; }

/* Entering a choice: 0 if counting stops at it. */
static int choice_begin(void) {
    if (slice_counting && choice_depth == slice_depth) { slice_deeper = 1; return 0; }
    choice_depth++;
    return 1;
}

/* Whether to take the next alternative of the choice entered last. */
static int choice_take(void) {
    int d = choice_depth - 1;
    if (d >= slice_depth) return 1;
    slice_seq++;
    return d < slice_depth - 1 || slice_counting || slice_owned();
}

static Cont *mk_cont(Expr *e, Ctx c, Cont *next) {
    Cont *k = NEW(Cont);
    k->e = e; k->c = c; k->next = next;
    return k;
}

/* A variable reached from where ENABLED marks the chain, not through an
   argument from outside, is bound by name, in a slot past the state's own
   when no state variable has that name. */
static int enabled_names[16], nenabled_names;

static int enabled_slot(Def *d) {
    for (int i = 0; i < nvars; i++) if (vars[i]->name == d->name) return i;
    for (int i = 0; i < nenabled_names; i++) if (enabled_names[i] == d->name) return nvars + i;
    if (nenabled_names == 16) return -1;
    enabled_names[nenabled_names] = d->name;
    return nvars + nenabled_names++;
}

/* The evaluation globals, which a caller that goes on after an error
   restores. */
typedef struct {
    sigjmp_buf *handler;
    Arena *arena;
    Value **cur_state, **next_state, **gen_target, *at_value;
    int (*gen_emit)(void);
    int primed, gen_init, nenabled_names, java_depth, eval_depth, keep_lazy, fp_depth, nregions, nframes;
} EvalState;

static EvalState eval_save(void) {
    return (EvalState){handler, arena, cur_state, next_state, gen_target, at_value, gen_emit,
                       primed, gen_init, nenabled_names, java_depth, eval_depth, keep_lazy, fp_depth, nregions, nframes};
}

static void eval_restore(EvalState s) {
    handler = s.handler; arena = s.arena;
    cur_state = s.cur_state; next_state = s.next_state; gen_target = s.gen_target; at_value = s.at_value;
    gen_emit = s.gen_emit;
    primed = s.primed; gen_init = s.gen_init; nenabled_names = s.nenabled_names;
    java_depth = s.java_depth; eval_depth = s.eval_depth; keep_lazy = s.keep_lazy; fp_depth = s.fp_depth;
    nregions = s.nregions; nframes = s.nframes;
}

/* The error being reported, which an evaluation whose own error is
   forgotten keeps. */
typedef struct { Buf msg; Expr *expr; int status, module, stackless; } ErrorState;

static ErrorState error_save(void) {
    ErrorState e = {{0}, error_expr, error_status, error_module, stackless};
    buf_puts(&e.msg, error_message.s ? error_message.s : "");
    return e;
}

static void error_restore(ErrorState *e) {
    error_reset();
    buf_puts(&error_message, e->msg.s);
    free(e->msg.s);
    error_expr = e->expr, error_status = e->status, error_module = e->module, stackless = e->stackless;
}

/* AssertError(err, exp): whether evaluating exp fails
   with the message err, as TLC's method catches its EvalException before
   the preambles of the operators outside are added. A worker leaves it to
   the search, which tells a real error from one only it can avoid. */
NATIVE(n_asserterror) {
    UNUSED;
    if (a) return FALSEV;   /* its arguments evaluated */
    Expr *err = call->args[0];
    if (err->kind != X_STR) {
        fail("In computing AssertError, a non-string expression (%s) was used as the err of an AssertError(err, exp).", node_str(err));
    }
    if (in_worker) worker_cannot();
    EvalState s = eval_save();
    ErrorState saved = error_save();
    sigjmp_buf here;
    handler = &here;
    java_depth = 0;
    int failed = sigsetjmp(here, 0);
    if (!failed) eval(call->args[1], c);
    else if (error_java) { eval_restore(s); free(saved.msg.s); raise_error(); }   /* Java's own exception */
    int same = failed && !strcmp(error_message.s ? error_message.s : "", S((int)err->num));
    eval_restore(s);
    error_restore(&saved);
    return BOOLV(same);
}

/* A lazy function as TLC prints it: computed in full if it can be, else
   as its definition, the error forgotten (§6.6). A worker gives the state
   back instead, as the error may be one only the search can avoid. */
static Value *try_realize(Value *f) {
    if (in_worker || set_is_infinite(f->u.l.a)) return realize(f);
    EvalState s = eval_save();
    ErrorState e = error_save();
    Value *volatile r = f;
    sigjmp_buf here;
    handler = &here;
    if (!sigsetjmp(here, 0)) r = realize(r);
    eval_restore(s);
    error_restore(&e);
    return r;
}

static void print_lambda(Buf *b, Value *f) {
    Bound *bs = f->u.l.binder ? f->u.l.binder->bounds : f->u.l.expr->bounds;
    int nb = f->u.l.binder ? f->u.l.binder->nb : f->u.l.expr->nb;
    int total = bounds_total(bs, nb), k = 0;
    buf_puts(b, "[");
    for (int i = 0; i < nb; i++) {
        if (i) buf_puts(b, ", ");
        if (bs[i].tuple) {
            buf_puts(b, "<<");
            for (int j = 0; j < bs[i].n; j++) buf_printf(b, "%s%s", j ? ", " : "", S(bs[i].names[j]));
            buf_puts(b, ">>");
        } else {
            buf_puts(b, S(bs[i].names[0]));
        }
        buf_puts(b, " \\in ");
        print_value(b, total == 1 ? f->u.l.a : f->u.l.a->u.l.names[total + k]);
        k += bs[i].tuple ? 1 : bs[i].n;
    }
    buf_puts(b, " |-> <expression ");
    node_text(b, f->u.l.binder ? f->u.l.binder->body : f->u.l.expr->args[0]);
    buf_puts(b, ">]");
}

/* A filter of a set TLC cannot enumerate, as it prints one: a tuple of
   names without its brackets. */
static void print_filter(Buf *b, Value *s) {
    Bound *bound = &s->u.l.expr->bounds[0];
    buf_puts(b, "{");
    for (int j = 0; j < bound->n; j++) buf_printf(b, "%s%s", j ? ", " : "", S(bound->names[j]));
    buf_puts(b, " \\in ");
    print_value(b, s->u.l.a);
    buf_puts(b, " : <expression ");
    node_text(b, s->u.l.expr->args[0]);
    buf_puts(b, "> }");
}

/* Binds the bounds bs over dom (as bounds_domain makes it) to the
   argument a, with TLC's checks: 0, or 1 if a part is outside its set and
   2 if it is not a tuple where one is needed, that part being *argno (0:
   the only one, -1: the whole argument). */
static int bind_arg(Bound *bs, int nb, Value *dom, Value *a, Env **env, int *argno) {
    int total = bounds_total(bs, nb), k = 0;
    *argno = total == 1 ? 0 : -1;
    Value **parts = &a;
    if (total > 1) {
        if (!is_fcn(a) || !fcn_is_tuple(a) || a->n < total) return 2;
        parts = a->u.fcn.vals;
    }
    for (int i = 0; i < nb; i++) {
        Bound *b = &bs[i];
        for (int j = 0; j < (b->tuple ? 1 : b->n); j++, k++) {
            Value *part = parts[k], *set = total == 1 ? dom : dom->u.l.names[total + k];
            if (total > 1) *argno = k + 1;
            if (!set_member(part, set)) return b->tuple && total > 1 ? 3 : 1;
            if (!b->tuple) { *env = mk_binding(b->defs[j], part, *env); continue; }
            if (!is_fcn(part) || !fcn_is_tuple(part) || part->n != b->n) return 2;
            for (int m = 0; m < b->n; m++) *env = mk_binding(b->defs[m], part->u.fcn.vals[m], *env);
        }
    }
    return 0;
}

static _Noreturn void lambda_outside(Value *f, Value *a, int why, int argno, Expr *where) {
    char part[48];
    if (argno == 0) snprintf(part, sizeof part, "the first argument");
    else if (argno < 0) snprintf(part, sizeof part, "the argument list");
    else snprintf(part, sizeof part, "the argument number %d", argno);
    if (argno > 0) a = a->u.fcn.vals[argno - 1];
    const char *wrong = why == 2 ? "which does not match its formal parameter." : "which is not in its domain.";
    if (!where && why == 1 && argno > 0) {   /* a part of several outside its set: TLC names the whole domain */
        const char *dom = pretty(enumerate(f->u.l.a));
        fail_module("In applying the function\n%s,\n%s is:\n%s\nwhich is not in the function's domain %s.\n", pretty(f), part, pretty(a), dom);
    }
    if (!where) fail_module("In applying the function\n%s,\n%s is:\n%s\n%s\n", pretty(f), part, pretty(a), wrong);
    /* Computing states, TLC binds the argument itself (Tool.getFcnContext). */
    if (argno < 0) fail("Attempted to apply a function to an argument not in its domain.\n%s", loc_str(where));
    fail("In applying the function\n%s,\n%s is:\n%s%s%s\n%s", pretty(f), argno || why != 2 ? part : "the argument",
         pretty(a), why == 3 ? "\n" : "", wrong, loc_str(where));
}

/* The variable an expression assigns: v (initial predicate) or v'
   (action), through operator parameters, definitions, LET and instance
   substitutions that stand for it, as TLC's getPrimedVar and getVar;
   -1 if none. */
static Ctx instance_ctx(Expr *e, Ctx c);
static int assignable(Expr *lhs, Ctx c) {
    for (int prime = gen_init;;) {   /* an initial predicate has no prime */
        Def *d = lhs->def;
        if (lhs->kind == K_PRIME && !prime) {
            prime = 1;
            lhs = lhs->args[0];
        } else if (lhs->kind == K_BOUND || (lhs->kind == K_CALL && lhs->n == 0)) {
            if (lhs->kind == K_BOUND || d->kind == D_PARAM || d->local == 2) {
                Env *b = env_find(c.env, d);
                if (!b || !b->e) return -1;
                lhs = b->e;
                c = (Ctx){b->ctx_env, b->ctx_inst};
            } else if (d->kind == D_OP && !d->native && !d->nparams && !d->replacement) {
                lhs = d->body;
                c = (Ctx){NULL, c.inst};
            } else {
                return -1;
            }
        } else if (lhs->kind == K_INSTCALL && lhs->n == 0 && d->kind == D_OP && !d->native) {
            c = instance_ctx(lhs, c);
            lhs = d->body;
        } else if (lhs->kind == X_LET && !prime) {
            Env *env = c.env;
            for (int i = 0; i < lhs->ndefs; i++)
                if (!lhs->defs[i]->nparams) env = mk_thunk(lhs->defs[i], lhs->defs[i]->body, c, env);
            for (Env *t = env; t != c.env; t = t->next) t->ctx_env = env;
            c.env = env;
            lhs = lhs->args[0];
        } else if (lhs->kind == K_DECL && prime) {
            Expr *sub = NULL;
            Ctx outer = c;
            for (Inst *in = c.inst; in && !sub; in = in->parent) {
                if (in->def == &enabled_mark) return d->kind == D_VAR ? enabled_slot(d) : -1;
                int i = subst_index(in->def, d);
                if (i >= 0) { sub = in->def->subst_expr[i]; outer = (Ctx){in->env, in->parent}; }
            }
            if (!sub) return d->kind == D_VAR ? d->var_index : -1;
            lhs = sub;
            c = outer;
        } else {
            return -1;
        }
    }
}

static int gen_assign(int var, Value *v, Cont *k) {
    gen_target[var] = v;
    int r = gen_cont(k);
    gen_target[var] = NULL;
    return r;
}

typedef struct { Expr *body; Cont *k; } GenData;

static int gen_bound_fn(Ctx c, void *data) {
    GenData *g = data;
    if (slicing && !choice_take()) return 0;
    return gen(g->body, c, g->k);
}

/* \E as -generate takes it: each variable's set in its random order, all
   drawn first, the first varying fastest. */
static int gen_exists_random(Expr *e, Ctx c, Cont *k) {
    int total = bounds_total(e->bounds, e->nb), empty = 0;
    Order *o = NEWN(Order, total);
    Bound **owner = NEWN(Bound *, total);
    int *slot = NEWN(int, total);
    Value **cur = NEWN(Value *, total);
    Big *at = NEWN(Big, total);
    for (int i = 0, j = 0; i < e->nb; i++) {
        Value *s = bound_value(&e->bounds[i], c);
        for (int m = 0; m < (e->bounds[i].tuple ? 1 : e->bounds[i].n); m++, j++) {
            owner[j] = &e->bounds[i], slot[j] = m;
            order_begin(&o[j], s);
            empty |= !o[j].size;
        }
    }
    if (empty) return 0;
    for (int j = 0; j < total; j++) cur[j] = order_next(&o[j]);
    for (;;) {
        Env *env = c.env;
        for (int j = 0; j < total; j++) {
            Bound *b = owner[j];
            Value *v = cur[j];
            if (!b->tuple) { env = mk_binding(b->defs[slot[j]], v, env); continue; }
            if (!is_fcn(v) || !fcn_is_tuple(v) || v->n != b->n)
                fail("Argument mismatch in operator application.%%1");   /* sic, as for_bindings */
            for (int m = 0; m < b->n; m++) env = mk_binding(b->defs[m], v->u.fcn.vals[m], env);
        }
        int r = gen(e->args[0], (Ctx){env, c.inst}, k);
        if (r || sim_kept()) return r;
        int j = 0;
        for (; j < total; j++) {
            cur[j] = order_next(&o[j]);
            if (++at[j] < o[j].size) break;
            at[j] = 0;
        }
        if (j == total) return 0;
    }
}

/* The bindings of a quantifier, in the arena. */
typedef struct { Ctx *v; int n, cap; } Ctxs;

static int collect_fn(Ctx c, void *data) {
    Ctxs *l = data;
    if (l->n == l->cap) {
        Ctx *v = NEWN(Ctx, l->cap = l->cap ? 2 * l->cap : 8);
        if (l->n) memcpy(v, l->v, sizeof(Ctx) * (size_t)l->n);
        l->v = v;
    }
    l->v[l->n++] = c;
    return 0;
}

/* UNCHANGED e: each variable of e keeps its value. */
/* Whether e' = e, comparing each variable with the value it has been
   assigned: in ENABLED, a variable of an instance by name, as TLC does. */
static int unchanged_now(Expr *e, Ctx c) {
    if (e->kind == X_TUPLE) {
        for (int i = 0; i < e->n; i++) if (!unchanged_now(e->args[i], c)) return 0;
        return 1;
    }
    if (e->kind == K_CALL && e->n == 0 && e->def->kind == D_OP && !e->def->native && e->def->local != 2)
        return unchanged_now(e->def->body, (Ctx){NULL, c.inst});
    if (e->kind == K_DECL) {
        Expr prime = {.kind = K_PRIME, .n = 1, .args = &e};
        int var = assignable(&prime, c);
        if (var >= 0 && gen_target[var]) return veq(eval(e, c), gen_target[var]);
    }
    Value *now = eval(e, c);
    int saved = primed;
    primed = 1;
    Value *then = eval(e, c);
    primed = saved;
    return veq(now, then);
}

static int gen_unchanged(Expr *e, Ctx c, Cont *k) {
    if (e->kind == X_TUPLE) {
        for (int i = e->n - 1; i >= 1; i--) {
            k = mk_cont(e->args[i], c, k);
            k->unchanged = 1;
        }
        if (e->n == 0) return gen_cont(k);
        return gen_unchanged(e->args[0], c, k);
    }
    if (e->kind == K_CALL && e->n == 0 && e->def->kind == D_OP && !e->def->native && e->def->local != 2)
        return gen_unchanged(e->def->body, (Ctx){NULL, c.inst}, k);
    if (e->kind == K_BOUND) {   /* a parameter: of its argument */
        Env *b = env_find(c.env, e->def);
        if (b && b->e) return gen_unchanged(b->e, (Ctx){b->ctx_env, b->ctx_inst}, k);
    }
    if (e->kind == K_DECL) {
        /* UNCHANGED of a variable an instance substitutes: of what it is. */
        Ctx outer = c;
        Expr *sub = substitute(e->def, &outer);
        int named = 0;   /* ENABLED binds the variable by name */
        for (Inst *in = c.inst; in != outer.inst && !named; in = in->parent) named = in->def == &enabled_mark;
        if (sub && sub->kind != X_OPREF && !named) return gen_unchanged(sub, outer, k);
        Expr prime;
        memset(&prime, 0, sizeof prime);
        prime.kind = K_PRIME;
        prime.n = 1;
        prime.args = &e;
        int var = assignable(&prime, c);
        if (var >= 0 && !gen_target[var]) {
            Value *v = eval(e, c);
            return gen_assign(var, v, k);
        }
    }
    return unchanged_now(e, c) ? gen_cont(k) : 0;
}

/* What TLC is computing, as its messages name it. */
static const char *gen_what(void) {
    return gen_init ? "initial states" : gen_emit == enabled_emit ? "ENABLED" : "next states";
}

/* A conjunct that is no boolean: TLC's Assert.fail, a TLCRuntimeException. */
static _Noreturn void not_boolean(Expr *e, Value *v) {
    fail_runtime(e, MANYAN_ERROR,"In computing %s, TLC expected a boolean expression,\nbut instead found %s.", gen_what(), pretty(v));
}

/* A number or string where TLC expects an action. */
static _Noreturn void not_relation(Expr *e) {
    fail_at(e, gen_init ? "The init state relation is not a boolean expression."
               : gen_emit == enabled_emit ? "Attempted to compute ENABLED on a non-boolean expression."
               : "The next state relation is not a boolean expression.");
}

/* The context of the body of an instance call's definition: the chain
   of instances (instance_chain) and the definition's parameters. */
static Ctx instance_ctx(Expr *e, Ctx c) {
    Def *d = e->def;
    Inst *inst = instance_chain(e, c);
    Env *env = NULL;
    for (int i = 0; i < e->n && i < d->nparams; i++) {
        if (d->params[i]->arity) env = mk_binding(d->params[i], eval_operator_arg(e->args[i], c), env);
        else env = mk_arg(d->params[i], e->args[i], c, env);
    }
    return (Ctx){env, inst};
}

static int gen_untracked(Expr *e, Ctx c, Cont *k);

/* TLC's incomplete action composition, behind its Java property: s goes
   to u by A \cdot B when s goes to some t by A and t to u by B. As TLC,
   t starts with s's values of the variables already assigned, and the
   conjuncts after A \cdot B follow both A and B. */
static void cdot_enabled(void) {
    if (strcasecmp(S(*prop("-Dtlc2.tool.impl.Tool.cdot")), "true"))
        fail("The current version of TLC does not support action composition.  An incomplete implementation can be enabled via the tlc2.tool.impl.Tool.cdot=true java property.");
}

typedef struct { Value ***v; int n, cap; } Middles;
static Middles *cdot_middle;
static int middle_emit(void) {
    Middles *m = cdot_middle;
    if (m->n == m->cap) {
        Value ***v = NEWN(Value **, m->cap = m->cap ? 2 * m->cap : 8);
        if (m->n) memcpy(v, m->v, sizeof(Value **) * (size_t)m->n);
        m->v = v;
    }
    m->v[m->n++] = snapshot(gen_target);
    return 0;
}

/* The states t that A goes to from the current state, starting from t. */
static Middles cdot_first(Expr *a, Ctx c, Value **t, Cont *k) {
    Value **saved_target = gen_target, **saved_next = next_state;
    int (*saved_emit)(void) = gen_emit;
    Middles m = {0}, *saved_middle = cdot_middle;
    gen_target = next_state = t;
    gen_emit = middle_emit;
    cdot_middle = &m;
    int saved_slicing = slicing;
    slicing = 0;
    gen(a, c, k);
    slicing = saved_slicing;
    cdot_middle = saved_middle;
    gen_target = saved_target;
    next_state = saved_next;
    gen_emit = saved_emit;
    return m;
}

static Value **cdot_from;          /* s, while B goes on from t */
static int (*cdot_emit)(void);     /* the emit of A \cdot B */
static int last_emit(void) {
    Value **t = cur_state;
    cur_state = cdot_from;
    int r = cdot_emit();
    cur_state = t;
    return r;
}

static int gen_cdot(Expr *e, Ctx c, Cont *k) {
    cdot_enabled();
    Value **s = cur_state, **t = NEWN(Value *, nvars);
    for (int i = 0; i < nvars; i++) t[i] = gen_target[i] ? s[i] : NULL;
    int enabling = gen_emit == enabled_emit;
    Middles m = cdot_first(e->args[0], c, t, enabling ? NULL : k);
    Value **saved_from = cdot_from;
    int (*saved_emit)(void) = gen_emit, (*saved_cdot)(void) = cdot_emit;
    if (!enabling) {
        generated += m.n;
        cdot_from = s;
        cdot_emit = gen_emit;
        gen_emit = last_emit;
    }
    int found = 0;
    for (int i = 0; i < m.n && !found; i++) {
        cur_state = m.v[i];
        found = gen(e->args[1], c, k);
    }
    cur_state = s;
    gen_emit = saved_emit;
    cdot_emit = saved_cdot;
    cdot_from = saved_from;
    return found;
}

/* A \cdot B as a formula, as TLC: some t that A goes to from the current
   state, starting from no values, goes to the next state by B. */
static Value *eval_cdot(Expr *e, Ctx c) {
    cdot_enabled();
    int saved_init = gen_init, saved_primed = primed;
    gen_init = primed = 0;
    Middles m = cdot_first(e->args[0], c, NEWN(Value *, nvars), NULL);
    gen_init = saved_init;
    primed = saved_primed;
    Value **s = cur_state, *v = FALSEV;
    for (int i = 0; i < m.n && v != TRUEV; i++) {
        cur_state = m.v[i];
        v = eval(e->args[1], c);
        if (v->kind != V_BOOL) not_boolean(e->args[1], v);
    }
    cur_state = s;
    return v;
}

static int gen_tracked(Expr *e, Ctx c, Cont *k) {
    int n = nframes;
    frames_push(e);
    int found = gen_untracked(e, c, k);
    nframes = n;
    return found;
}
static inline int gen(Expr *e, Ctx c, Cont *k) { return tracking ? gen_tracked(e, c, k) : gen_untracked(e, c, k); }

/* var' \in s: each element in turn, in TLC's random order in -generate. */
typedef struct { int var; Cont *k; } GenMember;
static int gen_member_take(Value *v, void *data) {
    GenMember *g = data;
    return !slicing || choice_take() ? gen_assign(g->var, v, g->k) : 0;
}

static int gen_member(int var, Value *s, Expr *e, Cont *k) {
    /* TLC enumerates any set it can, failing there for an infinite one. */
    if (!is_set(s) || user_set(s))
        fail_at(e, gen_emit == enabled_emit ? "The right side of \\IN is not enumerable." : "In computing %s, the right side of \\IN is not enumerable.", gen_what());
    if (choosing()) {
        Order o;
        order_begin(&o, s);
        for (Big i = 0; i < o.size; i++) {
            int r = gen_assign(var, order_next(&o), k);
            if (r || sim_kept()) return r;
        }
        return 0;
    }
    int r = 0;
    if (slicing && !choice_begin()) return 0;
    if (s->kind == V_LAZY && s->lazy == L_FILTER && !s->u.l.b) {   /* as TLC, one element at a time */
        GenMember g = {var, k};
        r = each_filtered(s, gen_member_take, &g);
    } else {
        s = elements(s);
        for (int i = 0; i < s->n && !r; i++) if (!slicing || choice_take()) r = gen_assign(var, s->u.set.elems[i], k);
    }
    if (slicing) choice_depth--;
    return r;
}

static int gen_untracked(Expr *e, Ctx c, Cont *k) {
    switch (e->kind) {
    case X_BOOL:
        return e->num ? gen_cont(k) : 0;
    case X_NUM: case X_STR:
        not_relation(e);
    case K_AND:
        for (int i = e->n - 1; i >= 1; i--) k = mk_cont(e->args[i], c, k);
        return gen(e->args[0], c, k);
    case K_OR:
        if (choosing()) {   /* from a random disjunct, by a random prime step */
            int n = e->n, i = rng_index(n), p = rng_prime();
            for (int t = 0; t < n; t++, i = (i + p) % n) {
                int r = gen(e->args[i], c, k);
                if (r || sim_kept()) return r;
            }
            return 0;
        }
        if (slicing) {
            if (!choice_begin()) return 0;
            int r = 0;
            for (int i = 0; i < e->n && !r; i++) if (choice_take()) r = gen(e->args[i], c, k);
            choice_depth--;
            return r;
        }
        for (int i = 0; i < e->n; i++) if (gen(e->args[i], c, k)) return 1;
        return 0;
    case X_EXISTS: {
        if (choosing()) return gen_exists_random(e, c, k);
        GenData g = {e->args[0], k};
        if (slicing && !choice_begin()) return 0;
        int r = for_bindings(e->bounds, e->nb, c, gen_bound_fn, &g);
        if (slicing) choice_depth--;
        return r;
    }
    case X_FORALL: {
        /* As TLC: the conjunction of the body for each binding, the
           first, then the others from the last, each a choice point. */
        Ctxs l = {0};
        for_bindings(e->bounds, e->nb, c, collect_fn, &l);
        if (!l.n) return gen_cont(k);
        for (int i = 1; i < l.n; i++) k = mk_cont(e->args[0], l.v[i], k);
        return gen(e->args[0], l.v[0], k);
    }
    case X_IF: {
        Value *v = eval(e->args[0], c);
        if (v->kind != V_BOOL) {
            if (gen_emit == enabled_emit)
                fail("In computing ENABLED, a non-boolean expression(%s) was used as the guard condition of an IF.\n%s", article_kind(v), loc_str(e));
            fail("In computing %s, a non-boolean expression (%s) was used as the condition of an IF.%s%s", gen_what(), article_kind(v), gen_init ? "\n" : "", loc_str(e));
        }
        return gen(e->args[v->u.i ? 1 : 2], c, k);
    }
    case K_IMPLIES: {
        Value *v = eval(e->args[0], c);
        if (v->kind != V_BOOL && gen_init) {
            fail("In computing initial states of a predicate of form P => Q, P was %s\n.%s", article_kind(v), loc_str(e));
        }
        if (v->kind != V_BOOL) fail_at(e, "In computing next states of a predicate of the form P => Q, P was\n%s.", article_kind(v));
        return v->u.i ? gen(e->args[1], c, k) : gen_cont(k);
    }
    case X_CASE:
        if (choosing()) fail_java("java.lang.UnsupportedOperationException", "Probabilistic evaluation of next-state relation not implemented for CASE yet.");
        for (int i = 0; i + 1 < e->n; i += 2) {
            Value *v = e->args[i] ? eval(e->args[i], c) : TRUEV;
            if (v->kind != V_BOOL)
                fail_at(e->args[i + 1], "In computing %s, a non-boolean expression%s(%s) was used as a guard condition of a CASE.",
                        gen_what(), gen_emit == enabled_emit ? "" : " ", article_kind(v));
            if (v->u.i) return gen(e->args[i + 1], c, k);
        }
        fail_at(e, "In computing %s, TLC encountered a CASE with no conditions true.", gen_what());
    case X_LET: {
        Env *env = c.env;
        for (int i = 0; i < e->ndefs; i++) env = mk_thunk(e->defs[i], e->defs[i]->body, c, env);
        for (Env *b = env; b != c.env; b = b->next) b->ctx_env = env;
        return gen(e->args[0], (Ctx){env, c.inst}, k);
    }
    case K_CALL: {
        Def *d = e->def->replacement ? e->def->replacement : e->def;
        if (d->kind != D_OP || d->native || d->nparams != e->n) break;
        if (e->n == 0 && def_level(d) == 0) break;   /* TLC computes it as a constant */
        if (d->local == 2) {
            Env *b = env_find(c.env, d);
            if (!b) break;
            Env *env = b->ctx_env;
            for (int i = 0; i < e->n; i++) {
                if (d->params[i]->arity) env = mk_binding(d->params[i], eval_operator_arg(e->args[i], c), env);
                else env = mk_arg(d->params[i], e->args[i], c, env);
            }
            return gen(d->body, (Ctx){env, b->ctx_inst}, k);
        }
        Env *env = NULL;
        for (int i = 0; i < e->n; i++) {
            if (d->params[i]->arity) env = mk_binding(d->params[i], eval_operator_arg(e->args[i], c), env);
            else env = mk_arg(d->params[i], e->args[i], c, env);
        }
        deeper();
        int r = gen(d->body, (Ctx){env, c.inst}, k);
        eval_depth--;
        return r;
    }
    case K_PARAMCALL: {
        /* A constant operator that stands for a definition is a call of it. */
        if (e->def->kind != D_CONST) break;
        Ctx at = {NULL, NULL};
        Def *d = const_operator(e->def, c, &at);
        if (!d || d->kind != D_OP || d->native || d->local == 2 || d->nparams != e->n) break;
        Env *env = NULL;
        for (int i = 0; i < e->n; i++) {
            if (d->params[i]->arity) env = mk_binding(d->params[i], eval_operator_arg(e->args[i], c), env);
            else env = mk_arg(d->params[i], e->args[i], c, env);
        }
        return gen(d->body, (Ctx){env, at.inst}, k);
    }
    case K_INSTCALL: {
        if (e->def->kind != D_OP || e->def->native) break;
        /* As a definition of the module, one TLC computes as a constant. */
        int plain = e->n == 0;
        for (int i = 0; i < e->ndefs && plain; i++) plain = e->defs[i]->nparams == 0;
        if (plain && expr_level(e) == 0) break;
        return gen(e->def->body, instance_ctx(e, c), k);
    }
    case K_BOUND: {
        /* A parameter stands for its argument, which may be an action. */
        Env *b = env_find(c.env, e->def);
        if (!b || !b->e) break;
        return gen(b->e, (Ctx){b->ctx_env, b->ctx_inst}, k);
    }
    case K_EQ: {
        int var = assignable(e->args[0], c);
        if (var >= 0 && !gen_target[var]) return gen_assign(var, eval(e->args[1], c), k);
        break;
    }
    case K_IN: case K_SUBSETEQ: {   /* x' \subseteq S as x' \in SUBSET S */
        int var = assignable(e->args[0], c);
        if (var < 0 || gen_target[var]) break;
        Value *s = eval(e->args[1], c);
        if (e->kind == K_SUBSETEQ) {
            Value *t = mk_lazy(L_SUBSET);
            t->u.l.expr = source(e);
            t->u.l.a = s;
            s = t;
        }
        return gen_member(var, s, e, k);
    }
    case X_APPLY: {
        /* As TLC: a lazy function applied is its body, part of the
           action; TLC computes initial states without keeping it lazy. */
        Value *key, *f = apply_parts(e, c, !gen_init, gen_what(), &key);
        Ctx at = c;
        Expr *body = !f ? fcndef_bind(e->args[0]->def, key, &at, e->args[0])
                   : f->kind == V_LAMBDA && !f->n ? lambda_bind(f, key, &at, e->args[0]) : NULL;
        if (!body) {
            Value *v = fcn_apply(f, key, e);
            if (v->kind != V_BOOL) fail_at(e, "In computing %s, TLC expected a boolean expression,\nbut didn't find one.", gen_what());
            return v->u.i ? gen_cont(k) : 0;
        }
        Value *saved = at_value;
        if (f) at_value = f->u.l.b;
        int found = gen(body, at, k);
        at_value = saved;
        return found;
    }
    case K_UNCHANGED:
        return gen_unchanged(e->args[0], c, k);
    case K_CDOT:
        return gen_cdot(e, c, k);
    case X_SQACT: {
        if (gen(e->args[0], c, k)) return 1;
        return gen_unchanged(e->args[1], c, k);
    }
    case X_ANGLEACT: {
        Expr *u = NEW(Expr);
        *u = *e;
        u->kind = K_UNCHANGED;
        u->n = 1;
        u->args = NEWN(Expr *, 1);
        u->args[0] = e->args[1];
        Expr *not = NEW(Expr);
        *not = *e;
        not->kind = K_NOT;
        not->n = 1;
        not->args = NEWN(Expr *, 1);
        not->args[0] = u;
        return gen(e->args[0], c, mk_cont(not, c, k));
    }
    case K_NOT:
        /* The step of <<A>>_v changes v. */
        if (e->args[0]->kind != K_UNCHANGED) break;
        return unchanged_now(e->args[0]->args[0], c) ? 0 : gen_cont(k);
    default:
        break;
    }
    Value *v = eval(e, c);
    if (v->kind != V_BOOL) not_boolean(e, v);
    return v->u.i ? gen_cont(k) : 0;
}

/* Whether action a has a successor from the current state. */
static int enabled_found;
static Value **enabled_seen;   /* if set, where the successor found is put */
static int enabled_emit(void) {
    enabled_found = 1;
    if (enabled_seen) memcpy(enabled_seen, gen_target, sizeof *gen_target * (size_t)nvars);
    return 1;
}

static int enabled(Expr *a, Ctx c) {
    Value **saved_target = gen_target, **saved_next = next_state;
    int saved_init = gen_init, saved_primed = primed;
    int (*saved_emit)(void) = gen_emit;
    int saved_names = nenabled_names;
    Value **fresh = NEWN(Value *, nvars + 16);
    gen_target = next_state = fresh;
    gen_init = 0;
    primed = 0;
    gen_emit = enabled_emit;
    enabled_found = 0;
    Inst *mark = NEW(Inst);
    mark->def = &enabled_mark;
    mark->parent = c.inst;
    c.inst = mark;
    int saved_slicing = slicing;
    slicing = 0;
    gen(a, c, NULL);
    slicing = saved_slicing;
    nenabled_names = saved_names;
    int found = enabled_found;
    gen_target = saved_target;
    next_state = saved_next;
    gen_init = saved_init;
    primed = saved_primed;
    gen_emit = saved_emit;
    return found;
}

/* ---------------------------------------------------------------- actions */

/* The next-state action split at its disjunctions, constant existential
   quantifiers, and the definitions it uses; each part is named by the
   definition it belongs to and located by its expression (§11.2). */
typedef struct { Expr *e; Ctx c; int name; Expr *loc; Def *op; } Action;   /* op: the definition whose arguments label it */

static Action *actions;
static int nactions;

static void add_action(Expr *e, Ctx c, int name, Expr *loc, Def *op) {
    actions = xrealloc(actions, sizeof(Action) * (size_t)(nactions + 1));
    actions[nactions] = (Action){e, c, name, loc, op};
    nactions++;
}

typedef struct { Expr *body; int name; Def *op; } SplitData;

static void split_action(Expr *e, Ctx c, int name, Def *op);

/* A definition seen through instances as TLC names it, I!A, and the first
   of the instances that substitutes, NULL if none. */
static int instance_name(Expr *e, Def **in) {
    Buf b = {0};
    *in = NULL;
    for (int i = 0; i < e->ndefs; i++) {
        if (!*in && e->defs[i]->nsubst) *in = e->defs[i];
        if (e->defs[i]->name) buf_printf(&b, "%s!", S(e->defs[i]->name));
    }
    buf_puts(&b, S(e->def->name));
    int name = intern(b.s);
    free(b.s);
    return name;
}

static int split_fn(Ctx c, void *data) {
    SplitData *s = data;
    split_action(s->body, c, s->name, s->op);
    return 0;
}

static int bounds_constant(Expr *e) {
    for (int i = 0; i < e->nb; i++) if (!e->bounds[i].set || expr_level(e->bounds[i].set) > 0) return 0;
    return 1;
}

/* Whether the bounds of e have more bindings than -symbolic splits an
   action into: past them it picks one, as Apalache does. */
static int bindings_many(Expr *e, Ctx c) {
    int64_t total = 1;
    for (int i = 0; i < e->nb; i++) {
        int64_t n = set_size(union_cache(eval(e->bounds[i].set, c)));
        for (int j = 0; j < (e->bounds[i].tuple ? 1 : e->bounds[i].n); j++)
            if (n < 0 || (total *= n) > 64) return 1;
    }
    return 0;
}

/* The actions of e, as TLC splits them: each named by the definition it
   is in, op, and labeled with the values of op's constant arguments. */
static void split_action(Expr *e, Ctx c, int name, Def *op) {
    switch (e->kind) {
    case K_OR:
        for (int i = 0; i < e->n; i++) split_action(e->args[i], c, name, op);
        return;
    case X_EXISTS:
        if (bounds_constant(e)) {
            /* As TLC, \E x \in S : A is one action if S is empty or fails. */
            SplitData s = {e->args[0], name, op};
            int n = nactions;
            volatile int many = 0;
            EvalState es = eval_save();
            ErrorState er = error_save();
            sigjmp_buf here;
            handler = &here;
            if (sigsetjmp(here, 0)) nactions = n;
            else if (!symbolic_mode || !(many = bindings_many(e, c))) for_bindings(e->bounds, e->nb, c, split_fn, &s);
            eval_restore(es);
            error_restore(&er);
            if (many) { add_action(e, c, name, e->args[0], op); return; }   /* located as TLC's action of each binding */
            if (nactions > n) return;
        }
        break;
    case X_LET: {
        Env *env = c.env;
        for (int i = 0; i < e->ndefs; i++) env = mk_thunk(e->defs[i], e->defs[i]->body, c, env);
        for (Env *b = env; b != c.env; b = b->next) b->ctx_env = env;
        split_action(e->args[0], (Ctx){env, c.inst}, name, op);
        return;
    }
    case K_CALL: {
        Def *d = e->def->replacement ? e->def->replacement : e->def;
        if (d->kind != D_OP || d->nparams != e->n) break;
        /* As TLC, a call is one action, named by the definition and located
           at the call, if the definition is built in or an argument is not
           constant or fails. */
        int whole = d->native != NULL;
        for (int i = 0; i < e->n; i++) whole |= expr_level(e->args[i]) > 0;
        if (whole) { add_action(e, c, e->def->name, e, NULL); return; }
        Env *volatile env = d->local == 2 ? c.env : NULL;   /* a LET definition sees the LET */
        EvalState es = eval_save();
        ErrorState er = error_save();
        sigjmp_buf here;
        handler = &here;
        int failed = sigsetjmp(here, 0);
        if (!failed)
            for (int i = 0; i < e->n; i++)
                env = mk_binding(d->params[i], d->params[i]->arity ? eval_operator_arg(e->args[i], c) : eval(e->args[i], c), env);
        eval_restore(es);
        error_restore(&er);
        if (failed) { add_action(e, c, e->def->name, e, NULL); return; }
        deeper();
        split_action(d->body, (Ctx){env, c.inst}, d->name, d);
        eval_depth--;
        return;
    }
    case K_INSTCALL: {
        if (e->def->kind != D_OP || e->def->native) break;
        /* As TLC, a definition seen through an instance that substitutes is
           one action, named I!A and located at the INSTANCE statement. */
        /* A part of a specification is no definition: TLC's Action. */
        Def *in;
        int qualified = instance_name(e, &in);
        if (e->def->part) qualified = name;
        if (in) { add_action(e, c, qualified, in->where, NULL); return; }
        split_action(e->def->body, instance_ctx(e, c), qualified, NULL);
        return;
    }
    case X_NUM: case X_STR:
        not_relation(e);
    default:
        break;
    }
    add_action(e, c, name, e, op);
}

/* ---------------------------------------------------------------- states */

/* The fingerprint of a value hashes its canonical form, the same for
   equal values. An atom mixes its kind (tag 1 to 4) and payload; a set sums
   its elements' hashes and a function its pairs', a function on 1..n
   being a tuple, so that a function with one pair changed differs by one
   term (fcn_update, Append). A set or function keeps its sum. The mixing
   is wyhash's: the halves of a full product, folded. */
static inline uint64_t wymix(uint64_t a, uint64_t b) {
    __uint128_t m = (__uint128_t)a * b;
    return (uint64_t)m ^ (uint64_t)(m >> 64);
}

static inline uint64_t fmix(uint64_t h) { return wymix(h ^ 0xa0761d6478bd642fULL, 0xe7037ed1a0b428dbULL); }

static uint64_t value_hash(Value *v);

static inline uint64_t atom_word(int kind, int64_t x) { return (uint64_t)(kind + 1) | (uint64_t)x << 8; }

static inline uint64_t elem_hash(Value *v) { return v->kind <= V_MODEL ? fmix(atom_word(v->kind, v->u.i)) : value_hash(v); }

/* The hashes of the first indices of tuples, 1 to 64. */
static uint64_t index_hash[64];

/* The hash of pair i of f, with value val: the key's hash and the value's,
   or an atom's word, which the pair's mixing spreads. */
static inline uint64_t pair_hash(Value *f, int i, Value *val) {
    uint64_t k = f->kind != V_TUPLE ? elem_hash(f->u.fcn.keys[i]) : i < 64 ? index_hash[i] : fmix(atom_word(V_INT, i + 1));
    uint64_t x = val->kind <= V_MODEL ? atom_word(val->kind, val->u.i) : value_hash(val);
    return wymix(k ^ 0x8ebc6af09c88c6e3ULL, x ^ 0x589965cc75374cc3ULL);
}

/* A lazy function hashes as the function it is; out of value_hash's way. */
static __attribute__((cold, noinline)) uint64_t hash_lambda(Value *v) {
    Value *f = realize(v);
    if (f->kind == V_LAMBDA) count_infinite(f->u.l.a);
    return value_hash(f);
}

static int unfingerprintable;   /* a fingerprint failed on a value TLC has no fingerprint for, as Nat */

static uint64_t value_hash(Value *v) {
    uint64_t sum = 0;
    switch (v->kind) {
    case V_BOOL: case V_INT: case V_STR: case V_MODEL: return elem_hash(v);
    case V_INTERVAL: {
        uint64_t n = (uint64_t)interval_size(v);
        for (int64_t i = v->u.range.lo; i <= v->u.range.hi; i++) sum += fmix(atom_word(V_INT, i));
        return fmix(sum ^ (0x05 | n << 8));
    }
    case V_SET: case V_LAZY: {
        if (user_set(v)) { unfingerprintable = 1; fail("TLC has found a state in which the value of a variable contains %s", pretty(v)); }
        Value *set = enumerate(union_cache(v));
        if (!(sum = set->u.set.hash)) {
            fp_enter(set->u.set.source);
            for (int i = 0; i < set->n; i++) sum += elem_hash(set->u.set.elems[i]);
            fp_leave(set->u.set.source);
            set->u.set.hash = sum;
        }
        return fmix(sum ^ (0x05 | (uint64_t)set->n << 8));
    }
    case V_LAMBDA: return hash_lambda(v);
    case V_TUPLE: case V_FCN:
        if (v->made >= MADE_LAMBDA) v->made = MADE_PLAIN;   /* TLC normalizes what it fingerprints */
        if (!(sum = v->u.fcn.hash)) {
            fp_enter(v->u.fcn.source);
            for (int i = 0; i < v->n; i++) sum += pair_hash(v, i, v->u.fcn.vals[i]);
            fp_leave(v->u.fcn.source);
            v->u.fcn.hash = sum;
        }
        return fmix(sum ^ (0x06 | (uint64_t)v->n << 8));
    default:
        fail("Attempted to fingerprint an operator.");
    }
}

/* A state is stored as the bytes of its values, which keep how a value
   prints: a tag and its 32-bit word, zigzagged and in 7-bit groups, so a
   small number takes one byte. */
static int put_word(char *w, int64_t v) {
    uint32_t z = (uint32_t)(int32_t)v << 1 ^ (uint32_t)((int32_t)v >> 31);
    int n = 0;
    for (; z > 0x7f; z >>= 7) w[n++] = (char)(z | 0x80);
    w[n++] = (char)z;
    return n;
}

static void put32(Buf *b, int64_t v) {
    buf_room(b, 5);
    b->n += (size_t)put_word(b->s + b->n, v);
    b->s[b->n] = 0;
}

static inline void put_tagged(Buf *b, char tag, int64_t v) {
    buf_room(b, 6);
    char *w = b->s + b->n;
    uint32_t z = (uint32_t)(int32_t)v << 1 ^ (uint32_t)((int32_t)v >> 31);
    w[0] = tag;
    if (z < 0x80) {   /* most words: one byte */
        w[1] = (char)z;
        w[2] = 0;
        b->n += 2;
        return;
    }
    b->n += 1 + (size_t)put_word(w + 1, v);
    b->s[b->n] = 0;
}

static void encode(Buf *b, Value *v) {
    if (v->kind == V_LAMBDA) v = realize(v);
    switch (v->kind) {
    case V_BOOL: buf_add(b, v->u.i ? "b\1" : "b\0", 2); return;
    case V_INT: put_tagged(b, 'i', v->u.i); return;
    case V_STR: put_tagged(b, 's', v->u.i); return;
    case V_MODEL: put_tagged(b, 'm', v->u.i); return;
    case V_INTERVAL: put_tagged(b, 'I', v->u.range.lo); put32(b, v->u.range.hi); return;
    case V_SET: case V_LAZY: {
        Value *set = enumerate(v);
        put_tagged(b, 'S', set->n);
        for (int i = 0; i < set->n; i++) encode(b, set->u.set.elems[i]);
        return;
    }
    case V_TUPLE: case V_FCN: {
        if (v->kind == V_FCN && v->n == 0) { put_tagged(b, 'T', 0); return; }
        put_tagged(b, v->kind == V_TUPLE ? 'T' : v->made == MADE_RECORD ? 'R' : v->range ? 'N' : 'F', v->n);
        for (int i = 0; i < v->n; i++) {
            if (v->kind == V_FCN) encode(b, v->u.fcn.keys[i]);
            encode(b, v->u.fcn.vals[i]);
        }
        return;
    }
    default:
        fail("Attempted to fingerprint an operator.");
    }
}

static int32_t get32(const char **p) {
    uint32_t z = (unsigned char)**p;
    if (z < 0x80) { (*p)++; return (int32_t)(z >> 1 ^ -(z & 1)); }
    z = 0;
    unsigned char c;
    int shift = 0;
    do { c = (unsigned char)*(*p)++; z |= (uint32_t)(c & 0x7f) << shift; shift += 7; } while (c & 0x80);
    return (int32_t)(z >> 1 ^ -(z & 1));
}

/* A value of a state, with its hash: the successors that keep or update it
   need not hash it again. */
static Value *decode(const char **p) {
    char tag = *(*p)++;
    uint64_t sum = 0;
    switch (tag) {
    case 'b': return BOOLV(*(*p)++);
    case 'i': return mk_int(get32(p));
    case 's': return mk_str(get32(p));
    case 'm': return mk_model(get32(p));
    case 'I': { int32_t lo = get32(p); int32_t hi = get32(p); return mk_interval(lo, hi); }
    case 'S': {
        int n = get32(p);
        Value *s = mk_set(n);
        for (int i = 0; i < n; i++) sum += elem_hash(s->u.set.elems[i] = decode(p));
        s->u.set.hash = sum;
        return s;
    }
    case 'T': {
        int n = get32(p);
        Value *t = mk_tuple(n);
        for (int i = 0; i < n; i++) sum += pair_hash(t, i, t->u.fcn.vals[i] = decode(p));
        t->u.fcn.hash = sum;
        return t;
    }
    default: {
        int n = get32(p);
        Value *f = mk_fcn(n);
        for (int i = 0; i < n; i++) {
            f->u.fcn.keys[i] = decode(p);
            sum += pair_hash(f, i, f->u.fcn.vals[i] = decode(p));
        }
        f->u.fcn.hash = sum;
        if (tag == 'R') f->made = MADE_RECORD;
        f->range = tag == 'N';
        return f;
    }
    }
}

typedef struct { uint64_t fp; size_t off; int len; int parent; int action; int depth; int *edges; int nedges, capedges; } StateRec;

static StateRec *states;
static int nstates, capstates;
static Buf store;
/* The fingerprint set: open addressing on the fingerprint, which each
   slot keeps beside its state's index (0 is an empty slot). */
typedef struct { uint64_t fp; int state; } FpSlot;

static FpSlot *fp_table;
static int fp_size;

static int fp_find(uint64_t fp) {
    if (!fp_size) return -1;
    for (int j = (int)(fp & (uint64_t)(fp_size - 1)); fp_table[j].state; j = (j + 1) & (fp_size - 1))
        if (fp_table[j].fp == fp) return fp_table[j].state - 1;
    return -1;
}

static void fp_put(FpSlot *table, int size, uint64_t fp, int idx) {
    int j = (int)(fp & (uint64_t)(size - 1));
    while (table[j].state) j = (j + 1) & (size - 1);
    table[j].fp = fp;
    table[j].state = idx + 1;
}

static char *fp_region;       /* shared memory the tables are taken from, in turn */
static size_t fp_region_used, fp_region_size;

static void fp_insert(int idx) {
    if ((nstates + 1) * 2 >= fp_size) {
        if (fp_size >= 1 << 30) { fputs("manyan: too many states\n", stderr); exit(MANYAN_ERROR); }
        int size = fp_size ? fp_size * 2 : 1 << 16;
        size_t bytes = sizeof(FpSlot) * (size_t)size;
        FpSlot *table;
        if (fp_region) {
            if (fp_region_used + bytes > fp_region_size) { fputs("manyan: too many states\n", stderr); exit(MANYAN_ERROR); }
            table = (FpSlot *)(fp_region + fp_region_used);
            fp_region_used += bytes;
        } else {
            table = xcalloc((size_t)size, sizeof(FpSlot));
        }
        for (int i = 0; i < fp_size; i++) if (fp_table[i].state) fp_put(table, size, fp_table[i].fp, fp_table[i].state - 1);
        if (!fp_region) free(fp_table);
        fp_table = table;
        fp_size = size;
    }
    fp_put(fp_table, fp_size, states[idx].fp, idx);
}

static Value **decode_state(int idx) {
    Value **st = NEWN(Value *, nvars);
    const char *p = store.s + states[idx].off;
    for (int i = 0; i < nvars; i++) st[i] = decode(&p);
    return st;
}

/* ---------------------------------------------------------------- the model */

typedef struct { Def *def; Expr *expr; Ctx ctx; int name, possible; } Check;   /* expr, in ctx; possible: 1 + its _POSSIBLE's index */

static Expr *init_expr, *next_expr;
/* The last of the initial predicates, which a simulation names an initial
   state by: a definition's body by the definition, as TLC's Action. */
static int init_name;   /* the initial predicate's name in a simulation, 0 if none */
static Expr *init_where;
static Ctx root_ctx;
static Check *invariants, *implied_inits, *constraints, *action_constraints, *action_props, *temporal_props;
static int ninvariants, nimplied_inits, nconstraints, naction_constraints, naction_props, ntemporal_props;
static Expr *view_expr;
static Expr *periodic_expr;   /* _PERIODIC: TLC evaluates it at its progress reports */
static Value **symmetry;     /* permutations of model values */
static int nsymmetry;
static int check_deadlock = 1;
static Module *root;
static Expr **fairness;       /* WF and SF conjuncts of the specification */
static int nfairness;
static Expr *spec_subscript;

static void add_check(Check **list, int *n, Def *d, Expr *e, Ctx c, int name) {
    *list = xrealloc(*list, sizeof(Check) * (size_t)(*n + 1));
    (*list)[*n] = (Check){d, e, c, name, 0};
    (*n)++;
}

/* The model value a permutation maps v to; any other value is itself. */
static Value *permute(Value *v, Value *perm) {
    if (v->kind == V_MODEL)
        for (int i = 0; i < perm->n; i++) {
            Value *k = perm->u.fcn.keys[i];
            if (k->kind == V_MODEL && k->u.i == v->u.i) return perm->u.fcn.vals[i];
        }
    return v;
}

/* v with each model value mapped by perm. */
static Value *permute_value(Value *v, Value *perm) {
    switch (v->kind) {
    case V_MODEL: return permute(v, perm);
    case V_SET: case V_LAZY: {
        if (v->kind == V_LAZY && set_is_infinite(v)) return v;
        Value *s = enumerate(v);
        List l = {0};
        for (int i = 0; i < s->n; i++) list_add(&l, permute_value(s->u.set.elems[i], perm));
        return list_set(&l);
    }
    case V_TUPLE: {
        Value *t = mk_tuple(v->n);
        for (int i = 0; i < v->n; i++) t->u.fcn.vals[i] = permute_value(v->u.fcn.vals[i], perm);
        return t;
    }
    case V_FCN: {
        List keys = {0}, vals = {0};
        for (int i = 0; i < v->n; i++) {
            list_add(&keys, permute_value(v->u.fcn.keys[i], perm));
            list_add(&vals, permute_value(v->u.fcn.vals[i], perm));
        }
        Value *f = mk_fcn_from(&keys, &vals);
        f->made = v->made;
        f->range = v->range;
        return f;
    }
    default:
        return v;
    }
}

/* x mapped by q, then by p, as a permutation without its fixed points. */
static Value *perm_compose(Value *p, Value *q) {
    List keys = {0}, vals = {0};
    Value *dom[2] = {q, p};
    for (int d = 0; d < 2; d++)
        for (int i = 0; i < dom[d]->n; i++) {
            Value *x = fcn_key(dom[d], i), *y = permute(permute(x, q), p);
            int seen = veq(x, y);
            for (int k = 0; k < keys.n && !seen; k++) seen = veq(keys.v[k], x);
            if (!seen) { list_add(&keys, x); list_add(&vals, y); }
        }
    return mk_fcn_from(&keys, &vals);
}

/* The group the permutations generate, as TLC takes a SYMMETRY: each
   composition of them, without fixed points so that equal ones are
   equal values. */
static Value *permutation_group(Value *generators) {
    List g = {0};
    size_t size = 64;
    int *table = xcalloc(size, sizeof(int));   /* indices into g, plus one, by hash */
    Value *identity = mk_fcn_from(&(List){0}, &(List){0});
    for (int i = -1; i < g.n; i++) {
        for (int j = 0; j < generators->n; j++) {
            Value *c = perm_compose(generators->u.set.elems[j], i < 0 ? identity : g.v[i]);
            size_t h = (size_t)value_hash(c) & (size - 1);
            while (table[h] && !veq(g.v[table[h] - 1], c)) h = (h + 1) & (size - 1);
            if (table[h]) continue;
            list_add(&g, c);
            table[h] = g.n;
            if ((size_t)g.n * 2 > size) {   /* grow, rehashing */
                free(table);
                size *= 2;
                table = xcalloc(size, sizeof(int));
                for (int k = 0; k < g.n; k++) {
                    size_t t = (size_t)value_hash(g.v[k]) & (size - 1);
                    while (table[t]) t = (t + 1) & (size - 1);
                    table[t] = k + 1;
                }
            }
        }
    }
    free(table);
    return list_set(&g);
}

/* The model values the symmetry moves, and the hashes of their images
   under each permutation p: as elements at [p * m + j], as words of a
   function's values after them. */
static Value **sym_models;
static int nsym_models;
static uint64_t *sym_elem, *sym_word;

static void symmetry_tables(void) {
    List m = {0};
    for (int p = 0; p < nsymmetry; p++)
        for (int i = 0; i < symmetry[p]->n; i++) {
            Value *k = symmetry[p]->u.fcn.keys[i];
            int seen = 0;
            for (int j = 0; j < m.n && !seen; j++) seen = veq(m.v[j], k);
            if (!seen) list_add(&m, k);
        }
    sym_models = m.v;
    nsym_models = m.n;
    sym_elem = xmalloc(sizeof(uint64_t) * 2 * (size_t)nsymmetry * (size_t)(m.n + 1));
    sym_word = sym_elem + (size_t)nsymmetry * (size_t)m.n;
    for (int p = 0; p < nsymmetry; p++)
        for (int j = 0; j < m.n; j++) {
            Value *w = permute(m.v[j], symmetry[p]);
            sym_elem[p * m.n + j] = elem_hash(w);
            sym_word[p * m.n + j] = atom_word(w->kind, w->u.i);
        }
}

/* Space for permuted_hashes at each depth: three hashes per permutation. */
static uint64_t **sym_bufs;
static int nsym_bufs;

static uint64_t *sym_buf(int depth) {
    if (depth == nsym_bufs) {
        sym_bufs = xrealloc(sym_bufs, sizeof(uint64_t *) * (size_t)++nsym_bufs);
        sym_bufs[depth] = xmalloc(sizeof(uint64_t) * 3 * (size_t)nsymmetry);
    }
    return sym_bufs[depth];
}

/* Whether a permutation of the symmetry moves a model value in v; if so,
   h[p] is value_hash(permute(v, symmetry[p])) for each p, computed without
   building it: a permutation is one to one, and a set's or function's
   hash is the sum of its parts'. With atom, an atom's h[p] is its word,
   as a function's value is hashed. */
static int permuted_hashes(Value *v, uint64_t *h, int atom, int depth) {
    int n = nsymmetry, moved = 0;
    if (v->kind <= V_MODEL) {
        int j = 0, m = nsym_models;
        if (v->kind == V_MODEL) while (j < m && sym_models[j]->u.i != v->u.i) j++;
        if (v->kind != V_MODEL || j == m) return 0;
        uint64_t *t = atom ? sym_word : sym_elem;
        for (int p = 0; p < n; p++) h[p] = t[p * m + j];
        return 1;
    }
    uint64_t *sums = sym_buf(depth), *k = sums + n, *x = k + n, fixed = 0, tag;
    if (v->kind == V_SET || (v->kind == V_LAZY && !set_is_infinite(v))) {
        Value *set = enumerate(v);
        for (int i = 0; i < set->n; i++) {
            Value *e = set->u.set.elems[i];
            if (!permuted_hashes(e, k, 0, depth + 1)) { fixed += elem_hash(e); continue; }
            if (!moved) memset(sums, 0, sizeof(uint64_t) * (size_t)n);
            moved = 1;
            for (int p = 0; p < n; p++) sums[p] += k[p];
        }
        tag = 0x05 | (uint64_t)set->n << 8;
    } else if (v->kind == V_TUPLE || v->kind == V_FCN) {
        for (int i = 0; i < v->n; i++) {
            Value *val = v->u.fcn.vals[i];
            int km = v->kind == V_FCN && permuted_hashes(v->u.fcn.keys[i], k, 0, depth + 1);
            int vm = permuted_hashes(val, x, 1, depth + 1);
            if (!km && !vm) { fixed += pair_hash(v, i, val); continue; }
            uint64_t k0 = km ? 0 : v->kind == V_FCN ? elem_hash(v->u.fcn.keys[i]) : i < 64 ? index_hash[i] : fmix(atom_word(V_INT, i + 1));
            uint64_t x0 = vm ? 0 : val->kind <= V_MODEL ? atom_word(val->kind, val->u.i) : value_hash(val);
            if (!moved) memset(sums, 0, sizeof(uint64_t) * (size_t)n);
            moved = 1;
            for (int p = 0; p < n; p++)
                sums[p] += wymix((km ? k[p] : k0) ^ 0x8ebc6af09c88c6e3ULL, (vm ? x[p] : x0) ^ 0x589965cc75374cc3ULL);
        }
        tag = 0x06 | (uint64_t)v->n << 8;
    } else {
        return 0;   /* an interval, or a value hashed as it is */
    }
    if (moved) for (int p = 0; p < n; p++) h[p] = fmix((sums[p] + fixed) ^ tag);
    return moved;
}

/* As TLC takes a state under symmetry: the least of its permutations,
   comparing the variables' values in turn. */
static Value **least_permutation(Value **st) {
    Value **best = st;
    for (int p = 0; p < nsymmetry; p++) {
        Value **t = NEWN(Value *, nvars);
        int c = 0;
        for (int i = 0; i < nvars; i++) {
            t[i] = permute_value(st[i], symmetry[p]);
            if (!c) c = vcmp(t[i], best[i]);
        }
        if (c < 0) best = t;
    }
    return best;
}

static uint64_t fingerprint(Value **st) {
    if (view_expr) {
        Value **saved = cur_state;
        cur_state = nsymmetry ? least_permutation(st) : st;
        Value *v = eval(view_expr, root_ctx);
        cur_state = saved;
        return value_hash(v);
    }
    uint64_t h = 0;
    if (!nsymmetry) {
        for (int i = 0; i < nvars; i++) h = fmix(h + elem_hash(st[i]));
        return h;
    }
    /* The least fingerprint of the state's permutations. A successor shares
       most of its values with its state's: each variable's last value and
       its hashes under the permutations, h[p] the same for all if unmoved,
       are kept. */
    static uint64_t *fps, *vh;
    static Value **last;
    static unsigned *last_resets;
    if (!fps) {
        fps = xmalloc(sizeof(uint64_t) * (size_t)nsymmetry);
        vh = xmalloc(sizeof(uint64_t) * (size_t)nsymmetry * (size_t)nvars);
        last = xcalloc((size_t)nvars, sizeof(Value *));
        last_resets = xcalloc((size_t)nvars, sizeof(unsigned));
    }
    memset(fps, 0, sizeof(uint64_t) * (size_t)nsymmetry);
    for (int i = 0; i < nvars; i++) {
        uint64_t *h = vh + (size_t)i * (size_t)nsymmetry;
        if (st[i] != last[i] || last_resets[i] != scratch_resets) {
            if (!permuted_hashes(st[i], h, 0, 0)) {
                uint64_t same = elem_hash(st[i]);
                for (int p = 0; p < nsymmetry; p++) h[p] = same;
            }
            last[i] = st[i];
            last_resets[i] = scratch_resets;
        }
        for (int p = 0; p < nsymmetry; p++) fps[p] = fmix(fps[p] + h[p]);
    }
    uint64_t best = fps[0];
    for (int p = 1; p < nsymmetry; p++) if (fps[p] < best) best = fps[p];
    return best;
}

static int nworkers = 1;   /* processes expanding states; with more than one, the store is shared */

/* A new state whose encoding ends the store. */
static int add_record(size_t off, uint64_t fp, int parent, int action, int depth) {
    if (nstates == capstates) {
        if (nworkers > 1) { fputs("manyan: too many states\n", stderr); exit(MANYAN_ERROR); }
        capstates = capstates ? capstates * 2 : 1024;
        states = xrealloc(states, sizeof(StateRec) * (size_t)capstates);
    }
    StateRec *r = &states[nstates];
    r->fp = fp;
    r->off = off;
    r->len = (int)(store.n - off);
    r->parent = parent;
    r->action = action;
    r->depth = depth;
    r->edges = NULL;
    r->nedges = r->capedges = 0;
    fp_insert(nstates);
    return nstates++;
}

static void store_add(const char *bytes, size_t n) {
    if (nworkers > 1 && store.n + n + 1 > store.cap) { fputs("manyan: too many states\n", stderr); exit(MANYAN_ERROR); }
    buf_add(&store, bytes, n);
}

static int add_state(Value **st, uint64_t fp, int parent, int action, int depth) {
    size_t off = store.n;
    for (int i = 0; i < nvars; i++) encode(&store, st[i]);
    return add_record(off, fp, parent, action, depth);
}

/* ---------------------------------------------------------------- reporting */

static int max_depth = 1;
static int expanded;          /* states taken off the queue */

static void fprint_state(FILE *f, Value **st) {
    if (nvars == 1) {
        fprintf(f, "%s = %s\n", S(vars[0]->name), st[0] ? pretty(st[0]) : "null");
        return;
    }
    for (int i = 0; i < nvars; i++) fprintf(f, "/\\ %s = %s\n", S(vars[i]->name), st[i] ? pretty(st[i]) : "null");
}

static void print_state(Value **st) { fprint_state(stdout, st); }

static int view_trace;   /* -view */

/* With -view, a reported state as its view's value: returns whether it
   printed it. */
static int print_shown(Value **st) {
    if (!view_trace || !view_expr) return 0;
    Value **saved = cur_state;
    cur_state = st;
    printf("%s\n", pretty(eval(view_expr, root_ctx)));
    cur_state = saved;
    return 1;
}

/* An action as TLC names it, an initial predicate without a name as
   `unnamed`; outside a simulation TLC knows no initial predicate's. */
static void action_text(Buf *b, int action, const char *unnamed) {
    if (action < 0 && !simulating) { buf_puts(b, "<Initial predicate>"); return; }
    Action *a = action < 0 ? NULL : &actions[action];
    Expr *l = a ? a->loc : init_where;
    buf_printf(b, "<%s", a ? S(a->name) : init_name ? S(init_name) : unnamed);
    const char *sep = "(";
    for (int i = 0; a && a->op && i < a->op->nparams; i++)
        if (!a->op->params[i]->arity) { buf_printf(b, "%s%s", sep, pretty(force(env_find(a->c.env, a->op->params[i])))); sep = ","; }
    if (*sep == ',') buf_puts(b, ")");
    buf_printf(b, " line %d, col %d to line %d, col %d of module %s>", l->l1, l->c1, l->l2, l->c2, S(l->mod->name));
}

static void action_label(int action) {
    Buf b = {0};
    action_text(&b, action, "Initial predicate");
    fputs(b.s, stdout);
    free(b.s);
}

static int cur_action;

/* TLC rebuilds the states of a trace from their fingerprints by evaluating
   the spec again: all of Init for the first state, then each action in turn
   until one yields the next state. Side effects such as Print happen
   again, so manyan replays the same evaluations for the same output. The
   state found is the first with the fingerprint, which under a view or
   symmetry may be another than the one stored. */
static Value **replay_target;
static uint64_t replay_fp;
static int replay_found;
static Value **replay_match;   /* the state found */
static int replay_checks;     /* also evaluate the properties and invariants, as TLC does replaying Init */
static int check_list(Check *list, int n, Value **st);
static void live_init_lits(void);
static void live_init(Value **st);
static void eval_init_lits(Value **st);
static int live_init_failed;   /* an error in a property on an initial state: its exit status */
static int check_initial(Value **st);

static int replay_emit(void) {
    if (!replay_found) {
        int complete = 1;
        for (int i = 0; i < nvars && complete; i++) complete = gen_target[i] != NULL;
        replay_found = complete && replay_target && fingerprint(gen_target) == replay_fp;
        if (replay_found) {   /* normalized, as a state TLC keeps */
            replay_match = memcpy(NEWN(Value *, nvars), gen_target, sizeof(Value *) * (size_t)nvars);
            for (int i = 0; i < nvars; i++) materialize(replay_match[i]);
        }
    }
    if (replay_checks) {
        if (ntemporal_props && !live_init_failed) eval_init_lits(gen_target);   /* reported */
        /* reported again, as -continue reports it; a property failing on an
           initial state fails again on it first */
        if (keep_going && !live_init_failed) check_initial(gen_target);
        else check_list(invariants, ninvariants, gen_target);
    }
    return 0;
}

/* The step from `from`, at level `level` (Init's 0 if from is NULL), to `to`. */
static int replay(Value **from, Value **to, int64_t level) {
    Value **saved_cur = cur_state, **saved_next = next_state, **saved_target = gen_target;
    int (*saved_emit)(void) = gen_emit;
    int saved_init = gen_init;
    int64_t saved_level = cur_level;
    cur_level = level;
    Value **st = NEWN(Value *, nvars);
    /* A successor not completely specified is no state to find. */
    replay_target = to;
    for (int i = 0; i < nvars && replay_target; i++) if (!to[i]) replay_target = NULL;
    if (replay_target) replay_fp = fingerprint(to);
    replay_found = 0;
    replay_match = to;
    gen_target = st;
    gen_emit = replay_emit;
    /* Model checking draws as the search did; in a simulation TLC's main
       thread rebuilds a behavior, drawing from its generator. */
    JRandom *saved_drawing = drawing, saved_model = draw_model;
    Value **saved_from = draw_from;
    int saved_due = draw_due;
    drawing = &draw_model;
    if (!simulating) draw_restart(from);
    if (!from) {
        gen_init = 1;
        cur_state = st;
        next_state = NULL;
        gen(init_expr, root_ctx, NULL);
    }
    int action = -1;
    for (int a = 0; from && a < nactions && !replay_found; a++) {
        gen_init = 0;
        cur_state = from;
        memset(st, 0, sizeof(Value *) * (size_t)nvars);
        next_state = st;
        gen(actions[a].e, actions[a].c, NULL);
        action = a;
    }
    cur_state = saved_cur; next_state = saved_next; gen_target = saved_target;
    gen_emit = saved_emit; gen_init = saved_init;
    cur_level = saved_level;
    drawing = saved_drawing;
    if (!simulating) draw_model = saved_model, draw_from = saved_from, draw_due = saved_due;
    return action;   /* the action that yields `to`, the last tried if none */
}

/* After an evaluation error TLC evaluates Init, or the next-state action
   of the state it failed in, again to locate the error: from == NULL
   replays Init with its checks. The error happens again and ends it.
   Returns whether an error did. */
static int replay_error(Value **from) {
    sigjmp_buf here, *saved = handler;
    handler = &here;
    tracking = 1;
    for (int i = 0; i <= K_WHILE; i++) eval_tracking[i] = eval_tracked;
    eval_fns = eval_tracking;
    nframes = 0;
    volatile int failed = 1;
    if (!sigsetjmp(here, 0)) {
        replay_checks = !from;
        replay(from, NULL, cur_level);
        failed = 0;
    }
    tracking = 0;
    eval_fns = eval_kind;
    replay_checks = 0;
    handler = saved;
    return failed;
}

static int diff_trace;   /* -difftrace */

/* Whether a variable keeps its value p as v, as TLC compares them: an
   error comparing, as of a string with a number, is a change. */
static int unchanged(Value *p, Value *v) {
    if (!p || !v) return 0;
    EvalState s = eval_save();
    ErrorState e = error_save();
    sigjmp_buf here, *outer = handler;
    handler = &here;
    int same = !sigsetjmp(here, 0) && veq(p, v);
    handler = outer;
    eval_restore(s);
    error_restore(&e);
    return same;
}

/* State number of a trace, reached by action. With -difftrace, only the
   variables that changed from prev, unless prev is NULL. */
/* The definition the configuration names as role, which TLC resolves
   only as it uses it: a POSTCONDITION or the ALIAS. NULL if TLC fails to,
   its error in why. */
static Def *late_def(int name, const char *role, Buf *why) {
    Sym *s = module_lookup(root, name);
    Def *d = s && s->def->kind == D_OP ? s->def : NULL;
    if (!d) buf_printf(why, "The %s %s specified in the configuration file\nis not defined in the specification.", role, S(name));
    else if (d->cache || d->value) buf_printf(why, "The %s %s cannot be a constant.", role, S(name));
    else if (d->nparams) buf_printf(why, "TLC requires %s not to take any argument, but one was given: %s", role, S(name));
    else return d;
    return NULL;
}

static int alias_name;   /* the ALIAS, 0 if none */
static Expr *unfold(Expr *e);

static void state_text(Buf *b, Value **st) {
    for (int i = 0; i < nvars; i++)
        buf_printf(b, "%s%s = %s\n", nvars == 1 ? "" : "/\\ ", S(vars[i]->name), st[i] ? pretty(st[i]) : "null");
}


/* State st of a trace, the level-th, followed by next, as TLC prints it, into b:
   with an ALIAS, the alias's value on the step from st to next is printed
   as the state if it is a record, its fields as variables, in the order a
   record constructor gives them, as TLC prints the record unnormalized; an
   error evaluating it is printed as a variable _ALIASEvalError after st's. */
/* The ALIAS of state st, followed by next, at level; NULL if it fails, why. */
static Value *alias_value(Value **st, Value **next, int level, Buf *why) {
    Def *d = late_def(alias_name, "alias", why);
    Value *v = NULL;
    if (!d) return NULL;
    EvalState saved = eval_save();
    ErrorState error = error_save();
    int64_t saved_level = cur_level;
    sigjmp_buf here;
    handler = &here;
    if (!sigsetjmp(here, 0)) {
        cur_state = st;
        next_state = next;
        cur_level = level;
        v = realize(eval(d->body, root_ctx));
    } else {
        buf_puts(why, error_message.s ? error_message.s : "");
        if (error_expr && error_expr->mod) buf_puts(why, "\n"), node_text(why, error_expr);
    }
    eval_restore(saved);
    error_restore(&error);
    cur_level = saved_level;
    return v;
}

/* What TLC printed of the state before, with an ALIAS: the alias's
   record, or else the state. With -difftrace TLC leaves out the fields
   that it shows unchanged, but an error evaluating the alias. */
static Value *shown_record;
static Value **shown_state;

/* Whether the field name, now v, is as shown before: in record, or else st. */
static int shown_was(Value *record, Value **st, int name, Value *v) {
    Value *was = NULL;
    if (record) {
        for (int i = 0; i < record->n; i++) if (record->u.fcn.keys[i]->u.i == name) was = record->u.fcn.vals[i];
    } else if (st) {
        for (int i = 0; i < nvars; i++) if (vars[i]->name == name) was = st[i];
    }
    return unchanged(was, v);
}

static void trace_state_text(Buf *b, Value **st, Value **next, int level, int diff) {
    if (!alias_name) { state_text(b, st); return; }
    Buf why = {0};
    Value *v = alias_value(st, next, level, &why);
    Def *d = v ? late_def(alias_name, "alias", &why) : NULL;
    Value *was_record = shown_record;
    Value **was_state = shown_state;
    shown_record = v && fcn_is_record(v) ? v : NULL;
    shown_state = st;
    if (v && fcn_is_record(v)) {
        Expr *made = unfold(d->body);
        int fmt = intern("_format");
        const char *format = NULL;
        for (int i = 0; i < v->n; i++) {
            if (v->u.fcn.keys[i]->u.i != fmt) continue;
            if (v->u.fcn.vals[i]->kind != V_STR) fail_java("java.lang.ClassCastException", "");
            format = S(v->u.fcn.vals[i]->u.i);
        }
        for (int i = 0; i < v->n; i++) {
            int k = i;
            for (int j = 0; made->kind == X_RECORD && j < v->n; j++)
                if (v->u.fcn.keys[j]->u.i == made->segs[i].name) k = j;
            if (v->u.fcn.keys[k]->u.i == fmt) continue;
            if (diff && shown_was(was_record, was_state, v->u.fcn.keys[k]->u.i, v->u.fcn.vals[k])) continue;
            const char *key = S(v->u.fcn.keys[k]->u.i), *val = pretty(v->u.fcn.vals[k]);
            if (!format) { buf_printf(b, "%s%s = %s\n", v->n == 1 ? "" : "/\\ ", key, val); continue; }
            const char *cls, *args[] = {key, val}, *why = java_format(b, format, 2, args, &cls);
            if (why) fail_java(cls, why);
        }
        return;
    }
    if (v) { state_text(b, st); return; }
    for (int i = 0; i < nvars; i++)
        if (!diff || !shown_was(was_record, was_state, vars[i]->name, st[i]))
            buf_printf(b, "/\\ %s = %s\n", S(vars[i]->name), st[i] ? pretty(st[i]) : "null");
    buf_printf(b, "/\\ _ALIASEvalError = %s\n", pretty(mk_str(intern(why.s))));
    free(why.s);
}

static void print_trace_state(Value **st, Value **next, int level) {
    Buf b = {0};
    trace_state_text(&b, st, next, level, 0);
    fputs(b.s ? b.s : "", stdout);
    free(b.s);
}

static void print_numbered(int number, int action, Value **st, Value **prev, Value **next) {
    static Buf b;   /* TLC makes the state's text before it prints its number; an error may end it */
    b.n = 0;
    if (b.s) b.s[0] = 0;
    /* With -difftrace TLC prints a state after another as what changed, not as the view. */
    int diff = diff_trace && prev && !alias_name, shown = view_trace && view_expr && !diff;
    if (!diff && !shown) trace_state_text(&b, st, next, number, diff_trace && prev);
    printf("State %d: ", number);
    action_label(action);
    printf("\n");
    if (shown && print_shown(st)) return;   /* no blank line after a view, as TLC prints it */
    if (diff) {
        for (int i = 0; i < nvars; i++)
            if (!unchanged(prev[i], st[i]))
                printf("%s%s = %s\n", nvars == 1 ? "" : "/\\ ", S(vars[i]->name), st[i] ? pretty(st[i]) : "null");
    }
    printf("%s\n", b.s ? b.s : "");
}

/* TLC's report of a Java exception, up to its message. */
static void print_exception(const char *cls, const char *then) {
    printf("Error: TLC threw an unexpected exception.\n"
           "This was probably caused by an error in the spec or model.\n"
           "See the User Output or TLC Console for clues to what happened.\n"
           "The exception was a %s\n%s", cls, then);
}

/* The message of the error that stopped the search, then where it was. */
static void error_text(Buf *b) {
    buf_printf(b, "%s\n", error_message.s ? error_message.s : "");
    if (error_expr && error_expr->mod) node_text(b, error_expr), buf_puts(b, "\n");
}

static void print_error_text(void) {
    Buf b = {0};
    error_text(&b);
    fputs(b.s, stdout);
    free(b.s);
}

/* While TLC rebuilds a behavior, the states it rebuilt up to the one it
   replays from, or prints: Trace's there. */
static Value ***trace_path;
static int ntrace_path;

static void print_trace_states(int s1, Value **s2, int action, int print) {
    int n = 0;
    for (int i = s1; i >= 0; i = states[i].parent) n++;
    int *path = NEWN(int, n);
    Value ***st = NEWN(Value **, n + 1);
    int k = n;
    for (int i = s1; i >= 0; i = states[i].parent) path[--k] = i;
    for (int i = 0; i < n; i++) st[i] = decode_state(path[i]);
    trace_path = st;
    /* Each state as TLC rebuilds it, from the one before as rebuilt. */
    for (int i = 0; i + 1 < n; i++) { ntrace_path = i; replay(i ? st[i - 1] : NULL, st[i], i); st[i] = replay_match; }
    /* The last state is printed whole, as TLC prints it. TLC prints an
       initial one as it has it, but rebuilds it to rebuild the behavior. */
    if (print) printf("Error: The behavior up to this point is:\n");
    for (int i = 0; i + 1 < n && print; i++) {
        ntrace_path = i + 1;
        print_numbered(i + 1, states[path[i]].action, st[i], i ? st[i - 1] : NULL, st[i + 1]);
    }
    ntrace_path = n - 1;
    if (n > 1 || !print) { replay(n > 1 ? st[n - 2] : NULL, st[n - 1], n - 1); st[n - 1] = replay_match; }
    ntrace_path = n;
    if (print) print_numbered(n, states[s1].action, st[n - 1], s2 && n > 1 ? st[n - 2] : NULL, s2 ? s2 : st[n - 1]);
    if (s2) {
        replay(st[n - 1], s2, n);
        st[n] = s2;
        ntrace_path = n + 1;
        if (print) print_numbered(n + 1, action, s2, NULL, s2);
    }
    if (!print) {
        int *acts = NEWN(int, n + 1);
        for (int i = 0; i < n; i++) acts[i] = i ? states[path[i]].action : -1;
        acts[n] = action;
        post_behavior(st, acts, n + (s2 != NULL), 0, 0, 1);
    }
}

/* The error that failed the last behavior printed: its text, its Java exception. */
static Buf trace_failure;
static const char *trace_failure_java;

/* The behavior from an initial state to state s1, then the state s2
   reached from it by `action` if s2 is not NULL, as TLC prints it (print
   2: the error is left unreported). As TLC, an error rebuilding a state
   ends the behavior there, reported as an exception: returns the exit
   status of that error, 0 if none. */
static int trace_states(int s1, Value **s2, int action, int print) {
    EvalState s = eval_save();
    ErrorState e = error_save();
    int failed = 0;
    sigjmp_buf here;
    handler = &here;
    Value ***saved_path = trace_path;
    int saved_n = ntrace_path;
    if (!sigsetjmp(here, 0)) print_trace_states(s1, s2, action, print);
    else {
        failed = eval_failure_status();
        trace_failure.n = 0;
        error_text(&trace_failure);
        trace_failure_java = error_java ? error_java : "tlc2.tool.EvalException";
        if (print == 1) {
            print_exception(trace_failure_java, ": ");
            fputs(trace_failure.s, stdout);
        }
    }
    trace_path = saved_path, ntrace_path = saved_n;
    eval_restore(s);
    error_restore(&e);
    return failed;
}
static int print_trace(int s1, Value **s2, int action) { return trace_states(s1, s2, action, 1); }

static struct { int name, module; } *posts;   /* the POSTCONDITIONs, and the module of each -postCondition */
static int nposts;
/* The _POSSIBLE predicates, and how often each held where evaluated:
   -1 where never evaluated. */
static Check *possibles;
static int npossibles;
static int64_t *possible_counts;

/* Counts an evaluation of a _POSSIBLE predicate, which TLC adds to the
   constraints, as satisfied. */
static int count_possible(Check *c, Value *v) {
    int64_t *w = &possible_counts[c->possible - 1];
    if (*w < 0) *w = 0;
    *w += v->u.i;
    return 1;
}

/* TLC's check of the _POSSIBLE predicates, after the POSTCONDITIONs: at
   the first never witnessed, it prints the counts and fails. */
static int check_possibles(void) {
    for (int i = 0; i < npossibles; i++) {
        if (possible_counts[i] > 0) continue;
        List keys = {0}, vals = {0};
        for (int j = 0; j < npossibles; j++)
            if (possible_counts[j] >= 0) list_add(&keys, mk_str(possibles[j].name)), list_add(&vals, mk_int(possible_counts[j]));
        printf("%s\n", pretty(mk_fcn_from(&keys, &vals)));
        Buf b = {0};
        loc_text(&b, possibles[i].def->body);
        printf("Error: The _POSSIBLE predicate %s at %s was never witnessed.\n"
               "Others may be unwitnessed too; only witnessed predicates appear with a\n"
               "non-zero count in the record printed above.\n"
               "See https://explain.tlapl.us/possible-conditions for additional details.\n", S(possibles[i].name), b.s);
        free(b.s);
        return MANYAN_VIOLATION_ASSUMPTION;
    }
    return 0;
}


/* The postconditions checked as TLC checks them once the search is done,
   or after an error it reported (after_error), in order: the first that
   is false or fails is reported, with its exit status but after an error.
   As TLC, each name is resolved first, and an error resolving one stops
   the check: the simulator reports it plainly, with its status, even
   after an error; the model checker as an unexpected exception, but
   ignores it after an error, or with -continue reports it and returns -1. */
static int check_posts(int after_error) {
    Def **d = NEWN(Def *, nposts + 1);
    for (int i = 0; i < nposts; i++) {
        Buf why = {0};
        Sym *s = posts[i].module ? module_lookup(find_module(posts[i].module), posts[i].name) : NULL;
        if (posts[i].module && s && s->def->kind == D_OP) d[i] = s->def;
        else if (posts[i].module) buf_printf(&why, "Could not find operator: %s in module: %s", S(posts[i].name), S(posts[i].module));
        else d[i] = late_def(posts[i].name, "post condition", &why);
        if (d[i]) continue;
        if (simulating) printf("Error: %s\n", why.s);
        else if (!after_error || keep_going) {
            print_exception("java.lang.RuntimeException", ": ");
            printf("%s\n", why.s);
        }
        free(why.s);
        post_trace.n = 0;
        return simulating ? MANYAN_ERROR_CONFIG : !after_error ? MANYAN_ERROR : keep_going && !simulating ? -1 : 0;
    }
    EvalState saved = eval_save();
    ErrorState error = error_save();
    int64_t level = cur_level;
    cur_state = next_state = NULL;
    cur_level = 0;
    arena = &scratch_arena;   /* records keep their order as written, for JsonSerialize */
    Region *r = region_open();
    int status = 0;
    sigjmp_buf here;
    handler = &here;
    checking_posts = 1;
    for (int i = 0; i < nposts && !status; i++) {
        Buf b = {0};
        loc_text(&b, d[i]->body);
        if (sigsetjmp(here, 0)) {
            printf("Error: Evaluating postcondition %s at %s failed.\n", S(posts[i].name), b.s);
            print_error_text();
            free(b.s);
            status = MANYAN_VIOLATION_ASSUMPTION;
            continue;
        }
        Value *v = eval(d[i]->body, root_ctx);
        if (v->kind != V_BOOL) {
            printf("Error: Evaluating postcondition %s at %s failed.\n"
                   "TLC expected a boolean value, but did not find one. %s\n", S(posts[i].name), b.s, b.s);
            status = MANYAN_VIOLATION_ASSUMPTION;
        } else if (!v->u.i) {
            printf("Error: Postcondition %s at %s is false.\n", S(posts[i].name), b.s);
            status = MANYAN_VIOLATION_ASSUMPTION;
        }
        free(b.s);
    }
    if (!status) status = check_possibles();
    checking_posts = 0;
    post_trace.n = 0;
    region_close(r);
    eval_restore(saved);
    error_restore(&error);
    cur_level = level;
    return after_error ? 0 : status;
}

/* An error TLC reports for a state, or a step from it to s2, is followed
   by its rebuilding the behavior for its POSTCONDITIONs, which evaluates
   Init and Next again, then checking them. */
static void rebuild_for_posts(int s1, Value **s2, int action) {
    trace_states(s1, s2, action, 0);
    check_posts(1);
}

static int reported_trace(int s1, Value **s2, int action) {
    int failed = print_trace(s1, s2, action);
    rebuild_for_posts(s1, s2, action);
    return failed;
}

/* TLC's report of an error evaluating a step from state s1, to s2 by
   action: an error of its own evaluator as an unexpected exception, one
   of a standard module's operators plainly. */
static void print_next_failure(int s1, Value **s2, int action, int status) {
    if (status == MANYAN_FAILURE_EVAL && error_module != 1)
        print_exception("java.lang.RuntimeException", ": ");
    else
        printf("Error: ");
    print_error_text();
    print_trace(s1, s2, action);
}

static void print_counts(int queued) {
    printf("%ld states generated, %d distinct states found, %d states left on queue.\n", generated, nstates + npicked_explored, queued);
    printf("The depth of the complete state graph search is %d.\n", generated ? max_depth : 0);
    fflush(stdout);
}

static void print_error_message(void) {
    printf("Error: %s", error_message.s ? error_message.s : "");
    if (error_expr && error_expr->mod) {
        Buf b = {0};
        node_text(&b, error_expr);
        printf("\n%s", b.s);
        free(b.s);
    }
    printf("\n");
}

/* ---------------------------------------------------------------- search */

static int expanding = -1;    /* the state whose successors are generated */
static Value **expanding_state;
static Value **succ;          /* the assignment the generator fills */
static int succ_count;
static int violation;         /* the exit status of the first violation, 0 if none */

/* The check being evaluated, and its state, when an error stops it. */
static Check *error_check;
static Value **error_state;

/* Whether the check an error stopped is one of list. */
static int checking(Check *list, int n) { return error_check && n && error_check >= list && error_check < list + n; }
static int checking_invariant(void) { return checking(invariants, ninvariants); }

/* Whether the error is TLC's EvalException, not one of its own
   TLCRuntimeExceptions, which some of its callers catch. */
static int eval_exception(void) { return error_status == MANYAN_VIOLATION_ASSERT || error_module == 1; }

/* A formula that is no boolean, an error TLC raises outside its evaluator. */
static _Noreturn void not_boolean_formula(Expr *e) {
    error_reset();
    buf_puts(&error_message, "TLC expected a boolean value, but did not find one. ");
    node_text(&error_message, e);
    error_status = MANYAN_FAILURE_EVAL;
    stackless = 1;
    raise_error();
}

static _Noreturn void not_boolean_check(Check *c) {
    not_boolean_formula(c->def && c->def->body && c->expr->kind == K_CALL && c->expr->def == c->def ? c->def->body : c->expr);
}

/* The first of the checks that st, a step after the state at cur_level
   (Init's 0), fails, or -1. */
static int check_list(Check *list, int n, Value **st) {
    Value **saved = cur_state, **target = gen_target;
    cur_state = st;
    gen_target = NULL;   /* st is complete */
    cur_level++;
    int bad = -1;
    for (int i = 0; i < n && bad < 0; i++) {
        error_check = &list[i];
        error_state = st;
        /* TLC keeps a constraint's definition where a literal keeps its value. */
        Expr *body = list[i].def ? list[i].def->body : NULL;
        if (list == constraints && body && (body->kind == X_NUM || body->kind == X_STR))
            fail("class tla2sany.semantic.OpDefNode cannot be cast to class tlc2.value.impl.Value "
                 "(tla2sany.semantic.OpDefNode and tlc2.value.impl.Value are in unnamed module of loader 'app')");
        Value *v = eval(list[i].expr, list[i].ctx);
        if (v->kind != V_BOOL) {
            cur_state = saved;
            gen_target = target;
            cur_level--;
            not_boolean_check(&list[i]);
        }
        if (!(list[i].possible ? count_possible(&list[i], v) : v->u.i)) bad = i;
    }
    error_check = NULL;
    error_state = NULL;
    cur_state = saved;
    gen_target = target;
    cur_level--;
    return bad;
}

static int check_actions(Check *list, int n, Value **from, Value **to) {
    Value **saved_cur = cur_state, **saved_next = next_state;
    cur_state = from;
    next_state = to;
    int bad = -1;
    for (int i = 0; i < n && bad < 0; i++) {
        error_check = &list[i];
        error_state = to;
        Value *v = eval(list[i].expr, list[i].ctx);
        if (v->kind != V_BOOL) not_boolean_check(&list[i]);
        if (!(list[i].possible ? count_possible(&list[i], v) : v->u.i)) bad = i;
    }
    error_check = NULL;
    error_state = NULL;
    cur_state = saved_cur;
    next_state = saved_next;
    return bad;
}

#define STUTTER (-2)

/* An edge of the state graph, kept for liveness checking: target and action. */
static void add_edge(int from, int to, int action) {
    StateRec *r = &states[from];
    for (int i = 0; i < r->nedges; i++) if (r->edges[2 * i] == to) return;
    if (r->nedges == r->capedges) {
        r->capedges = r->capedges ? r->capedges * 2 : 4;
        r->edges = xrealloc(r->edges, sizeof(int) * 2 * (size_t)r->capedges);
    }
    r->edges[2 * r->nedges] = to;
    r->edges[2 * r->nedges + 1] = action;
    r->nedges++;
}

/* The state graph in dot, as TLC's -dump dot writes it: each state as
   it is found, an initial one filled, and each step as it is taken; then
   by depth the initial states and those a step was taken from. */
static FILE *dump_file;
static int dump_actions;
static int *dump_ranked, dump_nranked;

static void dump_rank(int idx) {
    if (dump_nranked && dump_ranked[dump_nranked - 1] == idx) return;
    dump_ranked = xrealloc(dump_ranked, sizeof(int) * (size_t)(dump_nranked + 1));
    dump_ranked[dump_nranked++] = idx;
}

static void dump_node(int idx, Value **st) {
    Buf b = {0};
    for (int i = 0; i < nvars; i++) {
        if (i) buf_puts(&b, "\\n");
        if (nvars > 1) buf_puts(&b, "/\\\\ ");
        buf_printf(&b, "%s = ", S(vars[i]->name));
        for (const char *c = st[i] ? pretty(st[i]) : "null"; *c; c++) {
            if (*c == '\n') { buf_puts(&b, "\\n"); continue; }
            if (*c == '\\' || *c == '"') buf_add(&b, "\\", 1);
            buf_add(&b, c, 1);
        }
    }
    if (states[idx].parent < 0) fprintf(dump_file, "%lld [label=\"%s\",style = filled]\n", (long long)states[idx].fp, b.s);
    else fprintf(dump_file, "%lld [label=\"%s\",tooltip=\"%s\"];\n", (long long)states[idx].fp, b.s, b.s);
    free(b.s);
    if (states[idx].parent < 0) dump_rank(idx);
}

static void dump_edge(int from, int to, int action) {
    if (states[from].parent >= 0) dump_rank(from);
    fprintf(dump_file, "%lld -> %lld [label=\"%s\",color=\"black\",fontcolor=\"black\"];\n", (long long)states[from].fp,
            (long long)states[to].fp, dump_actions ? S(actions[action].name) : "");
}

static void dump_close(void) {
    for (int i = 0; i < dump_nranked; i++) {
        int s = dump_ranked[i];
        if (!i || states[s].depth != states[dump_ranked[i - 1]].depth) fprintf(dump_file, "%s{rank = same; ", i ? "}\n" : "");
        fprintf(dump_file, "%lld;", (long long)states[s].fp);
    }
    fprintf(dump_file, "%s}\n}", dump_nranked ? "}\n" : "");
    fclose(dump_file);
    dump_file = NULL;
    free(dump_ranked);
    dump_ranked = NULL;
    dump_nranked = 0;
}

/* An initial state checked as TLC checks it: the invariants, then the
   properties that are state predicates. Returns the exit status of a
   violation, which it reports, or 0. */

static int check_initial(Value **st) {
    int bad = check_list(invariants, ninvariants, st);
    if (bad >= 0) {
        printf("Error: Invariant %s is violated by the initial state:\n", S(invariants[bad].name));
        if (!print_shown(st)) print_trace_state(st, st, 1), printf("\n");   /* no blank line after a view */
        post_behavior(&st, (int[]){-1}, 1, 0, 0, 0);
        if (!keep_going || simulating) return MANYAN_VIOLATION_SAFETY;   /* TLC's simulator stops */
    }
    bad = check_list(implied_inits, nimplied_inits, st);
    if (bad >= 0) {
        printf("Error: Property %s is violated by the initial state:\n", S(implied_inits[bad].name));
        if (!print_shown(st)) print_trace_state(st, st, 1), printf("\n");   /* no blank line after a view */
        post_behavior(&st, (int[]){-1}, 1, 0, 0, 0);
        return MANYAN_VIOLATION_LIVENESS;
    }
    return 0;
}

/* TLC's error for a successor st of cur_action that leaves variables out. */
static void print_unspecified(Value **st) {
    int unassigned = 0;
    for (int i = 0; i < nvars; i++) unassigned += !st[i];
    printf("Error: Successor state is not completely specified by ");
    if (nactions == 1) printf("the next-state action");
    else printf("action %s of the next-state relation", S(actions[cur_action].name));
    printf(". The following variable%s not defined: ", unassigned == 1 ? " is" : "s are");
    for (int i = 0, k = 0; i < nvars; i++) if (!st[i]) printf("%s%s", k++ ? ", " : "", S(vars[i]->name));
    printf(".\n\n");
}

static int init_emit(void) {
    for (int i = 0; i < nvars; i++)
        if (!succ[i]) fail("The variable %s was not assigned a value by the initial predicate.", S(vars[i]->name));
    generated++;
    Value **st = NEWN(Value *, nvars);
    memcpy(st, succ, sizeof(Value *) * (size_t)nvars);
    if (check_list(constraints, nconstraints, st) >= 0) {   /* as TLC, checked though not kept */
        violation = check_initial(st);
        return violation != 0;
    }
    error_state = st;
    uint64_t fp = fingerprint(st);
    error_state = NULL;
    if (fp_find(fp) >= 0) return 0;
    int idx = add_state(st, fp, -1, -1, 1);
    if (dump_file) dump_node(idx, st);
    if (ntemporal_props) live_init(st);
    Region *r = region_open();   /* what checking the state made: one of many */
    violation = check_initial(st);
    region_close(r);
    return violation != 0;
}

/* PickSuccessor(e): TRUE where e is, else the user's answer on standard
   input, as TLC asks for it, of each step whose successor is not yet
   seen: yes (or an empty line), no, explored (yes, but go no further from
   it: seen, as in TLC's set of fingerprints), or show the states or what
   changes. Of a state or a step not yet complete, TRUE. */
static uint64_t *picked_explored;
static int picked_seen(uint64_t fp) {
    for (int i = 0; i < npicked_explored; i++) if (picked_explored[i] == fp) return 1;
    return 0;
}
NATIVE(n_picksuccessor) {
    UNUSED;
    if (a) return TRUEV;
    if (in_worker) worker_cannot();
    int complete = next_state != NULL;
    for (int i = 0; complete && i < nvars; i++) complete = next_state[i] != NULL;
    uint64_t fp = complete && !simulating ? fingerprint(next_state) : 0;
    if (complete && !simulating && (fp_find(fp) >= 0 || picked_seen(fp))) return TRUEV;   /* in the model already */
    Value *g = eval(call->args[0], c);
    if (g->kind != V_BOOL)
        fail("In evaluating TLCExt!PickSuccessor, a non-boolean expression (%s) was used as the condition of an IF.\n%s",
             kind_string(g), node_str(call->args[0]));
    if (g == TRUEV || !complete) return TRUEV;
    char *line = NULL;
    size_t cap = 0;
    for (;;) {
        printf("Extend behavior of length %ld with a \"%s\" step [<Action %s>]? (Yes/no/explored/states/diff):\n",
               (long)cur_level, S(actions[cur_action].name), loc_str(actions[cur_action].e));
        fflush(stdout);
        ssize_t n = getline(&line, &cap, stdin);
        if (n < 0) { free(line); fail("No line found"); }   /* Java's Scanner at the end of the input */
        if (n && line[n - 1] == '\n') line[--n] = 0;
        int blank = 1;
        for (ssize_t i = 0; i < n; i++) blank &= isspace((unsigned char)line[i]) != 0;
        char first = (char)tolower((unsigned char)line[0]);
        if (blank || first == 'y') break;
        if (line[0] == 'n') { free(line); return FALSEV; }
        Buf b = {0}, t = {0};
        if (line[0] == 's') {
            state_text(&b, cur_state), state_text(&t, next_state);
            while (b.n && b.s[b.n - 1] == '\n') b.s[--b.n] = 0;
            while (t.n && t.s[t.n - 1] == '\n') t.s[--t.n] = 0;
            printf("%s\n~>\n%s\n", b.s, t.s);
        } else if (line[0] == 'd') {
            for (int i = 0; i < nvars; i++)
                if (!veq(cur_state[i], next_state[i])) buf_printf(&b, "%s%s = %s\n", nvars == 1 ? "" : "/\\ ", S(vars[i]->name), pretty(next_state[i]));
            printf("%s\n", b.s ? b.s : "");
        } else if (line[0] == 'e') {
            if (simulating) printf("Marking a state explored is unsupported by the current TLC mode. Is TLC running in simulation mode?\n");
            else {
                picked_explored = xrealloc(picked_explored, sizeof *picked_explored * (size_t)(npicked_explored + 1));
                picked_explored[npicked_explored++] = fp;
                break;
            }
        }
        free(b.s), free(t.s);
    }
    free(line);
    return TRUEV;
}
/* Whether the state a violation reports was new: as TLC, it is not queued. */
static int violation_fresh;

/* With -continue, the behavior to st, which violates the check named:
   TLC prints it inside its check, without a postcondition, so an error
   printing it fails the check, and then the step, which stops the search. */
static int continued_trace(const char *check, int name, Value **st) {
    int failed = trace_states(expanding, st, cur_action, 2);
    if (!failed) return 0;
    char *why = strdup(trace_failure.s);
    const char *java = trace_failure_java;
    printf("Error: Evaluating %s %s failed.\n%s", check, S(name), why);
    print_trace(expanding, st, cur_action);
    if (strcmp(java, "tlc2.tool.EvalException")) print_exception(java, ": ");
    else printf("Error: ");   /* an EvalException of TLC's own, plainly */
    fputs(why, stdout);
    print_trace(expanding, st, cur_action);
    free(why);
    violation = MANYAN_ERROR;
    /* TLC replays the step, which may now fail: an error of the step. */
    if (replay_error(expanding_state)) {
        violation = eval_failure_status();
        print_next_failure(expanding, NULL, 0, violation);
        printf("\n");
    }
    return failed;
}

/* Whether a step to st violates an action property, which TLC checks
   for every step. */
static int action_violated(Value **st) {
    int bad = check_actions(action_props, naction_props, cur_state, st);
    if (bad < 0) return 0;
    printf("Error: Action property %s is violated.\n", S(action_props[bad].name));
    if (keep_going) {
        if (!continued_trace("action property", action_props[bad].name, st)) return 0;
        /* TLC checks the step again as it replays it, to the same error. */
        printf("Error: Action property %s is violated.\n", S(action_props[bad].name));
        violation = continued_trace("action property", action_props[bad].name, st);
        return 1;
    }
    reported_trace(expanding, st, cur_action);
    violation = MANYAN_VIOLATION_LIVENESS;
    return 1;
}

/* Whether a successor is being fingerprinted: TLC does it outside Next. */
static int fingerprinting;

static int next_emit(void) {
    succ_count++;
    generated++;
    int unassigned = 0;
    for (int i = 0; i < nvars; i++) unassigned += !succ[i];
    if (unassigned) {
        /* TLC looks the successor up among its workers' states for the
           postconditions, to an ArrayIndexOutOfBoundsException; it reports
           it with -continue, and the error again as it replays it. */
        print_unspecified(succ);
        print_trace(expanding, succ, cur_action);
        if (keep_going) {
            print_exception("java.lang.ArrayIndexOutOfBoundsException", ": Index 32767 out of bounds for length 1\n");
            print_trace(expanding, succ, cur_action);
            print_unspecified(succ);
            print_trace(expanding, succ, cur_action);
        }
        violation = MANYAN_FAILURE_EVAL;
        violation_fresh = 0;
        return 1;
    }
    Value **st = NEWN(Value *, nvars);
    memcpy(st, succ, sizeof(Value *) * (size_t)nvars);
    /* As TLC: a state outside the model is not kept, but its invariants
       are checked each time it is found. */
    if (check_list(constraints, nconstraints, st) >= 0 || check_actions(action_constraints, naction_constraints, cur_state, st) >= 0) {
        int bad = check_list(invariants, ninvariants, st);
        violation_fresh = 0;
        if (bad >= 0) {
            printf("Error: Invariant %s is violated.\n", S(invariants[bad].name));
            if (keep_going) {
                if (continued_trace("invariant", invariants[bad].name, st)) return 1;
            } else {
                reported_trace(expanding, st, cur_action);
                violation = MANYAN_VIOLATION_SAFETY;
                return 1;
            }
        }
        return action_violated(st);
    }
    fingerprinting = 1;
    uint64_t fp = fingerprint(st);
    fingerprinting = 0;
    int found = fp_find(fp);
    if (found < 0 && npicked_explored && picked_seen(fp)) return action_violated(st);   /* seen, as PickSuccessor marked it */
    if (found >= 0 && ntemporal_props) add_edge(expanding, found, cur_action);
    if (found >= 0 && dump_file) dump_edge(expanding, found, cur_action);
    violation_fresh = found < 0;
    if (found < 0) {
        int depth = states[expanding].depth + 1;
        int idx = add_state(st, fp, expanding, cur_action, depth);
        if (dump_file) dump_edge(expanding, idx, cur_action), dump_node(idx, st);
        if (depth > max_depth) max_depth = depth;
        int bad = check_list(invariants, ninvariants, st);
        if (ntemporal_props) add_edge(expanding, idx, cur_action);
        if (bad >= 0) {
            printf("Error: Invariant %s is violated.\n", S(invariants[bad].name));
            if (keep_going) {
                if (continued_trace("invariant", invariants[bad].name, st)) return 1;
            } else {
                reported_trace(expanding, st, cur_action);
                violation = MANYAN_VIOLATION_SAFETY;
                return 1;
            }
        }
    }
    if (action_violated(st)) return 1;
    violation_fresh = 0;
    return 0;
}

static time_t started;   /* when checking began, for TLCGet("duration") */

static long sim_traces_max = -1, sim_depth = 100;   /* a simulation's -simulate num= and -depth */

/* A record of n fields, its names interned in this order, as TLC makes its own. */
static Value *mk_record(int n, const char *const *names, Value *const *vals) {
    List keys = {0}, l = {0};
    for (int i = 0; i < n; i++) list_add(&keys, mk_str(intern(names[i]))), list_add(&l, vals[i]);
    Value *r = mk_fcn_from(&keys, &l);
    r->made = MADE_RECORD;
    return r;
}

static Value *empty_counter_example;

/* The record of state i of n: its ALIAS's on the step from it, as TLC
   evaluates it, if aliased, else of its variables. */
static Value *post_state(Value ***st, int n, int i, int aliased) {
    Buf why = {0};
    int depth = java_depth;   /* TLC evaluates the ALIAS before the postconditions */
    java_depth = 0;
    Value *alias = aliased ? alias_value(st[i], st[i + 1 < n ? i + 1 : i], i + 1, &why) : NULL;
    java_depth = depth;
    List keys = {0}, vals = {0};
    for (int v = 0; v < nvars; v++) list_add(&keys, mk_str(vars[v]->name)), list_add(&vals, st[i][v]);
    if (aliased && !alias)   /* TLC's record of the state, with why */
        list_add(&keys, mk_str(intern("_ALIASEvalError"))), list_add(&vals, mk_str(intern(why.s ? why.s : "")));
    free(why.s);
    if (alias && fcn_is_record(alias)) return alias;
    Value *r = mk_fcn_from(&keys, &vals);
    r->made = MADE_RECORD;
    r->range = r->n == nvars;
    return r;
}

static void post_behavior(Value ***st, const int *act, int n, int loop, int loop_act, int aliased) {
    aliased = alias_name ? aliased : 0;
    Value **rec = NEWN(Value *, n);
    for (int i = 0; i < n && aliased == 1; i++) rec[i] = post_state(st, n, i, 1);
    if (!nposts) return;
    /* kept for good: the arena of the states may be reset before the check */
    Arena *saved = arena;
    arena = &perm_arena;
    post_trace.st = NEWN(Value **, n);
    post_trace.rec = NEWN(Value *, n);
    for (int i = 0; i < n; i++) {
        post_trace.st[i] = NEWN(Value *, nvars);
        for (int v = 0; v <= nvars; v++) {
            Value *x = v < nvars ? st[i][v] : rec[i];
            long budget = INT64_MAX;
            Value *kept = x ? copy_value(x, &budget) : NULL;
            *(v < nvars ? &post_trace.st[i][v] : &post_trace.rec[i]) = kept ? kept : x;
        }
    }
    arena = saved;
    post_trace.act = memcpy(xrealloc(post_trace.act, sizeof(int) * (size_t)n), act, sizeof(int) * (size_t)n);
    post_trace.n = n, post_trace.loop = loop, post_trace.loop_act = loop_act, post_trace.aliased = aliased;
    post_trace.value = NULL;
}

/* A CounterExample: TLC sorts its fields as it interned them, "state"
   first when it sets up a trace spec but has not read _JsonTrace. */
static Value *counter_example_record(Value *states, Value *steps) {
    if (!te_spec) return mk_record(2, (const char *[]){"action", "state"}, (Value *[]){steps, states});
    return mk_record(2, (const char *[]){"state", "action"}, (Value *[]){states, steps});
}

static Value *counter_example(void) {
    if (!checking_posts || !post_trace.n || (simulating && keep_going && post_trace.n > 1)) {   /* TLC's simulator keeps no behavior to go on */
        if (!empty_counter_example) {
            Arena *saved = arena;
            arena = &perm_arena;
            empty_counter_example = counter_example_record(mk_set(0), mk_set(0));
            arena = saved;
        }
        return empty_counter_example;
    }
    if (post_trace.value) return post_trace.value;
    int n = post_trace.n;
    Value **node = NEWN(Value *, n), *states = mk_set(n), *steps = mk_set(n - 1 + (post_trace.loop > 0));
    for (int i = 0; i < n; i++) {
        node[i] = mk_tuple(2);
        node[i]->u.fcn.vals[0] = mk_int(i + 1);
        node[i]->u.fcn.vals[1] = post_trace.rec[i] ? post_trace.rec[i] : post_state(post_trace.st, n, i, post_trace.aliased);
        states->u.set.elems[i] = node[i];
    }
    for (int i = 0; i < steps->n; i++) {
        Value *step = steps->u.set.elems[i] = mk_tuple(3);
        int last = i + 1 == n;   /* the lasso's step back */
        step->u.fcn.vals[0] = node[i];
        int act = last ? post_trace.loop_act : post_trace.act[i + 1];
        step->u.fcn.vals[1] = action_value(act < 0 ? -2 : act);   /* TLC knows no action of an initial state */
        step->u.fcn.vals[2] = node[last ? post_trace.loop - 1 : i + 1];
    }
    return post_trace.value = counter_example_record(set_normalize(states), set_normalize(steps));
}

/* ToTrace(ce): the states of a CounterExample, in order. */
static Value *counter_trace(Value *ce) {
    if (!ce || (ce != post_trace.value && ce != empty_counter_example))
        fail_module("The argument of ToTrace should be a CounterExample, but instead it is:\n%s", pretty(ce));
    Value *states = ce->u.fcn.vals[fcn_index(ce, mk_str(intern("state")))];
    Value *t = mk_tuple(states->n);
    for (int i = 0; i < states->n; i++) {
        Value *node = states->u.set.elems[i];
        t->u.fcn.vals[node->u.fcn.vals[0]->u.i - 1] = node->u.fcn.vals[1];
    }
    return t;
}

/* TLCGet("config") of a search or a simulation: TLC's fields but those
   naming its fingerprint polynomial and its jar. TLC's aril is "0",
   whatever -aril says. */
static Value *search_config(void) {
    char seed[24];
    snprintf(seed, sizeof seed, "%lld", (long long)draw_seed);
    const char *names[] = {"mode", "deadlock", "worker", "seed", "traces", "depth", "aril", "sched"};
    Value *vals[] = {mk_str(intern(generating ? "generate" : simulating ? "simulate" : "bfs")), BOOLV(check_deadlock), mk_int(nworkers),
                     mk_str(intern(seed)), mk_int(sim_traces_max), mk_int(sim_depth), mk_str(intern("0")),
                     mk_str(intern("random"))};
    return mk_record(simulating ? 8 : 4, names, vals);
}

/* TLCGet("revision"): that of the TLC whose behavior manyan follows, the
   Makefile's oracle. */
static Value *tlc_revision(void) {
    const char *names[] = {"timestamp", "date", "count", "tag", "calver"};
    Value *vals[] = {mk_int(1794003837), mk_str(intern("2026-11-06T22:23:57.662Z")), mk_int(9088),
                     mk_str(intern("d8fb231")), mk_str(intern("2026.11.06.222357"))};
    return mk_record(5, names, vals);
}

/* TLCGet's counters of the search, -1 for another key. As TLC, a new
   successor joins the queue once checked; a simulation counts none but
   the time. */
static int64_t search_counter(const char *key) {
    if (!strcmp(key, "duration")) return time(NULL) - started;
    int which = !strcmp(key, "distinct") ? 1 : !strcmp(key, "queue") ? 2 : !strcmp(key, "diameter") ? 3
              : !strcmp(key, "generated") && checking_posts ? 4 : 0;
    if (!which || simulating) return -1;
    if (in_worker) worker_cannot();   /* the counts are the search's, not a worker's */
    return which == 1 ? nstates : which == 2 ? nstates - expanded - violation_fresh : which == 3 ? max_depth : generated;
}

static void collect_fairnesses(void);
static int live_violated(void);
static int live_cut_violated(void);
static int live_error(void);
/* The states generated when each state had been expanded, with temporal
   properties: TLC reports an error in them with these counts. */
static long *gen_after;
static int ngen_after;
static int live_cut = -1;   /* the state TLC stopped expanding at in its temporal checks */
static void note_expanded(int idx) {
    if (!ntemporal_props) return;
    if (idx >= ngen_after) {
        ngen_after = idx + 1 > 2 * ngen_after ? idx + 1 : 2 * ngen_after;
        gen_after = xrealloc(gen_after, sizeof(long) * (size_t)ngen_after);
    }
    gen_after[idx] = generated;
}

/* TLC adds a deadlocked state to its temporal checks after reporting it:
   a finite counterexample ending there is reported too. Returns whether
   one was. */
static int live_after_deadlock(int idx) {
    note_expanded(idx);
    Arena *saved = arena;
    arena = &perm_arena;
    collect_fairnesses();
    sigjmp_buf live;
    handler = &live;
    volatile int found = 0;
    if (!sigsetjmp(live, 0)) found = live_cut_violated() != 0;
    handler = NULL;
    arena = saved;
    return found;
}

/* The counts TLC reports when it stops in its temporal checks, once
   state s had been expanded. */
static void print_counts_after(int s) {
    int seen = 0;
    while (seen + 1 < nstates && states[seen + 1].parent == -1) seen++;
    for (int i = 0; i <= s; i++)
        for (int e = 0; e < states[i].nedges; e++) if (states[i].edges[2 * e] > seen) seen = states[i].edges[2 * e];
    printf("%ld states generated, %d distinct states found, %d states left on queue.\n", gen_after[s], seen + 1, seen - s);
    printf("The depth of the complete state graph search is %d.\n", states[seen].depth);
}

/* Expands state idx: its successors join the search. Returns the exit
   status of a violation it reports, 0 if none. */
static int expand_state(int idx) {
    expanding = idx;
    expanded = idx + 1;
    cur_level = states[idx].depth;
    cur_state = expanding_state = decode_state(idx);
    draw_restart(cur_state);
    succ_count = 0;
    for (int a = 0; a < nactions; a++) {
        cur_action = a;
        memset(succ, 0, sizeof(Value *) * (size_t)nvars);
        next_state = succ;
        gen_target = succ;
        gen(actions[a].e, actions[a].c, NULL);
        if (violation) {
            print_counts(nstates - expanded - violation_fresh);
            return violation;
        }
    }
    if (succ_count == 0 && check_deadlock) {
        printf("Error: Deadlock reached.\n");
        print_trace(idx, NULL, 0);
        trace_states(idx, NULL, 0, 0);
        /* With -continue TLC's worker fails resolving a postcondition, or
           stops its temporal checks with an exception it reports; it
           replays the step, deadlocked again. */
        int again = check_posts(1) < 0;
        if (!again && ntemporal_props && live_after_deadlock(idx) && keep_going) {
            print_exception("tlc2.tool.INextStateFunctor$InvariantViolatedException", ": Invariant violated\n");
            print_trace(idx, NULL, 0);
            again = 1;
        }
        if (again) {
            printf("Error: Deadlock reached.\n");
            print_trace(idx, NULL, 0);
        }
        print_counts(nstates - expanded);
        return MANYAN_VIOLATION_DEADLOCK;
    }
    note_expanded(idx);
    arena_reset(&scratch_arena);
    return 0;
}

/* ---------------------------------------------------------------- workers */

/* Worker processes expand the states of a level in batches. They read the
   store, the state records and the fingerprint set, which live in shared
   memory, and write what they find to their own shared regions: for each
   state, whether it is clean (no error, violation or deadlock to report)
   and its successors in order. A successor not seen as the level started
   is claimed in a table the workers share; the worker that claims it
   checks the invariants and keeps its encoding, once. The search merges
   the batches in order as they are done, taking a new state's encoding
   from its claim; states it adds meanwhile are in a fingerprint table the
   workers do not read, so they claim them as new. It
   expands a state that is not clean, or that is the first to reach a
   state whose invariants failed, itself, so it reports exactly what one
   process would. */
#define PARALLEL_LEVEL 256    /* smaller levels are expanded by the search alone */
#define BATCH 32
#define CLAIM_CHUNK 64

/* A successor: the state it is if seen as the level started, NEW with
   its claim, or CONSTRAINED. */
typedef struct { uint64_t fp; int action; int seen; uint32_t claim; } Found;
enum { NEW = -1, CONSTRAINED = -2 };
typedef struct { int worker; size_t off; atomic_int done; } Batch;
enum { EXPAND, INIT, ATOMS, GROUPS, OFFERS, STEPS, PEMS };   /* a batch's job: expand states, compute Init's slices, a property's atoms, check groups of error models, the offers' and the <>[] conditions on the product, search error models */
typedef struct { _Atomic uint64_t key; atomic_int state; int len; uint64_t loc; int merged; } Claim;
enum { CLAIMED, SETTLED, FAILED };    /* a claim's state: its invariants unchecked, held, or not */

typedef struct {
    atomic_int next;          /* the next batch to take */
    int lo, hi, nbatches;     /* the level, Init's slices or the states for liveness */
    int job, per;             /* what of them a batch of per is */
    atomic_int starved;       /* a worker found the claim table full */
    FpSlot *fp_table;         /* the fingerprint set as the level starts */
    int fp_size;
    size_t nclaims;           /* the claim table's size, a power of two */
    atomic_size_t claimed;
} Control;

static Control *control;
static Batch *batches;
static Claim *claims;
static char **results, **encodings;   /* each worker's regions */
static int (*to_worker)[2], (*from_worker)[2];
static pid_t *worker_pids;
static int workers_running, forked_strs;
static double growth = 1;      /* new states per state expanded, on the last level */
static size_t max_claims, results_size, encodings_size;

/* What a worker's successors may fill of its results, the headers of a
   batch kept. */
static size_t results_room(void) { return results_size - BATCH * 2 * sizeof(int); }

static int w_id;               /* in a worker: its number */
static size_t w_n, w_encoded;  /* bytes used of its regions */
static size_t w_budget;        /* claims it may still make this level */
static int w_clean, w_found;
static Buf w_bytes;

#ifndef MAP_NORESERVE
#define MAP_NORESERVE 0
#endif

static void *shared(size_t bytes) {
    void *p = mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_SHARED | MAP_ANON | MAP_NORESERVE, -1, 0);
    if (p == MAP_FAILED) { fputs("manyan: cannot reserve shared memory for workers\n", stderr); exit(MANYAN_ERROR); }
    return p;
}

/* Puts the store, the state records and the fingerprint set in shared
   memory. Linux and macOS reserve it as it is touched; Windows commits all
   Cygwin maps, so there every region is halved until all fit in a quarter
   of the memory. */
static void share_search(void) {
    int shift = 0;
#ifdef __CYGWIN__
    size_t memory = (size_t)sysconf(_SC_PHYS_PAGES) * (size_t)sysconf(_SC_PAGESIZE);
    size_t all = ((size_t)1 << 37) + sizeof(StateRec) * ((size_t)1 << 29) + ((size_t)1 << 36) +
                 sizeof(Batch) * ((size_t)1 << 29) / BATCH + sizeof(Claim) * ((size_t)1 << 27) +
                 (size_t)nworkers * (((size_t)1 << 34) + ((size_t)1 << 36));
    while ((all >> shift) > memory / 4) shift++;
#endif
    store.cap = ((size_t)1 << 37) >> shift;
    store.s = shared(store.cap);
    capstates = (1 << 29) >> shift;
    states = shared(sizeof(StateRec) * (size_t)capstates);
    fp_region_size = ((size_t)1 << 36) >> shift;
    fp_region = shared(fp_region_size);
    control = shared(sizeof(Control));
    batches = shared(sizeof(Batch) * (size_t)(capstates / BATCH + 1));
    max_claims = ((size_t)1 << 27) >> shift;
    claims = shared(sizeof(Claim) * max_claims);
    results_size = ((size_t)1 << 34) >> shift;
    encodings_size = ((size_t)1 << 36) >> shift;
    results = xmalloc(sizeof(char *) * (size_t)nworkers);
    encodings = xmalloc(sizeof(char *) * (size_t)nworkers);
    for (int i = 0; i < nworkers; i++) {
        results[i] = shared(results_size);
        encodings[i] = shared(encodings_size);
    }
}

/* The claim of the state fp, made if `make` and there is none; NULL if
   there is none, or no room for it. */
static Claim *claim(uint64_t fp, int make, int *made) {
    uint64_t key = fp ? fp : 1;   /* 0 marks a free entry */
    size_t mask = control->nclaims - 1;
    for (size_t j = key & mask;; j = (j + 1) & mask) {
        uint64_t k = atomic_load(&claims[j].key);
        if (k == key) return &claims[j];
        if (k) continue;
        if (!make) return NULL;
        if (!w_budget) {
            /* Room for claims is taken a chunk at a time: the count is shared. */
            if (atomic_fetch_add(&control->claimed, CLAIM_CHUNK) + CLAIM_CHUNK > control->nclaims / 2) return NULL;
            w_budget = CLAIM_CHUNK;
        }
        w_budget--;
        if (atomic_compare_exchange_strong(&claims[j].key, &k, key)) { *made = 1; return &claims[j]; }
        if (k == key) return &claims[j];
    }
}

/* Checks the invariants of the successor a worker claimed and keeps its encoding. */
static void settle(Claim *c) {
    EvalState s = eval_save();
    sigjmp_buf here;
    handler = &here;
    volatile int ok = 0;
    if (!sigsetjmp(here, 0) && check_list(invariants, ninvariants, succ) < 0 &&
        (!gen_init || check_list(implied_inits, nimplied_inits, succ) < 0)) {
        w_bytes.n = 0;
        for (int i = 0; i < nvars; i++) encode(&w_bytes, succ[i]);
        ok = w_encoded + w_bytes.n <= encodings_size;   /* else the search keeps it */
    }
    eval_restore(s);
    if (ok) {
        memcpy(encodings[w_id] + w_encoded, w_bytes.s, w_bytes.n);
        c->loc = (uint64_t)w_id << 40 | w_encoded;
        c->len = (int)w_bytes.n;
        w_encoded += w_bytes.n;
    }
    atomic_store(&c->state, ok ? SETTLED : FAILED);
}

static long w_slice;     /* slicing Init: the slice whose states are being written */
static size_t w_head;    /* where its header goes */

static void slice_write(void) {
    if (!w_clean) { w_n = w_head + 2 * sizeof(int); w_found = 0; }
    int header[2] = {w_clean, w_found};
    memcpy(results[w_id] + w_head, header, sizeof header);
}

static void slice_next(void) {
    w_slice++;
    w_head = w_n;
    w_n += 2 * sizeof(int);
    w_found = 0;
}

/* The initial states, or the successors of a state, a worker finds. */
static int worker_emit(void) {
    if (gen_init) {
        if (!slice_owned()) return 0;
        while (w_slice < slice_seq) { slice_write(); slice_next(); }
    }
    succ_count++;
    for (int i = 0; i < nvars; i++) if (!succ[i]) { w_clean = 0; return 1; }
    Found f = {0, cur_action, CONSTRAINED, 0};
    if (check_list(constraints, nconstraints, succ) < 0 &&
        (gen_init || check_actions(action_constraints, naction_constraints, cur_state, succ) < 0)) {
        f.fp = fingerprint(succ);
        if (!gen_init && check_actions(action_props, naction_props, cur_state, succ) >= 0) { w_clean = 0; return 1; }
        f.seen = fp_find(f.fp);
        if (f.seen == NEW) {
            int made = 0;
            Claim *c = claim(f.fp, 1, &made);
            if (!c) { atomic_store(&control->starved, 1); w_clean = 0; return 1; }
            if (made) settle(c);
            f.claim = (uint32_t)(c - claims);
        }
    } else if (check_list(invariants, ninvariants, succ) >= 0 ||
               (gen_init ? check_list(implied_inits, nimplied_inits, succ) : check_actions(action_props, naction_props, cur_state, succ)) >= 0) {
        w_clean = 0;   /* outside the model: the search reports it */
        return 1;
    }
    if (w_n + sizeof f > results_room()) { w_clean = 0; return 1; }   /* the search expands it */
    memcpy(results[w_id] + w_n, &f, sizeof f);
    w_n += sizeof f;
    w_found++;
    return 0;
}

static void worker_expand(int idx) {
    size_t head = w_n;
    w_n += 2 * sizeof(int);
    w_clean = 1;
    w_found = 0;
    EvalState saved = eval_save();
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        w_clean = 0;
    } else {
        cur_level = states[idx].depth;
        cur_state = decode_state(idx);
        draw_restart(cur_state);
        succ_count = 0;
        for (int a = 0; a < nactions && w_clean; a++) {
            cur_action = a;
            memset(succ, 0, sizeof(Value *) * (size_t)nvars);
            next_state = succ;
            gen_target = succ;
            gen(actions[a].e, actions[a].c, NULL);
        }
        if (succ_count == 0 && check_deadlock) w_clean = 0;
    }
    eval_restore(saved);
    if (!w_clean) { w_n = head + 2 * sizeof(int); w_found = 0; }
    int header[2] = {w_clean, w_found};
    memcpy(results[w_id] + head, header, sizeof header);
    arena_reset(&scratch_arena);
}

static void worker_atoms(int lo, int hi);
static void worker_groups(int lo, int hi);
static void worker_offers(int lo, int hi);
static void worker_steps(int lo, int hi);
static void worker_pems(int lo, int hi);

/* Init's slices [lo, hi): a header for each, then its states. */
static void worker_init(int lo, int hi) {
    w_slice = lo - 1;
    slice_next();
    w_clean = 1;
    EvalState saved = eval_save();
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        w_clean = 0;
    } else {
        memset(succ, 0, sizeof(Value *) * (size_t)nvars);
        gen_target = cur_state = succ;
        next_state = NULL;
        gen_init = 1;
        cur_action = -1;
        slicing = 1, slice_counting = 0, slice_seq = -1, choice_depth = 0;
        slice_lo = lo, slice_hi = hi;
        gen(init_expr, root_ctx, NULL);
    }
    eval_restore(saved);
    slicing = 0;
    int clean = w_clean;
    slice_write();
    while (w_slice < hi - 1) { slice_next(); w_clean = clean; slice_write(); }   /* not reached if it stopped */
    arena_reset(&scratch_arena);
}

/* Expands the next batch of the level, if any is left and there is room
   for its results; else gives it back to the search. */
static int expand_batch(void) {
    int b = atomic_fetch_add(&control->next, 1);
    if (b >= control->nbatches) return 0;
    if (w_n > results_room()) {
        batches[b].worker = -1;
        atomic_store(&batches[b].done, 1);
        return 0;
    }
    batches[b].worker = w_id;
    batches[b].off = w_n;
    int lo = control->lo + b * control->per, hi = lo + control->per < control->hi ? lo + control->per : control->hi;
    if (control->job == INIT) worker_init(lo, hi);
    else if (control->job == ATOMS) worker_atoms(lo, hi);
    else if (control->job == GROUPS) worker_groups(lo, hi);
    else if (control->job == OFFERS) worker_offers(lo, hi);
    else if (control->job == STEPS) worker_steps(lo, hi);
    else if (control->job == PEMS) worker_pems(lo, hi);
    else for (int idx = lo; idx < hi; idx++) worker_expand(idx);
    atomic_store(&batches[b].done, 1);
    return 1;
}

static _Noreturn void worker_main(int id) {
    in_worker = 1;
    gen_emit = worker_emit;
    w_id = id;
    char c;
    while (read(to_worker[id][0], &c, 1) == 1) {
        fp_table = control->fp_table;
        fp_size = control->fp_size;
        gen_init = 0;   /* forked as Init was computed */
        w_n = w_encoded = w_budget = 0;
        while (expand_batch()) {}
        fflush(stdout);
        if (write(from_worker[id][1], "x", 1) != 1) _exit(1);
    }
    _exit(0);
}

static int nforked;   /* the workers running: nworkers - 1, or fewer for a level of fewer batches */

static void start_workers(int n) {
    fflush(stdout);
    to_worker = xmalloc(sizeof *to_worker * (size_t)nworkers);
    from_worker = xmalloc(sizeof *from_worker * (size_t)nworkers);
    worker_pids = xmalloc(sizeof(pid_t) * (size_t)nworkers);
    for (int i = 0; i < n; i++) {
        if (pipe(to_worker[i]) || pipe(from_worker[i])) { fputs("manyan: cannot start workers\n", stderr); exit(MANYAN_ERROR); }
        pid_t pid = fork();
        if (pid < 0) { fputs("manyan: cannot start workers\n", stderr); exit(MANYAN_ERROR); }
        if (pid == 0) {
            for (int j = 0; j < i; j++) { close(to_worker[j][1]); close(from_worker[j][0]); }
            close(to_worker[i][1]);
            close(from_worker[i][0]);
            worker_main(i);
        }
        close(to_worker[i][0]);
        close(from_worker[i][1]);
        worker_pids[i] = pid;
    }
    workers_running = 1;
    nforked = n;
    forked_strs = nstrs;
}

static void stop_workers(void) {
    if (!workers_running) return;
    for (int i = 0; i < nforked; i++) close(to_worker[i][1]);
    for (int i = 0; i < nforked; i++) waitpid(worker_pids[i], NULL, 0);
    workers_running = 0;
}

/* Whether the successors found for a state can merge: each new one was
   settled by the worker that claimed it, which may still be at it. */
static int mergeable(const Found *f, int nfound) {
    for (int k = 0; k < nfound; k++) {
        if (f[k].seen != NEW) continue;
        Claim *c = &claims[f[k].claim];
        int st;
        while ((st = atomic_load(&c->state)) == CLAIMED) sched_yield();
        if (st != SETTLED) return 0;
    }
    return 1;
}

/* The states a worker found from the state parent, or initial ones if it
   is -1, in order. */
static void merge_found(int parent, const Found *f, int nfound) {
    for (int k = 0; k < nfound; k++) {
        generated++;
        if (f[k].seen == CONSTRAINED) continue;
        int found = f[k].seen;
        Claim *c = &claims[f[k].claim];
        /* New this level: merged already, or added by the search itself. */
        if (found == NEW && (found = c->merged - 1) < 0 && (found = fp_find(f[k].fp)) < 0) {
            size_t off = store.n;
            store_add(encodings[c->loc >> 40] + (c->loc & (((uint64_t)1 << 40) - 1)), (size_t)c->len);
            int depth = parent < 0 ? 1 : states[parent].depth + 1;
            found = add_record(off, f[k].fp, parent, f[k].action, depth);
            if (depth > max_depth) max_depth = depth;
        }
        if (f[k].seen == NEW) c->merged = found + 1;
        if (ntemporal_props && parent >= 0) add_edge(parent, found, f[k].action);
    }
}

static void merge_state(int idx, const Found *f, int nfound) {
    expanding = idx;
    expanded = idx + 1;
    merge_found(idx, f, nfound);
    note_expanded(idx);
}

static int merge_level(int lo, int hi);
static int merge_init(int lo, int hi);
static int merge_atoms(void);

/* The workers take [lo, hi), states of a level or Init's slices, in
   batches of per, with room for n claims; the search merges them. */
static int run_level(int lo, int hi, int per, size_t n, int job) {
    /* Workers know the strings there were when they started; states may
       now hold newer ones. */
    int nbatches = (hi - lo + per - 1) / per;
    int want = job == EXPAND || job == INIT || nbatches >= nworkers ? nworkers - 1 : nbatches - 1;
    if (workers_running && (nstrs != forked_strs || nforked < want)) stop_workers();
    if (!workers_running) start_workers(want);
    control->lo = lo;
    control->hi = hi;
    control->job = job;
    control->per = per;
    control->nbatches = nbatches;
    control->fp_table = fp_table;
    control->fp_size = fp_size;
    memset(claims, 0, sizeof(Claim) * n);
    control->nclaims = n;
    atomic_store(&control->claimed, 0);
    atomic_store(&control->starved, 0);
    atomic_store(&control->next, 0);
    for (int b = 0; b < control->nbatches; b++) atomic_store(&batches[b].done, 0);
    fflush(stdout);
    for (int i = 0; i < nforked; i++)
        if (write(to_worker[i][1], "x", 1) != 1) { fputs("manyan: a worker stopped\n", stderr); exit(MANYAN_ERROR); }
    w_id = nworkers - 1;
    w_n = w_encoded = w_budget = 0;
    int r = job == INIT ? merge_init(lo, hi) : job == ATOMS || job == GROUPS || job == OFFERS || job == STEPS || job == PEMS ? merge_atoms() : merge_level(lo, hi);
    atomic_store(&control->next, control->nbatches);   /* after an error, the workers stop */
    char c;
    for (int i = 0; i < nforked; i++)
        if (read(from_worker[i][0], &c, 1) != 1) { fputs("manyan: a worker stopped\n", stderr); exit(MANYAN_ERROR); }
    control->job = EXPAND;
    return r;
}

static int expand_level(int lo, int hi) {
    size_t want = (size_t)(4 * (hi - lo) * (growth > 1 ? growth : 1)), n = 4096;
    while (n < want && n < max_claims) n *= 2;
    return run_level(lo, hi, BATCH, n, EXPAND);
}

/* The search expands a batch as the workers do while it waits for one. */
static int steal_batch(void) {
    int (*saved_emit)(void) = gen_emit;
    in_worker = 1;
    gen_emit = worker_emit;
    int took = expand_batch();
    gen_emit = saved_emit;
    in_worker = 0;
    return took;
}

static int merge_level(int lo, int hi) {
    for (int b = 0; b < control->nbatches; b++) {
        while (!atomic_load(&batches[b].done))
            if (!steal_batch()) sched_yield();
        /* A batch given back has no results: the search expands it. */
        const char *p = batches[b].worker < 0 ? NULL : results[batches[b].worker] + batches[b].off;
        int end = lo + (b + 1) * BATCH < hi ? lo + (b + 1) * BATCH : hi;
        for (int idx = lo + b * BATCH; idx < end; idx++) {
            if (p) {
                int header[2];
                memcpy(header, p, sizeof header);
                const Found *f = (const Found *)(p + sizeof header);
                p += sizeof header + sizeof(Found) * (size_t)header[1];
                if (header[0] && mergeable(f, header[1])) { merge_state(idx, f, header[1]); continue; }
            }
            int status = expand_state(idx);
            if (status || exit_requested) return status;
        }
    }
    return 0;
}

/* Merges Init's slices [lo, hi) in order: the first one the workers did
   not compute cleanly, or hi. */
static int merge_init(int lo, int hi) {
    int per = control->per;
    for (int b = 0; b < control->nbatches; b++) {
        while (!atomic_load(&batches[b].done))
            if (!steal_batch()) sched_yield();
        int first = lo + b * per, end = first + per < hi ? first + per : hi;
        if (batches[b].worker < 0) return first;
        const char *p = results[batches[b].worker] + batches[b].off;
        for (int s = first; s < end; s++) {
            int header[2];
            memcpy(header, p, sizeof header);
            const Found *f = (const Found *)(p + sizeof header);
            p += sizeof header + sizeof(Found) * (size_t)header[1];
            if (!header[0] || !mergeable(f, header[1])) return s;
            merge_found(-1, f, header[1]);
        }
    }
    return hi;
}

/* Waits for the workers to fill the atoms, filling some itself. */
static int merge_atoms(void) {
    for (int b = 0; b < control->nbatches; b++)
        while (!atomic_load(&batches[b].done))
            if (!steal_batch()) sched_yield();
    return 0;
}

/* Init's slices, numbered by the choices of a depth that gives the
   workers enough of them; 0 if Init is better computed by one process:
   too few, or evaluating it down to that depth fails, draws or prints. */
#define INIT_SLICES 32   /* for each worker */
static int count_shallow;
static int count_emit(void) { return ++count_shallow > 4096; }   /* a state above the depth: past a few, too shallow */

static int init_slices(void) {
    EvalState saved = eval_save();
    ErrorState er = error_save();
    sigjmp_buf here;
    handler = &here;
    volatile long total = 0;
    in_worker = 1;
    gen_emit = count_emit;
    for (slice_depth = 1; slice_depth <= 16; slice_depth++) {
        if (sigsetjmp(here, 0)) { total = 0; break; }
        memset(succ, 0, sizeof(Value *) * (size_t)nvars);
        slicing = slice_counting = 1;
        slice_deeper = choice_depth = count_shallow = 0;
        slice_seq = -1;
        if (gen(init_expr, root_ctx, NULL)) { total = 0; break; }
        total = slice_seq + 1;
        if (total >= INIT_SLICES * nworkers || !slice_deeper) break;
    }
    if (slice_depth > 16) slice_depth = 16;
    eval_restore(saved);
    error_restore(&er);
    in_worker = slicing = slice_counting = 0;
    memset(succ, 0, sizeof(Value *) * (size_t)nvars);   /* an error leaves its assignments */
    arena_reset(&scratch_arena);
    return total >= 2 * nworkers && total < (1 << 30) ? (int)total : 0;
}

static int init_slice_emit(void) { return slice_owned() ? init_emit() : 0; }

/* The search computes Init's slice s itself, as one process. */
static void init_slice(int s) {
    sigjmp_buf *outer = handler, here;
    handler = &here;
    if (sigsetjmp(here, 0)) { slicing = 0; gen_emit = init_emit; handler = outer; siglongjmp(*outer, 1); }
    memset(succ, 0, sizeof(Value *) * (size_t)nvars);
    gen_emit = init_slice_emit;
    slicing = 1, slice_counting = 0, slice_seq = -1, choice_depth = 0;
    slice_lo = s, slice_hi = s + 1;
    gen(init_expr, root_ctx, NULL);
    slicing = 0;
    gen_emit = init_emit;
    handler = outer;
}

/* Init computed by the workers, its states merged in the order one
   process finds them; 0 if left to the search. A slice they could not
   compute cleanly (an error, a violation, output, a draw) the search
   computes itself, in its turn. */
static int init_parallel(void) {
    if (nworkers < 2 || ntemporal_props) return 0;
    int total = init_slices();
    if (!total) return 0;
    int per = total / (16 * nworkers) > 1 ? total / (16 * nworkers) : 1;
    size_t n = (size_t)1 << 16 < max_claims ? (size_t)1 << 16 : max_claims;
    for (int from = 0; from < total && !violation;) {
        int stop = run_level(from, total, per, n, INIT);
        if (stop == total) break;
        if (atomic_load(&control->starved) && n < max_claims) { n = 4 * n < max_claims ? 4 * n : max_claims; from = stop; continue; }
        init_slice(stop);
        from = stop + 1;
    }
    return 1;
}

/* Whether TLC, seeking an unfingerprintable successor again among the
   state's by equality, can compare v with its copy: SUBSET S, [S -> T]
   and S \X T by their parts, another set it keeps as its definition by
   its elements, which may fail. */
static int comparable(Value *v) {
    if (v->kind == V_LAZY && !user_set(v)) switch (v->lazy) {
    case L_SUBSET: return comparable(v->u.l.a);
    case L_FCNSET: return comparable(v->u.l.a) && comparable(v->u.l.b);
    case L_TIMES: case L_RCDSET:
        for (int i = 0; i < v->n; i++) if (!comparable(v->u.l.names[v->n + i])) return 0;
        return 1;
    default: {
        EvalState es = eval_save();
        ErrorState er = error_save();
        sigjmp_buf *outer = handler, here;
        handler = &here;
        Value *volatile set = NULL;
        if (!sigsetjmp(here, 0)) set = enumerate(union_cache(v));
        handler = outer;
        eval_restore(es);
        error_restore(&er);
        if (!set) return 0;
        v = set;
    }
    }
    if (v->kind == V_SET) for (int i = 0; i < v->n; i++) if (!comparable(v->u.set.elems[i])) return 0;
    if (is_fcn(v)) for (int i = 0; i < v->n; i++) if (!comparable(v->u.fcn.vals[i])) return 0;
    return 1;
}

/* After an error, the function constructors that were being computed in
   full, innermost first, which TLC reports it cannot fingerprint (§11.3);
   else a blank line. */
/* TLC's fingerprint stack trace: its call stack replaying the error;
   without one, the values with a source, innermost first. */
static void print_unfingerprinted(Expr **fps, int n) {
    if (!n) { printf("\n"); return; }
    printf("Error: TLC was unable to fingerprint.\n\nFingerprint Stack Trace:\n");
    if (nfrozen > 0) {
        for (int i = 0, k = 0; i < nfrozen; i++) {
            if (i && frozen[i] == frozen[i - 1]) continue;
            Expr *e = frozen[i];
            printf("%d. Line %d, column %d to line %d, column %d in %s\n", k++, e->l1, e->c1, e->l2, e->c2, S(file_module(e->mod)->name));
        }
    } else {
        int m = 0;
        for (int i = 0; i < n; i++) if (!m || fps[m - 1] != fps[i]) fps[m++] = fps[i];
        for (int i = m - 1; i >= 0; i--) {
            Buf b = {0};
            loc_text(&b, fps[i]);
            printf("%d) %s\n", i, b.s);
            free(b.s);
        }
    }
    printf("\nReason:\n");
    print_error_text();
}

/* Breadth-first search (§10.4). Returns the exit status. */
static int search(void) {
    if (dump_file || npossibles) nworkers = 1;
    if (nworkers > 1) share_search();
    succ = NEWN(Value *, nvars);
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        handler = NULL;
        int status = eval_failure_status();
        int over = stackless;
        int nfp = fp_depth < 64 ? fp_depth : 64;
        Expr *fps[64];
        memcpy(fps, fp_trace, sizeof(Expr *) * (size_t)nfp);
        fp_depth = 0;
        if (expanding < 0) {
            if (!live_init_failed) print_error_message();
            if (error_state && error_module != 1 && !live_init_failed) {
                printf("While working on the initial state:\n");
                print_state(error_state);
                printf("\n");
            }
            /* After an error in a property TLC went on as it replays Init. */
            replay_error(NULL);
            if (over != 2) print_unfingerprinted(fps, nfp);
            print_counts(nstates);
            return MANYAN_FAILURE_EVAL;   /* TLC: a failed Assert too */
        }
        if (over == 2) {   /* TLC prints its Java stack */
            print_exception("java.lang.StackOverflowError", "java.lang.StackOverflowError\n\n");
            print_counts(nstates - expanded - checking_invariant());
            return checking_invariant() ? MANYAN_ERROR : MANYAN_FAILURE_EVAL;
        }
        int outside = fingerprinting;
        fingerprinting = 0;
        if (outside || checking(constraints, nconstraints) || checking(action_constraints, naction_constraints)) {
            /* TLC: an unexpected exception, with the behavior to the
               successor. A successor TLC cannot fingerprint it seeks again
               among the state's, by equality: it fails again on one it finds,
               and on one it cannot compare finds none, to its NullPointerException. */
            for (int k = 0; k <= keep_going; k++) {   /* with -continue, again as TLC replays the step */
                print_exception("java.lang.RuntimeException", error_module == 1 ? ": tlc2.tool.EvalException: " : ": ");
                print_error_text();
                if (outside) print_trace(expanding, NULL, 0);
                else print_trace(expanding, error_state, cur_action);
            }
            if (outside) {
                int again = 1;   /* found again by equality, it fails again */
                for (int i = 0; i < nvars && again && !unfingerprintable; i++) again = comparable(succ[i]);
                replay_error(decode_state(expanding));
                if (again) {
                    print_exception("java.lang.RuntimeException", ": ");
                    print_error_text();
                } else {
                    print_exception("java.lang.NullPointerException", ": ");
                    printf("Cannot read field \"state\" because \"currentStateInfo\" is null\n");
                }
            }
            if (!over) print_unfingerprinted(fps, nfp);
            print_counts(outside ? nstates - expanded : 0);
            return error_module == 1 ? MANYAN_ERROR : MANYAN_FAILURE_EVAL;
        }
        if (checking(action_props, naction_props)) {
            /* With -continue TLC reports the error again as an error of the
               step, and all of it again as it replays the step. */
            int failed = 0;
            for (int k = 0; k <= keep_going; k++) {
                printf("Error: Evaluating action property %s failed.\n", S(error_check->name));
                print_error_text();
                failed = print_trace(expanding, error_state, cur_action);
                if (keep_going) print_next_failure(expanding, error_state, cur_action, status);
            }
            print_unfingerprinted(fps, nfp);
            print_counts(nstates - expanded - violation_fresh);
            return failed ? failed : error_module == 1 ? MANYAN_ERROR : MANYAN_FAILURE_EVAL;
        }
        if (checking_invariant()) {
            /* An invariant of a new state failed to evaluate: as TLC, an
               error rebuilding the behavior replaces it. */
            printf("Error: Evaluating invariant %s failed.\n", S(error_check->name));
            print_error_text();
            int failed = print_trace(expanding, error_state, cur_action);
            if (keep_going) {   /* as an error of the step, which TLC replays and may fail */
                print_next_failure(expanding, error_state, cur_action, status);
                if (replay_error(expanding_state)) print_next_failure(expanding, NULL, 0, failed = eval_failure_status());
            }
            if (failed) printf("\n");   /* after the call stack TLC prints for it */
            print_counts(nstates - expanded - 1);
            return failed ? failed : keep_going ? MANYAN_ERROR : MANYAN_FAILURE_SAFETY_EVAL;
        }
        Value **from = decode_state(expanding);
        print_next_failure(expanding, NULL, 0, status);
        /* TLC goes on to find the state deadlocked, its error already
           reported, and rebuilds the behavior; then it replays the error.
           With -continue it reports the deadlock, which replaces the error,
           or else reports the error again as it replays it: of one it
           cannot fingerprint, only the behavior. */
        if (succ_count == 0 && check_deadlock && keep_going) {
            printf("Error: Deadlock reached.\n");
            reported_trace(expanding, NULL, 0);
            print_counts(nstates - expanded);
            return MANYAN_VIOLATION_DEADLOCK;
        }
        if (succ_count == 0 && check_deadlock) rebuild_for_posts(expanding, NULL, 0);
        ErrorState first = error_save();
        replay_error(from);
        if (keep_going) {   /* the error first found, as TLC reports it again */
            ErrorState replayed = error_save();
            error_restore(&first);
            if (nfp) print_trace(expanding, NULL, 0);
            else print_next_failure(expanding, NULL, 0, status);
            error_restore(&replayed);
        } else free(first.msg.s);
        print_unfingerprinted(fps, nfp);
        print_counts(nstates - expanded);
        if (status == MANYAN_FAILURE_EVAL && error_module == 1) status = MANYAN_ERROR;
        return status;
    }
    gen_target = succ;
    next_state = NULL;
    cur_state = succ;
    gen_init = 1;
    gen_emit = init_emit;
    if (ntemporal_props) live_init_lits();
    arena = &scratch_arena;
    init_draws = draw_model;
    draw_restart(NULL);
    if (!init_parallel()) gen(init_expr, root_ctx, NULL);
    arena_reset(&scratch_arena);
    if (live_init_failed) {   /* TLC stops */
        if (violation) printf("\n");
        print_counts(nstates);
        return live_init_failed;
    }
    if (violation) {
        check_posts(1);
        return violation;
    }
    if (generated == nstates)
        printf("Finished computing initial states: %d distinct state%s generated.\n", nstates, nstates == 1 ? "" : "s");
    else
        printf("Finished computing initial states: %ld state%s generated, with %d of them distinct.\n", generated, generated == 1 ? "" : "s", nstates);
    fflush(stdout);
    if (!next_expr) {
        printf("Error: No next state actions defined to generate successor states from.\n");
        return MANYAN_FAILURE_EVAL;
    }
    gen_init = 0;
    gen_emit = next_emit;
    for (int lo = 0; lo < nstates;) {
        int hi = nstates, status = 0;
        if (nworkers > 1 && hi - lo >= PARALLEL_LEVEL) status = expand_level(lo, hi);
        else for (int idx = lo; idx < hi && !status && !exit_requested; idx++) status = expand_state(idx);
        if (status) return status;
        if (exit_requested) break;
        growth = (double)(nstates - hi) / (hi - lo);
        lo = hi;
    }
    expanding = -1;
    if (ntemporal_props) {
        arena = &perm_arena;
        collect_fairnesses();
        sigjmp_buf live;
        handler = &live;
        if (sigsetjmp(live, 0)) return live_error();
        int violated = live_violated();
        if (violated) {
            check_posts(1);
            if (violated == MANYAN_VIOLATION_SAFETY && keep_going) {
                /* TLC stops its temporal checks with an exception, which it
                   reports with -continue. */
                print_exception("tlc2.tool.INextStateFunctor$InvariantViolatedException", ": Invariant violated\n");
                print_trace(live_cut, NULL, 0);
                violated = MANYAN_ERROR;
            }
            if (violated != MANYAN_VIOLATION_LIVENESS) print_counts_after(live_cut);
            else print_counts(exit_requested ? nstates - expanded : 0);
            return violated;
        }
        handler = &here;
    }
    handler = NULL;
    int post = check_posts(0);
    if (post) {
        print_counts(exit_requested ? nstates - expanded : 0);
        return post;
    }
    printf("Model checking completed. No error has been found.\n");
    print_counts(exit_requested ? nstates - expanded : 0);
    return MANYAN_OK;
}

/* ---------------------------------------------------------------- simulation */

/* States in order, complete or not. A simulation keeps them as values, as
   TLC does: it fingerprints only what it must (a liveness check, a trace),
   so a state may hold a function TLC cannot fingerprint. */
/* States, each with the action it was reached by, -1 for an initial one. */
typedef struct { Value ***a; int *act, n, cap; } States;
static States sim_found;
static int sim_kept(void) { return sim_found.n > 0; }

static void sim_push(States *s, Value **st, int act) {
    if (s->n == s->cap) {
        s->cap = s->cap ? 2 * s->cap : 64;
        s->a = xrealloc(s->a, sizeof(Value **) * (size_t)s->cap);
        s->act = xrealloc(s->act, sizeof(int) * (size_t)s->cap);
    }
    s->a[s->n] = st;
    s->act[s->n++] = act;
}

/* The behavior being generated, and TLC's running mean and M2 of the
   behaviors' lengths, packed as TLC packs them: M2 high, mean low. */
static States sim_trace;
static Value **sim_checked;   /* the successor being checked */
static uint64_t sim_levels;

static void sim_level(long len) {
    int64_t mean = (int32_t)(sim_levels & 0xffffffff), m2 = (int64_t)(sim_levels >> 32);
    int64_t delta = len - mean;
    mean = (int32_t)(mean + delta / (sim_traces > 1 ? sim_traces : 1));
    m2 += delta * (len - mean);
    sim_levels = ((uint64_t)m2 << 32) | ((uint64_t)mean & 0xffffffff);
}

static Value *location_record(Expr *l) {
    const char *names[] = {"beginLine", "beginColumn", "endLine", "endColumn", "module"};
    Value *vals[] = {mk_int(l ? l->l1 : 0), mk_int(l ? l->c1 : 0), mk_int(l ? l->l2 : 0), mk_int(l ? l->c2 : 0),
                     mk_str(intern(l ? S(l->mod->name) : "--TLA+ BUILTINS--"))};
    return mk_record(5, names, vals);
}

/* TLCGet("action"): the action into st, as a simulation keeps it in
   each state, Init's -1 for an initial one; TLC's UnnamedAction for a
   state without one, as each of a search. */
/* Action act as TLC's record of it: its name and location, and the values
   of the parameters that label it; -1 the initial predicate, -2 none. */
static Value *action_value(int act) {
    const char *names[] = {"name", "location", "context", "parameters"};
    if (act < -1) {
        Value *vals[] = {mk_str(intern("UnnamedAction")), location_record(NULL)};
        return mk_record(2, names, vals);
    }
    Action *a = act < 0 ? NULL : &actions[act];
    Value *vals[] = {mk_str(a ? a->name : init_name ? init_name : intern("Initial predicate")),
                     location_record(a ? a->loc : init_where), NULL, NULL};
    List keys = {0}, args = {0};
    for (int i = 0; a && a->op && i < a->op->nparams; i++)
        if (!a->op->params[i]->arity) {
            list_add(&keys, mk_str(a->op->params[i]->name));
            list_add(&args, force(env_find(a->c.env, a->op->params[i])));
        }
    if (!keys.n) return mk_record(2, names, vals);
    Value *params = mk_tuple(keys.n);
    memcpy(params->u.fcn.vals, keys.v, sizeof(Value *) * (size_t)keys.n);
    vals[2] = mk_fcn_from(&keys, &args);
    vals[2]->made = MADE_RECORD;
    vals[3] = params;
    return mk_record(4, names, vals);
}

static Value *action_record(Value **st) {
    int act = -2;
    for (int i = sim_trace.n - 1; i >= 0 && act == -2 && simulating; i--) if (sim_trace.a[i] == st) act = sim_trace.act[i];
    if (act == -2 && simulating && st == sim_checked) act = cur_action;
    return action_value(act);
}

/* A state as Trace gives it: a record of its variables, and in a
   simulation of the action into it, _action, as TLCGet("action"). */
static Value *state_record(Value **st) {
    List keys = {0}, vals = {0};
    for (int i = 0; i < nvars; i++) list_add(&keys, mk_str(vars[i]->name)), list_add(&vals, st[i]);
    if (simulating) list_add(&keys, mk_str(intern("_action"))), list_add(&vals, action_record(st));
    Value *r = mk_fcn_from(&keys, &vals);
    r->made = MADE_RECORD;
    r->range = 1;
    return r;
}

/* TLCExt's Trace: the behavior from an initial state to the one being
   evaluated, the state whose successors are generated or the one being
   checked; a simulation's, as it goes. As TLC, the states between the
   first and the last are rebuilt from the ones before, which evaluates
   Next again; there Trace is the behavior rebuilt so far. */
static Value *trace_value(void) {
    if (in_worker) worker_cannot();
    List l = {0};
    if (trace_path) {
        for (int i = 0; i < ntrace_path; i++) list_add(&l, (Value *)trace_path[i]);
    } else if (simulating) {
        for (int i = 0; i < sim_trace.n; i++) list_add(&l, (Value *)sim_trace.a[i]);
        if (cur_state && (!l.n || l.v[l.n - 1] != (Value *)cur_state)) list_add(&l, (Value *)cur_state);
    } else {
        for (int i = expanding; i >= 0; i = states[i].parent) list_add(&l, (Value *)decode_state(i));
        for (int i = 0, j = l.n - 1; i < j; i++, j--) { Value *t = l.v[i]; l.v[i] = l.v[j]; l.v[j] = t; }
        if (cur_state && (expanding < 0 || cur_state != expanding_state)) list_add(&l, (Value *)cur_state);
        Value ***st = (Value ***)l.v;
        trace_path = st;
        for (int i = 1; i + 1 < l.n; i++) { ntrace_path = i; replay(st[i - 1], st[i], i); st[i] = replay_match; }
        trace_path = NULL;
    }
    Value *t = mk_tuple(l.n);
    for (int i = 0; i < l.n; i++) t->u.fcn.vals[i] = state_record((Value **)l.v[i]);
    return t;
}

/* TLCGet("stats") of a simulation; the behavior's actions are those into
   the state being evaluated, the successor being checked too. */
static Value *sim_stats(void) {
    List names = {0}, counts = {0};
    int n = sim_trace.n;
    for (int i = 1; i <= n; i++) {
        int act = i < n ? sim_trace.act[i] : cur_state == sim_checked ? cur_action : -1;
        if (act < 0) continue;
        Value *name = mk_str(actions[act].name);
        int j = 0;
        while (j < names.n && names.v[j] != name) j++;
        if (j == names.n) list_add(&names, name), list_add(&counts, mk_int(0));
        counts.v[j] = mk_int(counts.v[j]->u.i + 1);
    }
    Value *acts = mk_fcn_from(&names, &counts);
    acts->made = MADE_RECORD;
    const char *bnames[] = {"actions", "id"};
    Value *bvals[] = {acts, mk_int(sim_traces)};
    const char *snames[] = {"actions", "behavior", "worker", "traces", "duration", "generated", "distinct",
                            "retries", "distinctvalues", "levelmean", "levelvariance"};
    Value *svals[] = {mk_record(0, NULL, NULL), mk_record(2, bnames, bvals), mk_int(0), mk_int(sim_traces),
                      mk_int(time(NULL) - started), mk_int(generated), mk_int(-1), mk_int(-1), mk_int(-1),
                      mk_int((int64_t)(sim_levels & 0xffffffff)),
                      mk_int(llround((double)(sim_levels >> 32) / (sim_traces + 1.0)))};
    return mk_record(11, snames, svals);
}

/* Whether two states are equal, as TLC compares them: variable by variable. */
static int same_state(Value **s, Value **t) {
    for (int i = 0; i < nvars; i++)
        if (s[i] && t[i] ? !veq(s[i], t[i]) : s[i] != t[i]) return 0;
    return 1;
}

/* The behavior so far, then `last` reached by act if it is not NULL, as
   TLC's worker gives it: a state equal to the one before it left out,
   compared from the end. */
static States *sim_behavior(States *trace, Value **last, int act) {
    static States all, b;
    all.n = b.n = 0;
    for (int i = 0; i < trace->n; i++) sim_push(&all, trace->a[i], trace->act[i]);
    if (last) sim_push(&all, last, act);
    char *keep = NEWN(char, all.n);
    for (int i = all.n - 1; i >= 0; i--) keep[i] = !i || !same_state(all.a[i], all.a[i - 1]);
    for (int i = 0; i < all.n; i++) if (keep[i]) sim_push(&b, all.a[i], all.act[i]);
    return &b;
}

static void materialize(Value *v);

/* A state found, normalized as TLC normalizes a state's values. */
static Value **sim_state(void) {
    Value **st = snapshot(gen_target);
    for (int i = 0; i < nvars; i++)
        if (st[i]) materialize(st[i]);
    return st;
}

static int sim_emit(void) {
    sim_push(&sim_found, sim_state(), -1);
    return 0;
}

/* A successor as TLC's simulation worker takes it, checking it as it is
   generated: complete, then the invariants and action properties, then
   kept if in the model. A failed check stops the generation. */
static int sim_failed;        /* its failed check: 1 incomplete, 2 an invariant, 3 an action property */
static int sim_bad;           /* the invariant or action property */
static Defer *sim_defers;     /* each successor kept's TLCDefer */
static int sim_defers_cap;

static int sim_succ_emit(void) {
    generated++;
    Value **s1 = sim_checked = sim_state();
    for (int v = 0; v < nvars; v++)
        if (!s1[v]) return sim_failed = 1;
    if ((sim_bad = check_list(invariants, ninvariants, s1)) >= 0) return sim_failed = 2;
    if ((sim_bad = check_actions(action_props, naction_props, cur_state, s1)) >= 0) return sim_failed = 3;
    int kept = check_list(constraints, nconstraints, s1) < 0 && check_actions(action_constraints, naction_constraints, cur_state, s1) < 0;
    if (kept) {
        sim_push(&sim_found, s1, cur_action);
        if (sim_defers_cap < sim_found.cap) sim_defers = xrealloc(sim_defers, sizeof(Defer) * (size_t)(sim_defers_cap = sim_found.cap));
        sim_defers[sim_found.n - 1] = sim_defer;
    }
    sim_defer.e = NULL;
    return 0;
}

/* The successor picked, from st: what TLCDefer left it to evaluate. */
static void sim_deferred(Value **st, int k) {
    Defer d = sim_defers[k];
    if (!d.e) return;
    cur_state = d.st;
    next_state = d.primed ? sim_found.a[k] : NULL;
    eval(d.e, d.c);
    cur_state = st;
    next_state = NULL;
}

/* The successors of st by one action: TLC picks the first action at
   random, then steps through them by a random prime until one has, or
   a check fails. Returns how many, 0 if a check failed. */
static int sim_next(Value **st) {
    sim_found.n = 0;
    sim_failed = 0;
    int a = rng_index(nactions), p = rng_prime();
    gen_emit = sim_succ_emit;
    for (int i = 0; i < nactions; i++) {
        cur_state = st;
        cur_action = a;
        sim_defer.e = NULL;   /* each action's working state is new */
        memset(succ, 0, sizeof(Value *) * (size_t)nvars);
        next_state = succ;
        gen_target = succ;
        gen(actions[a].e, actions[a].c, NULL);
        if (sim_failed) return 0;
        if (sim_found.n) return sim_found.n;
        a = (a + p) % nactions;
    }
    return 0;
}

/* A random behavior up to its error, as TLC prints it: each state labeled
   by the action it was reached by. */
static int sim_printing;
static void sim_print(States *trace) {
    sim_printing = 1;
    printf("Error: The behavior up to this point is:\n");
    trace_path = trace->a;   /* Trace in the ALIAS: the behavior to the state printed */
    for (int i = 0; i < trace->n; i++) {
        ntrace_path = i + 1;
        print_numbered(i + 1, trace->act[i], trace->a[i], i ? trace->a[i - 1] : NULL, trace->a[i + (i + 1 < trace->n)]);
    }
    trace_path = NULL;
    sim_printing = 0;
}

/* An error TLC catches as an exception: one raised outside its evaluator,
   and in a simulated behavior (in_behavior) a TLCRuntimeException, is
   reported plainly, any other as unexpected. */
static void report_exception(int in_behavior) {
    if (stackless || (in_behavior && error_module == 2)) {
        printf("Error: ");
        print_error_text();
        return;
    }
    print_exception(error_java ? error_java : eval_exception() ? "tlc2.tool.EvalException" : "java.lang.RuntimeException", ": ");
    print_error_text();
}

/* A simulated behavior: its states and the actions into them. */
static int *sim_order, *sim_acts, sim_n;

static void live_eval(void);

/* Whether a temporal property fails on the behavior, as TLC checks one:
   without its finite stuttering, each state may stutter or take its
   step. */
static int sim_violates(States *trace) {
    for (int i = 0; i < nstates; i++) free(states[i].edges);
    nstates = 0;
    store.n = 0;
    if (fp_size) memset(fp_table, 0, sizeof(FpSlot) * (size_t)fp_size);
    int prev = -1;
    sim_order = xrealloc(sim_order, sizeof(int) * (size_t)(trace->n + 1));
    sim_acts = xrealloc(sim_acts, sizeof(int) * (size_t)(trace->n + 1));
    sim_n = 0;
    for (int i = 0; i < trace->n; i++) {
        Value **st = trace->a[i];
        uint64_t fp = fingerprint(st);
        int s = fp_find(fp);
        if (s >= 0 && s == prev) continue;
        if (s < 0) s = add_state(st, fp, prev, -1, sim_n + 1);
        sim_acts[sim_n] = prev < 0 ? STUTTER : trace->act[i];
        if (prev >= 0) add_edge(prev, s, sim_acts[sim_n]);
        sim_order[sim_n++] = s;
        prev = s;
    }
    sigjmp_buf here, *outer = handler;
    handler = &here;
    if (sigsetjmp(here, 0)) {   /* the error TLC meets first */
        handler = outer;
        ErrorState first = error_save();
        live_eval();
        error_restore(&first);
        raise_error();
    }
    int violated = live_violated();
    handler = outer;
    sim_n = 0;
    return violated;
}

static void sim_summary(int64_t seed, int64_t aril) {
    printf("The number of states generated: %ld\n", generated);
    printf("Simulation using seed %lld and aril %lld\n", (long long)seed, (long long)aril);
}

/* Behavior t, ended without an error, as TLC writes it for -simulate
   file=FILE: a module FILE_0_t (worker 0) that defines each state. */
static void sim_write(const char *file, long t, States *trace) {
    Buf name = {0};
    buf_printf(&name, "%s_0_%ld", file, t);
    FILE *f = fopen(name.s, "w");
    if (!f) fail("Cannot write the behavior to %s.", name.s);
    fprintf(f, "---------------- MODULE %s -----------------\n", name.s);
    for (int i = 0; i < trace->n; i++) {
        Buf b = {0};
        action_text(&b, trace->act[i], "Action");
        fprintf(f, "\\* %s\nSTATE_%d == \n", b.s, i + 1);
        free(b.s);
        fprint_state(f, trace->a[i]);
        fprintf(f, "\n\n");
    }
    fprintf(f, "=================================================\n");
    fclose(f);
    free(name.s);
}

/* Random simulation (§10.8): TLC's behaviors for the seed, from one worker.
   The initial states are kept for good; a behavior, with all it
   evaluates, until it ends. */
static int simulate(const ManyanOptions *o) {
    int64_t seed = draw_seed;
    rng_seed(seed);
    for (int64_t i = 0; i < o->aril; i++) rng_index(1);
    int64_t aril = rng_aril;
    rng_seed(jr_long(&rng));
    long depth = sim_depth < 0 ? INT32_MAX : sim_depth;   /* -1, TLC's Integer.MAX_VALUE */
    nimplied_inits = 0;   /* TLC's simulator ignores the properties that are state predicates */
    succ = NEWN(Value *, nvars);
    sigjmp_buf here;
    handler = &here;
    static States init;   /* static: read after an error jumps back */
    States *const trace = &sim_trace;
    static EvalState fresh;
    fresh = eval_save();
    if (sigsetjmp(here, 0)) {
        Arena *in_use = arena;
        eval_restore(fresh);     /* the error may have left an evaluation, primed */
        arena = in_use;
        handler = NULL;
        int invariant = checking_invariant();
        if (!trace->n && (invariant || checking(constraints, nconstraints))) {
            printf("Error: ");
            print_error_text();
            printf("While working on the initial state:\n");
            print_state(error_state);
            printf("\n");
            sim_summary(seed, aril);
            return MANYAN_ERROR;
        }
        if (invariant || checking(action_props, naction_props)) {
            printf("Error: Evaluating %s %s failed.\n", invariant ? "invariant" : "action property", S(error_check->name));
            print_error_text();
            sim_print(sim_behavior(trace, sim_checked, cur_action));
            sim_summary(seed, aril);
            return invariant ? MANYAN_FAILURE_SAFETY_EVAL : MANYAN_VIOLATION_LIVENESS;
        }
        report_exception(trace->n > 0);
        int status = trace->n && error_module == 2 ? error_status : MANYAN_ERROR;
        if (trace->n && !sim_printing) {
            error_check = NULL;
            sim_print(sim_behavior(trace, NULL, 0));
        }
        return status;
    }
    static Arena init_arena;     /* the initial states, kept for good */
    arena = &init_arena;
    gen_target = cur_state = NEWN(Value *, nvars);
    next_state = NULL;
    gen_init = 1;
    gen_emit = sim_emit;
    gen(init_expr, root_ctx, NULL);
    gen_init = 0;
    init = sim_found;
    sim_found = (States){0};
    generated = init.n;
    printf("Computed %d initial states...\n", init.n);
    int in_model = 0;   /* as TLC, the behaviors start in the model: those kept first */
    for (int i = 0; i < init.n; i++) {
        Value **st = init.a[i];
        for (int v = 0; v < nvars; v++)
            if (!st[v]) {
                printf("Error: State is not completely specified by the initial predicate:\n");
                print_state(st);
                return MANYAN_ERROR;
            }
        sim_checked = st, cur_action = -1;   /* reached by Init */
        arena = &scratch_arena;   /* what checking makes, as the search's: records keep their order as written */
        Region *r = region_open();
        int violated = check_initial(st);
        region_close(r);
        arena = &init_arena;
        if (violated && check_posts(1)) {   /* TLC's error, as one in an invariant */
            printf("While working on the initial state:\n");
            print_state(st);
            printf("\n");
            return MANYAN_ERROR;
        }
        if (violated) return violated;
        if (check_list(constraints, nconstraints, st) < 0) init.a[in_model++] = st;
    }
    if (!init.n) {
        printf("Error: There is no state satisfying the initial state predicate.\n");
        return MANYAN_ERROR;
    }
    if (!in_model) {
        printf("Error: There is no state satisfying the initial state predicate and the state-constraint(s).\n");
        return MANYAN_ERROR;
    }
    init.n = in_model;
    printf("Finished computing initial states: %d distinct state generated.\n", init.n);
    arena = &perm_arena;
    collect_fairnesses();
    arena = &scratch_arena;
    drawing = &draw_behaviors;   /* TLC's worker thread */
    for (long t = 0; !o->traces || t < o->traces; t++) {
        arena_reset(&scratch_arena);
        trace->n = 0;
        sim_traces = t + 1;
        Value **st = init.a[rng_index(init.n)];
        tlc_cache_behavior(st);
        sim_push(trace, st, -1);
        int ended = 0;
        for (long d = 0; d < depth && !ended && !exit_requested; d++) {
            cur_level = d + 1;
            if (!sim_next(st)) {
                int status = 0;
                if (sim_failed == 1) {
                    States *b = sim_behavior(trace, sim_checked, cur_action);
                    print_unspecified(sim_checked);
                    sim_print(b);
                    /* TLC's postcondition writing the behavior for its trace spec fails on it */
                    if (!te_spec && !nposts) return MANYAN_FAILURE_EVAL;
                    printf("\nError: Evaluating postcondition _TLCTraceSilent at line 28, col 5 to line 28, col 21 of module _TLCTrace failed.\n"
                           "Attempted to apply the operator overridden by the Java method\n"
                           "public static final tlc2.value.IValue tlc2.module._TLCTrace.ioSerialize(tlc2.value.IValue,tlc2.value.impl.StringValue) throws java.io.IOException,\n"
                           "but it produced the following error:\n"
                           "Cannot invoke \"tlc2.value.impl.Value.fingerPrint(long)\" because \"this.values[i]\" is null\n");
                    return MANYAN_FAILURE_EVAL;
                }
                States *b = sim_behavior(trace, sim_failed ? sim_checked : NULL, cur_action);
                if (sim_failed) {
                    Check *list = sim_failed == 2 ? invariants : action_props;
                    printf("Error: %s %s is violated.\n", sim_failed == 2 ? "Invariant" : "Action property", S(list[sim_bad].name));
                    status = sim_failed == 2 ? MANYAN_VIOLATION_SAFETY : MANYAN_VIOLATION_LIVENESS;
                } else if (check_deadlock) {
                    printf("Error: Deadlock reached.\n");
                    status = MANYAN_VIOLATION_DEADLOCK;
                } else break;
                sim_print(b);
                post_behavior(b->a, b->act, b->n, 0, 0, 1);
                sim_summary(seed, aril);
                if (!keep_going) {
                    int post = check_posts(1);
                    return post ? post : status;
                }
                ended = 1;   /* as TLC, the behavior ends; the next begins */
                break;
            }
            int k = rng_index(sim_found.n);
            sim_deferred(st, k);
            sim_push(trace, st = sim_found.a[k], sim_found.act[k]);
        }
        if (exit_requested) break;   /* TLCSet("exit"): the simulation ends after the step */
        if (ended) continue;
        if (ntemporal_props && sim_violates(sim_behavior(trace, NULL, 0))) {
            sim_summary(seed, aril);
            int post = check_posts(1);
            return post ? post : MANYAN_VIOLATION_LIVENESS;
        }
        sim_level(trace->n < depth ? trace->n : depth);
        if (o->trace_file) sim_write(o->trace_file, t, sim_behavior(trace, NULL, 0));
    }
    handler = NULL;
    int post = check_posts(0);
    printf("Progress: %ld states checked.\n", generated);
    Value *periodic = periodic_expr ? eval(periodic_expr, root_ctx) : NULL;
    if (periodic && periodic->kind == V_BOOL && !periodic->u.i) {
        Buf b = {0};
        loc_text(&b, periodic_expr->def->body);
        printf("Error: Assumption %s is false.\n", b.s);   /* TLC's stops the simulation, not its exit status */
        free(b.s);
    }
    return post;
}

/* ---------------------------------------------------------------- configuration */

/* A configuration statement (§9). */
typedef struct { const char *keyword; int name; int op; Value *value; int target, module; Value *args; } CfgItem;
/* module: of name, in <- [M]; args: of name(a, ...) = value, a tuple */

static CfgItem *cfg;
static int ncfg;

static _Noreturn void config_error(const char *fmt, ...) {
    char msg[1024];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(msg, sizeof msg, fmt, ap);
    va_end(ap);
    printf("Error: %s\n", msg);
    exit(MANYAN_ERROR_CONFIG);
}

/* line: where the lexer is; tline: the line of the token last read. */
typedef struct { const char *s; int pos, line, tline; } CfgLexer;

/* A configuration TLC cannot read. */
static _Noreturn void cfg_fail(CfgLexer *L, const char *fmt, ...) {
    printf("Error: TLC found an error in the configuration file at line %d\n", L->tline);
    va_list ap;
    va_start(ap, fmt);
    vprintf(fmt, ap);
    va_end(ap);
    printf("\n");
    exit(MANYAN_ERROR_CONFIG);
}

static void cfg_space(CfgLexer *L) {
    for (;;) {
        const char *s = L->s + L->pos;
        if (*s == ' ' || *s == '\t' || *s == '\n' || *s == '\r') { L->line += *s == '\n'; L->pos++; continue; }
        if (s[0] == '\\' && s[1] == '*') { while (L->s[L->pos] && L->s[L->pos] != '\n') L->pos++; continue; }
        if (s[0] == '(' && s[1] == '*') {
            int depth = 0;
            do {
                const char *t = L->s + L->pos;
                if (!*t) config_error("Unterminated comment in the configuration file.");
                if (t[0] == '(' && t[1] == '*') { depth++; L->pos += 2; }
                else if (t[0] == '*' && t[1] == ')') { depth--; L->pos += 2; }
                else { L->line += *t == '\n'; L->pos++; }
            } while (depth > 0);
            continue;
        }
        return;
    }
}

static const char *cfg_keywords[] = {
    "CONSTANT", "CONSTANTS", "INVARIANT", "INVARIANTS", "PROPERTY", "PROPERTIES", "CONSTRAINT",
    "CONSTRAINTS", "ACTION_CONSTRAINT", "ACTION_CONSTRAINTS", "POSTCONDITION", "POSTCONDITIONS",
    "_POSSIBLE",                                                         /* lists */
    "INIT", "NEXT", "SPECIFICATION", "SYMMETRY", "VIEW", "ALIAS", "_PERIODIC", "_RL_REWARD", "CHECK_DEADLOCK", NULL};
enum { CFG_LISTS = 13 };

/* The next token: kind 'a' name, 'n' number (cfg_num), 's' string
   (cfg_str, interned unless cfg_scanning), 'p' punctuation, 0 end. Its
   text is cfg_text. */
static const char *cfg_text;
static int cfg_len, cfg_str, cfg_scanning;
static int64_t cfg_num;

/* Java's escapes of the characters, as JavaCC prints them. */
static void java_escaped(Buf *b, const char *s, int n) {
    for (int i = 0; i < n; i++) {
        const char *esc = strchr("\b\t\n\f\r\"'\\", s[i]);
        if (s[i] && esc) buf_printf(b, "\\%c", "btnfr\"'\\"[esc - "\b\t\n\f\r\"'\\"]);
        else if ((unsigned char)s[i] < 0x20 || s[i] == 0x7f) buf_printf(b, "\\u%04x", (unsigned char)s[i]);
        else buf_add(b, s + i, 1);
    }
}

/* A string the n characters from its quote that a line end breaks:
   JavaCC's error, on the configuration as TLC reads it, a newline ended. */
static _Noreturn void cfg_string_error(CfgLexer *L, int n) {
    const char *s = L->s + L->pos, *start = s;
    while (start > L->s && start[-1] != '\n') start--;
    int col = 0;
    for (const char *p = start; p <= s + n; p++) col = *p == '\t' ? (col / 8 + 1) * 8 : col + 1;
    Buf b = {0};
    if (s[n]) {
        java_escaped(&b, s, n);
        printf("Error: TLC found an error in the configuration file:\nLexical error at line %d, column %d.  "
               "Encountered: \"\\%c\" (%d), after : \"%s\"\n", L->line, col, s[n] == '\n' ? 'n' : 'r', s[n], b.s ? b.s : "");
    } else {
        java_escaped(&b, s, n);
        java_escaped(&b, "\n", 1);
        printf("Error: TLC found an error in the configuration file:\nLexical error at line %d, column 0.  "
               "Encountered: <EOF> after : \"%s\"\n", L->line + 1, b.s);
    }
    exit(MANYAN_ERROR_CONFIG);
}

static int cfg_token(CfgLexer *L) {
    cfg_space(L);
    const char *s = L->s + L->pos;
    if (!*s) return 0;
    L->tline = L->line;
    cfg_text = s;
    if (id_char(*s)) {
        int n = 0, digits = 1;
        while (id_char(s[n])) digits &= isdigit((unsigned char)s[n++]) != 0;
        L->pos += cfg_len = n;
        if (digits) { cfg_num = strtoll(s, NULL, 10); return 'n'; }
        return 'a';
    }
    if (*s == '"') {
        int n = 1;
        Buf b = {0};
        while (s[n] != '"') {
            if (!s[n] || s[n] == '\n' || s[n] == '\r') cfg_string_error(L, n);
            if (s[n] == '\\' && s[n + 1]) n++;
            buf_add(&b, s + n, 1);
            n++;
        }
        L->pos += cfg_len = n + 1;
        cfg_str = cfg_scanning ? -1 : intern_n(b.s ? b.s : "", (int)b.n);
        free(b.s);
        return 's';
    }
    L->pos += cfg_len = s[0] == '<' && s[1] == '-' ? 2 : 1;
    return 'p';
}

static int cfg_is(int kind, const char *text) {
    return kind && (int)strlen(text) == cfg_len && memcmp(cfg_text, text, (size_t)cfg_len) == 0;
}

/* The keyword the token is, if it is one. */
static int cfg_keyword(int kind) {
    for (int i = 0; kind == 'a' && cfg_keywords[i]; i++) if (cfg_is(kind, cfg_keywords[i])) return i;
    return -1;
}

/* The token as a name, interned unless cfg_scanning: TLC takes any token
   where a name is expected, and an operator symbol is one, joined from the
   characters that continue it: `++`, `\o`. */
static int cfg_name(CfgLexer *L, int kind) {
    if (kind == 'p') {
        int n = cfg_len;
        if (*cfg_text == '\\') while (isalpha((unsigned char)cfg_text[n])) n++;
        else while (cfg_text[n] && strchr("+-*/<>=!@#$%^&|~:.", cfg_text[n])) n++;
        L->pos += n - cfg_len;
        cfg_len = n;
    }
    return cfg_scanning ? -1 : intern_n(cfg_text, cfg_len);
}

/* A value: a number, a string, TRUE, FALSE, a set {v, ...}, or a model
   value, as TLC takes any other token. TLC makes the model values before
   it reads a module, so their names are interned even when cfg_scanning,
   when no value is made (§7.5). */
static Value *cfg_value(CfgLexer *L, int kind) {
    if (!kind) cfg_fail(L, "It was expecting a value, but did not find it.");
    if (symbolic_mode && cfg_is(kind, "-") && isdigit((unsigned char)L->s[L->pos])) {   /* a negative integer */
        cfg_token(L);
        return cfg_scanning ? NULL : mk_int(-cfg_num);
    }
    if (cfg_is(kind, "{")) {
        List l = {0};
        kind = cfg_token(L);
        if (!cfg_is(kind, "}"))
            for (;;) {
                list_add(&l, cfg_value(L, kind));
                kind = cfg_token(L);
                if (cfg_is(kind, "}")) break;
                if (!cfg_is(kind, ",")) cfg_fail(L, "It was expecting }, but did not find it.");
                kind = cfg_token(L);
            }
        return cfg_scanning ? NULL : list_set(&l);
    }
    if (cfg_scanning && (kind == 'n' || kind == 's' || cfg_is(kind, "TRUE") || cfg_is(kind, "FALSE"))) return NULL;
    if (kind == 'n') return mk_int(cfg_num);
    if (kind == 's') return mk_str(cfg_str);
    if (cfg_is(kind, "TRUE")) return TRUEV;
    if (cfg_is(kind, "FALSE")) return FALSEV;
    int name = intern_n(cfg_text, cfg_len);
    return cfg_scanning ? NULL : mk_model(name);
}

static Value *tuple_of(List *l) {
    Value *t = mk_tuple(l->n);
    for (int i = 0; i < l->n; i++) t->u.fcn.vals[i] = l->v[i];
    return t;
}

static void cfg_add(const char *keyword, int name, int op, Value *v, int target, int module, Value *args) {
    if (cfg_scanning) return;
    cfg = xrealloc(cfg, sizeof(CfgItem) * (size_t)(ncfg + 1));
    cfg[ncfg++] = (CfgItem){keyword, name, op, v, target, module, args};
}

/* Reads the configuration as TLC does. TLC reads it before any module, so
   a first pass, scanning, checks it and interns the model values' names;
   the second, after the modules, makes its statements. */
static void read_config(const char *text, int scanning) {
    CfgLexer L = {text, 0, 1, 1};
    int seen[sizeof cfg_keywords / sizeof *cfg_keywords] = {0};
    cfg_scanning = scanning;
    int kind = cfg_token(&L);
    while (kind) {
        int key = cfg_keyword(kind);
        if (key < 0) cfg_fail(&L, "It was expecting a keyword, but did not find it.");
        const char *k = cfg_keywords[key];
        kind = cfg_token(&L);
        if (key < 2) {
            while (kind && cfg_keyword(kind) < 0) {
                int name = cfg_name(&L, kind), module = 0;
                kind = cfg_token(&L);
                List args = {0};
                if (cfg_is(kind, "(")) {   /* name(a, ...) = value: an operator's value at a, ... */
                    do {
                        Value *a = cfg_value(&L, cfg_token(&L));
                        list_add(&args, a ? a : TRUEV);   /* scanning makes no values */
                        kind = cfg_token(&L);
                    } while (cfg_is(kind, ","));
                    if (!cfg_is(kind, ")")) cfg_fail(&L, "It was expecting ), but did not find it.");
                    kind = cfg_token(&L);
                }
                int op = cfg_is(kind, "=") ? '=' : cfg_is(kind, "<-") && !args.n ? '<' : 0;
                if (!op) cfg_fail(&L, "It was expecting = or <-, but did not find it.");
                kind = cfg_token(&L);
                if (cfg_is(kind, "[")) {   /* name = [M] value, name <- [M] target: name of module M */
                    module = cfg_name(&L, cfg_token(&L));
                    if (!cfg_is(cfg_token(&L), "]")) cfg_fail(&L, "It was expecting ], but did not find it.");
                    kind = cfg_token(&L);
                }
                if (op == '=') cfg_add(k, name, op, cfg_value(&L, kind), 0, module, args.n ? tuple_of(&args) : NULL);
                else if (!kind) cfg_fail(&L, module ? "Expected an identifier after <-[mod]." : "Expected an identifier after <-.");
                else cfg_add(k, name, op, NULL, cfg_name(&L, kind), module, NULL);
                kind = cfg_token(&L);
            }
        } else if (key < CFG_LISTS) {
            for (; kind && cfg_keyword(kind) < 0; kind = cfg_token(&L)) cfg_add(k, cfg_name(&L, kind), 0, NULL, 0, 0, NULL);
        } else {
            if (!kind) cfg_fail(&L, "The keyword %s was not followed by an identifier.", k);
            if (seen[key]++) cfg_fail(&L, "The keyword %s appeared twice.", k);
            if (strcmp(k, "CHECK_DEADLOCK") == 0) {
                if (!cfg_is(kind, "TRUE") && !cfg_is(kind, "FALSE")) cfg_fail(&L, "It was expecting TRUE or FALSE, but did not find it.");
                cfg_add(k, 0, 0, cfg_is(kind, "TRUE") ? TRUEV : FALSEV, 0, 0, NULL);
            } else cfg_add(k, cfg_name(&L, kind), 0, NULL, 0, 0, NULL);
            kind = cfg_token(&L);
        }
    }
    cfg_scanning = 0;
}

/* ---------------------------------------------------------------- model setup */

/* d's value with the configuration's line name(args) = value added: TLC
   makes the lines of a constant one OpRcdValue. */
static Value *table_add(Def *d, CfgItem *it) {
    Value *t = d->value && d->value->kind == V_OPER ? d->value->u.op.table : NULL;
    int n = t ? t->n : 0, arity = it->args->n;
    if (t && t->u.fcn.vals[0]->n != arity + 1)
        config_error("The arity of the operator %s is inconsistent in the configuration file.", S(d->name));
    Value *line = mk_tuple(arity + 1), *lines = mk_tuple(n + 1), *op = NEW(Value);
    for (int i = 0; i < arity; i++) line->u.fcn.vals[i] = it->args->u.fcn.vals[i];
    line->u.fcn.vals[arity] = it->value;
    for (int i = 0; i < n; i++) lines->u.fcn.vals[i] = t->u.fcn.vals[i];
    lines->u.fcn.vals[n] = line;
    *op = (Value){.kind = V_OPER, .u.op = {.def = d, .table = lines}};
    return op;
}

static Sym *root_sym(int name) { return module_lookup(root, name); }

/* A call of the definition the configuration names, through the instances
   it is reached by. */
/* The definition the configuration names as what. TLC rejects one with
   parameters as a role (args 'r') or by name ('s'), or, for SYMMETRY (0),
   evaluates it. */
static Expr *config_call(int name, const char *what, int args) {
    Sym *s = root_sym(name);
    if (!s || (s->def->kind != D_OP && s->def->kind != D_FCN))
        config_error("The %s %s specified in the configuration file\nis not defined in the specification.", what, S(name));
    if (s->def->nparams && args == 'r') config_error("TLC requires %s not to take any argument, but one was given: %s", what, S(name));
    if (s->def->nparams && args == 's') config_error("TLC requires %s not to take any argument.", S(name));
    if (s->def->nparams) return s->def->body;   /* its parameters undefined there */
    Def *d = s->def;
    Expr *e = NEW(Expr);
    e->kind = K_CALL;
    e->made = 1;
    e->def = d;
    e->mod = d->mod;
    if (d->where) { e->l1 = d->where->l1; e->c1 = d->where->c1; e->l2 = d->where->l2; e->c2 = d->where->c2; }
    if (s->npath) {
        e->kind = K_INSTCALL;
        e->defs = s->path;
        e->ndefs = e->nseg = s->npath;
        e->segs = NEWN(Seg, s->npath);
    }
    return e;
}

/* The body of a definition with no parameters, or the expression. */
/* The definition a call without arguments is of. */
static Def *named_def(Expr *e) {
    if (e->kind != K_CALL || e->n) return NULL;
    Def *d = e->def->replacement ? e->def->replacement : e->def;   /* Init <- MCInit */
    return d->kind == D_OP && !d->native && !d->nparams ? d : NULL;
}

static Expr *unfold(Expr *e) {
    for (int i = 0; i < 5000 && e->kind == K_CALL && e->n == 0; i++) {   /* a cycle by substitution is left to fail */
        Def *d = e->def->replacement ? e->def->replacement : e->def;   /* Init <- MCInit */
        if (d->kind != D_OP || d->native || d->nparams) break;
        e = d->body;
    }
    return e;
}

/* part, a subexpression of the body of the instance call's definition,
   as the instance sees it. */
/* inner, a call in the module call reaches, as one call from call's
   module: through I!Refinement, its M!Spec is I!M!Spec. */
static Expr *through(Expr *call, Expr *inner) {
    if (!call) return inner;
    Expr *e = NEW(Expr);
    *e = *inner;
    e->ndefs = e->nseg = call->ndefs + inner->ndefs;
    e->defs = NEWN(Def *, e->ndefs);
    e->segs = NEWN(Seg, e->ndefs);
    for (int i = 0; i < e->ndefs; i++) {
        Expr *from = i < call->ndefs ? call : inner;
        int k = i < call->ndefs ? i : i - call->ndefs;
        e->defs[i] = from->defs[k];
        if (k < from->nseg) e->segs[i] = from->segs[k];
    }
    return e;
}

static Expr *in_instance(Expr *call, Expr *part) {
    if (!call) return part;
    Def *d = NEW(Def);
    *d = *call->def;
    d->body = part;
    d->part = 1;
    d->level = -1;
    d->cache = NULL;
    Expr *e = NEW(Expr);
    *e = *call;
    e->def = d;
    e->made = 1;   /* TLC enters the instance's substitutions, not the call */
    return e;
}

/* The value of a call of a constant definition; NULL if it is no constant
   or fails. TLC computes those but a literal's before reading the
   configuration (literal_def). */
static int level_bound(Expr *e) {
    every_argument = 1;
    int level = expr_level(e);
    every_argument = 0;
    return level;
}

static Value *constant_value(Expr *e) {
    if (level_bound(e)) return NULL;
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) { handler = NULL; error_reset(); fp_depth = 0; return NULL; }
    Value *v = eval(e, root_ctx);
    handler = NULL;
    return v;
}

/* The conjuncts of a specification or property, each as the instance it
   is in sees it: a call of an instance's definition is followed into, as
   TLC does, unless the instance has parameters (IM(y)!Spec). In a
   specification, a constant definition named is its value: TRUE, which is
   dropped, or TLC's error. */
static void conjuncts(Expr *e, Expr *call, Expr ***out, int *n, int spec) {
    Value *v;
    if (spec && !call && e->kind == K_CALL && e->n == 0 && (v = constant_value(e))) {
        if (v->kind != V_BOOL) config_error("The operator %s, which equals %s,\ncannot be used as a spec", S(e->def->name), pretty(v));
        if (!v->u.i) config_error("The spec is trivially false because %s is false.", S(e->def->name));
        return;
    }
    Def *d = named_def(e);
    if (!d || expr_level(d->body) > 1) e = unfold(e);   /* as TLC, an initial predicate kept whole */
    if (e->kind == K_AND && eval_depth < 5000) {   /* as unfold */
        eval_depth++;
        for (int i = 0; i < e->n; i++) conjuncts(e->args[i], call, out, n, spec);
        eval_depth--;
        return;
    }
    if (e->kind == K_INSTCALL && e->n == 0 && e->def->kind == D_OP && !e->def->native) {
        conjuncts(e->def->body, through(call, e), out, n, spec);
        return;
    }
    *out = xrealloc(*out, sizeof(Expr *) * (size_t)(*n + 2));
    (*out)[(*n)++] = e;
    (*out)[(*n)++] = call;
}

static Expr *conjoin(Expr **parts, int n) {
    if (n == 1) return parts[0];
    Expr *e = NEW(Expr);
    *e = *parts[0];
    e->kind = K_AND;
    e->made = 1;
    e->n = n;
    e->args = NEWN(Expr *, n);
    memcpy(e->args, parts, sizeof(Expr *) * (size_t)n);
    return e;
}

/* The variables in a subscript, as TLC collects them to warn of one
   missing: in tuples and the definitions they call, through instances;
   an operator's parameter stands for its argument, and an instance's
   variable for what it substitutes, which TLC reads as if in the root
   module: through two instances, it finds the middle one's variables. */
typedef struct Args { Def *d; Expr **args; struct Args *up; } Args;
static void subscript_vars(Expr *e, Args *a, Def **path, Seg *segs, int npath, char *in, int depth) {
    if (depth > 1000) {   /* a cycle through substitutions: TLC's stack overflows */
        printf("Error: %s\n", stack_overflow);
        exit(MANYAN_ERROR);
    }
    switch (e->kind) {
    case K_DECL:
        if (e->def->var_index >= 0 && e->def->kind == D_VAR) in[e->def->var_index] = 1;
        for (int k = npath - 1; k >= 0; k--)
            for (int j = 0; j < path[k]->nsubst; j++)
                if (path[k]->subst_decl[j] == e->def) {
                    Args b = {path[k], segs[k].args, NULL};   /* a parameter of the instance stands for its argument */
                    subscript_vars(path[k]->subst_expr[j], path[k]->nparams ? &b : NULL, NULL, NULL, 0, in, depth + 1);
                    return;
                }
        return;
    case X_TUPLE:
        for (int i = 0; i < e->n; i++) subscript_vars(e->args[i], a, path, segs, npath, in, depth + 1);
        return;
    case X_LET:
        subscript_vars(e->args[0], a, path, segs, npath, in, depth + 1);
        return;
    case K_BOUND:
        for (; a; a = a->up)
            for (int i = 0; i < a->d->nparams; i++)
                if (a->d->params[i] == e->def) { subscript_vars(a->args[i], a->up, path, segs, npath, in, depth + 1); return; }
        return;
    case K_CALL: {
        Def *d = e->def->replacement ? e->def->replacement : e->def;
        if (d->kind != D_OP || d->native || d->nparams != e->n) return;
        Args b = {d, e->args, a};
        subscript_vars(d->body, &b, path, segs, npath, in, depth + 1);
        return;
    }
    case K_INSTCALL:
        if (e->def->kind == D_OP && !e->def->native && !e->n && !npath)
            subscript_vars(e->def->body, NULL, e->defs, e->segs, e->ndefs, in, depth + 1);
        return;
    default: return;
    }
}

/* The initial predicate's name and location, as TLC labels its states in
   a simulation: a definition's, or one seen through an instance's as its
   action would be (split_action). */
static void name_init(Expr *e) {
    Def *d = named_def(e), *in = NULL;
    init_name = d ? d->name : 0;
    init_where = d ? d->body : e;
    if (e->kind == K_INSTCALL && e->def->kind == D_OP && !e->def->native) {
        init_name = instance_name(e, &in);
        init_where = in ? in->where : e->def->body;
    }
}

/* SPECIFICATION Init /\ [][Next]_v /\ fairness (§9.1). */
static Def *spec_def;   /* the SPECIFICATION, NULL for INIT and NEXT */

static void use_specification(Expr *spec) {
    spec_def = spec->def;
    Expr **parts = NULL, **init = NULL;
    int n = 0, ninit = 0, nnext = 0;
    conjuncts(spec->def->body, spec->kind == K_INSTCALL ? spec : NULL, &parts, &n, 1);
    for (int i = 0; i < n; i += 2) {
        Expr *e = parts[i], *call = parts[i + 1];
        if (expr_level(e) <= 1) {
            name_init(e);
            init = xrealloc(init, sizeof(Expr *) * (size_t)(ninit + 1));
            init[ninit++] = in_instance(call, init_where);
            Def *in = NULL;
            if (call) instance_name(call, &in);
            if (in) init_where = in->where;   /* TLC locates a part through an instance that substitutes there */
        } else if (e->kind == K_ALWAYS && unfold(e->args[0])->kind == X_SQACT) {
            if (nnext++)
                config_error("The specification contains more than one conjunct of the form [][Next]_v,\n"
                             "but TLC can handle only specifications with one next-state relation.");
            Expr *sq = unfold(e->args[0]);
            next_expr = in_instance(call, sq->args[0]);
            spec_subscript = in_instance(call, sq->args[1]);
            char *in = xcalloc((size_t)nvars + 1, 1);
            subscript_vars(spec_subscript, NULL, NULL, NULL, 0, in, 0);
            if (!nowarning) {
                for (int v = 0; v < nvars; v++)
                    if (!in[v]) {
                        char text[256];
                        snprintf(text, sizeof text, "The subscript of the next-state relation specified by the specification\n"
                                 "does not seem to contain the state variable %s", S(vars[v]->name));
                        warning(text);
                    }
            }
            free(in);
        } else if (expr_level(e) == 2) {
            config_error("TLC cannot handle this conjunct of the spec:\n%s", loc_str(e));
        } else if (e->kind == K_ALWAYS && expr_level(e->args[0]) <= 1 && e->args[0]->kind != X_NUM &&
                   e->args[0]->kind != X_STR && e->args[0]->kind != X_LET) {
            /* []S, S an operator applied with no action: SANY's OpApplNode */
            printf("Error: TLC cannot handle the temporal formula %s\n", loc_str(e->args[0]));
            exit(MANYAN_ERROR);
        } else {
            fairness = xrealloc(fairness, sizeof(Expr *) * (size_t)(nfairness + 1));
            fairness[nfairness++] = in_instance(call, e);
        }
    }
    if (ninit) init_expr = conjoin(init, ninit);
    free(parts);
    free(init);
}

/* The parts of a property, as TLC's processConfigProps finds them
   (§10.5): through definitions, conjunctions, LET, calls of a definition
   with arguments and the arguments their parameters reach, and \A x \in S
   over a constant S, a part for each x; each in the context it is
   reached in. Inside an instance, where TLC has entered its
   substitutions, only definitions and conjunctions. A part is named by
   its location if it is a conjunct or a quantifier's body, else by the
   definition called, or, as []P, by P. */
typedef struct { Expr *e, *call; Ctx c; int name; } Part;

static int collect_ctx(Ctx c, void *data) {
    List *l = data;
    Ctx *k = NEW(Ctx);
    *k = c;
    list_add(l, (Value *)k);
    return 0;
}

static void property_parts(Expr *e, Expr *call, Ctx c, int name, Part **out, int *n) {
    Buf b = {0};
    switch (eval_depth < 5000 ? e->kind : -1) {
    case K_BOUND: {   /* a parameter of a call: its argument, where it was written */
        Env *p = env_find(c.env, e->def);
        if (p && !p->e && p->v) {   /* a value bound by \A, as TLC looks it up */
            if (p->v->kind != V_BOOL) config_error("The operator %s, which equals %s,\ncannot be used as a property", S(e->def->name), pretty(p->v));
            if (!p->v->u.i) config_error("The spec is trivially false because %s is false.", S(e->def->name));
            return;
        }
        if (!p || !p->e) break;
        property_parts(p->e, call, (Ctx){p->ctx_env, p->ctx_inst}, name, out, n);
        return;
    }
    case K_CALL: {
        Def *d = e->def->replacement ? e->def->replacement : e->def;
        if (d->kind != D_OP || d->native || d->nparams != e->n || (e->n && (call || d->recursive))) break;
        Env *env = d->local == 2 ? c.env : NULL;
        for (int i = 0; i < e->n; i++)
            env = d->params[i]->arity ? mk_binding(d->params[i], eval_operator_arg(e->args[i], c), env)
                                      : mk_thunk(d->params[i], e->args[i], c, env);
        eval_depth++;
        property_parts(d->body, call, (Ctx){env, c.inst}, e->def->name, out, n);
        eval_depth--;
        return;
    }
    case K_INSTCALL: {
        if (e->def->kind != D_OP || e->def->native || (e->n && call)) break;
        Def *in;
        property_parts(e->def->body, through(call, e), c, instance_name(e, &in), out, n);
        return;
    }
    case X_LET: {
        if (call) break;
        Env *env = c.env;
        for (int i = 0; i < e->ndefs; i++) env = mk_thunk(e->defs[i], e->defs[i]->body, c, env);
        for (Env *t = env; t != c.env; t = t->next) t->ctx_env = env;
        property_parts(e->args[0], call, (Ctx){env, c.inst}, name, out, n);
        return;
    }
    case K_AND:
        for (int i = 0; i < e->n; i++) {
            loc_text(&b, e->args[i]);
            property_parts(e->args[i], call, c, intern(b.s), out, n);
            b.n = 0;
        }
        free(b.s);
        return;
    case X_FORALL: {
        if (call || !bounds_constant(e)) break;
        List each = {0};
        EvalState es = eval_save();
        ErrorState er = error_save();
        sigjmp_buf here;
        handler = &here;
        int failed = sigsetjmp(here, 0);   /* as TLC, a set that fails is no constant: the part is whole */
        if (!failed) for_bindings(e->bounds, e->nb, c, collect_ctx, &each);
        eval_restore(es);
        error_restore(&er);
        if (failed) break;
        if (!each.n) config_error("The liveness formula is a tautology.");
        loc_text(&b, e->args[0]);
        for (int i = 0; i < each.n; i++) property_parts(e->args[0], call, *(Ctx *)each.v[i], intern(b.s), out, n);
        free(b.s);
        return;
    }
    }
    if (e->kind == K_ALWAYS && e->args[0]->kind == K_CALL && e->args[0]->n == 0) name = e->args[0]->def->name;
    *out = xrealloc(*out, sizeof(Part) * (size_t)(*n + 1));
    (*out)[(*n)++] = (Part){e, call, c, name};
}

/* A property's part that is an action, not under []. */
static void action_property(Expr *e, int name) {
    const char *n = S(name), *l = loc_str(e);
    const char *level = "is an action-level formula (i.e., it contains no temporal operators). "
                        "Only temporal-level (or state-level) formulas are allowed under PROPERTY or PROPERTIES.";
    const char *book = "Specifying Systems at https://lamport.azurewebsites.net/tla/book.html";
    if (e->kind == X_SQACT)
        config_error("The formula %s at %s %s To check that action %s holds in *every* step of the behavior, define a temporal property "
                     "by applying the \"always\" temporal operator ([]) to the formula at %s (compare page 90 of %s).", n, l, level, n, l, book);
    if (e->kind == X_ANGLEACT)
        config_error("The formula %s at %s %s To check that infinitely many %s steps occur, define a temporal property by applying "
                     "the \"always eventually\" temporal operator combination ([]<>) to the formula at %s (compare page 91 of %s).", n, l, level, n, l, book);
    config_error("The formula %s at %s %s To check that action %s holds in *every* step of the behavior, define a temporal property: "
                 "Let A be the formula at %s; rewrite A as [][A]_v, where v is a state function (typically the tuple of variables) "
                 "(compare page 90 of %s).", n, l, level, n, l, book);
}

/* A property: []P as an invariant, [][A]_v as an action property, the
   rest checked on the state graph (§10.5). */
static void use_property(Expr *p) {
    Def *d = p->def;
    Part *parts = NULL;
    int n = 0;
    property_parts(p->kind == K_INSTCALL ? d->body : p, p->kind == K_INSTCALL ? p : NULL, root_ctx, d->name, &parts, &n);
    for (int i = 0; i < n; i++) {
        Expr *e = parts[i].e, *call = parts[i].call;
        Ctx c = parts[i].c;
        int name = parts[i].name, level = level_in(in_instance(call, e), c);
        if (level <= 1) { add_check(&implied_inits, &nimplied_inits, d, in_instance(call, e), c, name); continue; }
        if (level == 2) action_property(e, name);
        if (e->kind == K_ALWAYS) {
            Expr *body = unfold(e->args[0]);
            if (level_in(in_instance(call, body), c) <= 1) { add_check(&invariants, &ninvariants, d, in_instance(call, body), c, name); continue; }
            if (body->kind == X_SQACT) { add_check(&action_props, &naction_props, d, in_instance(call, body), c, name); continue; }
        }
        add_check(&temporal_props, &ntemporal_props, d, in_instance(call, e), c, name);
    }
    free(parts);
}

static Value *def_body(Def *d) { return d->kind == D_FCN ? fcndef_value(d, (Ctx){NULL, NULL}) : eval(d->body, (Ctx){NULL, NULL}); }

/* The value of a constant definition, normalized, which TLC computes once.
   What computing it made is dropped once the value is copied out; a value
   holding its context, as a lazy function does, is computed again where it
   is kept, with the same draws, printing nothing again. After an error it
   is kept: it may be named. */
static Value *def_value(Def *d) {
    Arena *saved = arena, made = {0};
    JRandom draw = *drawing;
    int due = draw_due, loops = nregions, quiet = reprinting;
    sigjmp_buf *outer = handler, here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        handler = outer; arena = saved; nregions = loops; reprinting = quiet;
        arena_join(&perm_arena, &made);
        raise_error();
    }
    arena = &made;
    Value *v = def_body(d);
    materialize(v);
    arena = &perm_arena;
    long budget = (long)(arena_bytes(&made) / sizeof(Value));
    Value *c = copy_value(v, &budget);
    arena_free(&made);
    if (!c) {
        *drawing = draw;
        draw_due = due;
        reprinting = 1;
        materialize(c = def_body(d));
        reprinting = quiet;
    }
    handler = outer;
    arena = saved;
    return c;
}

/* Constant definition d evaluated once, any error ignored. */
static void evaluate_constant(Def *d) {
    EvalState s = eval_save();
    sigjmp_buf here;
    handler = &here;
    if (d->kind == D_FCN && !d->self && d->local != 2 && d->level == 0 && !sigsetjmp(here, 0)) {
        d->cache = def_value(d);   /* TLC keeps a function definition computed in full, if it can be */
    }
    if (d->kind == D_OP && !d->nparams && !d->native && !d->cache && def_level(d) == 0) {
        /* TLCGet's is evaluated each time, as one that fails */
        if (!level_bound(d->body) && !sigsetjmp(here, 0)) call_def(d, NULL, 0, (Ctx){NULL, NULL}, NULL);
        else d->uncached = 1;
    }
    eval_restore(s);
}

/* TLC evaluates the constant definitions of each module at startup, in
   the order SANY finishes the modules (a module after those it uses): a
   constant replaced by a definition with variables must evaluate, and every
   other constant definition without parameters is evaluated once, any
   error ignored. Side effects such as Print show then. */
static void evaluate_constants(Module *m) {
    if (m->instantiated && m->ndecls) return;
    Arena *saved = arena;
    arena = &perm_arena;
    for (int i = 0; i < m->ndecls; i++) {
        Def *c = m->decls[i];
        if (c->kind != D_CONST || !c->replacement || c->replacement->nparams) continue;
        sigjmp_buf here;
        handler = &here;
        if (sigsetjmp(here, 0)) {
            handler = NULL;
            /* A constant definition that fails is reported as the model is checked. */
            if (level_bound(c->replacement->body) == 0) continue;
            config_error("The configuration file substitutes constant %s with non-constant %s%s%s%s%s", S(c->name),
                         S(c->replacement->name), error_module == 1 ? "" : " - specifically: ",
                         error_module == 1 ? "" : error_message.s, error_expr ? "\n" : "", error_expr ? node_str(error_expr) : "");
        }
        call_def(c->replacement, NULL, 0, (Ctx){NULL, NULL}, NULL);
        handler = NULL;
    }
    for (int i = 0; i < m->nunits; i++) if (m->units[i].kind == 0) evaluate_constant(m->units[i].def);
    arena = saved;
    for (int i = 0; i < m->nnested; i++) evaluate_constants(m->nested[i]);
}

/* TLC's status for assumption u: 0 if it holds. */
static int check_assumption(Unit *u) {
    Arena *saved = arena, made = {0};   /* dropped after, as the value is a Boolean's */
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        handler = NULL;
        arena = saved;
        printf("Error: Evaluating assumption %s failed.\n%s", loc_str(u->expr), error_message.s ? error_message.s : "");
        if (error_expr && error_expr->mod) printf("\n%s", node_str(error_expr));
        printf("\n");
        arena_free(&made);
        return MANYAN_VIOLATION_ASSUMPTION;
    }
    arena = &made;
    Value *v = eval(u->expr, root_ctx);
    arena = saved;
    handler = NULL;
    int holds = v->kind == V_BOOL && v->u.i;
    arena_free(&made);
    if (!holds) {
        printf("Error: Assumption %s is false.\n", loc_str(u->expr));
        return MANYAN_VIOLATION_ASSUMPTION;
    }
    return 0;
}

static Unit **sym_assumes;   /* -cinit's: left to symbolic checking, which chooses the constants they assume of */
static int nsym_assumes;

static void check_assumptions(Module *m, int *done_status) {
    for (int i = 0; i < m->nunits; i++) {
        if (m->units[i].kind == 2 && sym_cinit_name) {
            sym_assumes = xrealloc(sym_assumes, sizeof(Unit *) * (size_t)(nsym_assumes + 1));
            sym_assumes[nsym_assumes++] = &m->units[i];
            continue;
        }
        int status = m->units[i].kind == 2 ? check_assumption(&m->units[i]) : 0;
        if (status) { *done_status = status; return; }
    }
}

/* ---------------------------------------------------------------- TLC's order of the variables */

/* TLC lists the variables of a state in the order the root module's
   context, a java.util.Hashtable, enumerates them, reversed. That order
   follows from the names the context holds and the order SANY put them
   in: its built-in operators, in reverse, then the module's symbols as
   SANY meets them. */
typedef struct { const char *name; int module; int local; Def *def; } CtxName;
typedef struct { CtxName *a; int n, cap; } CtxNames;

static const char *sany_builtins[] = {
    "STRING", "FALSE", "TRUE", "BOOLEAN", "=", "/=", ".", "'", "\\lnot", "\\neg", "\\land",
    "\\lor", "\\equiv", "=>", "SUBSET", "UNION", "DOMAIN", "\\subseteq", "\\in", "\\notin", "\\",
    "\\intersect", "\\union", "\\times", "~>", "[]", "<>", "ENABLED", "UNCHANGED", "\\cdot",
    "-+->", "$AngleAct", "$BoundedChoose", "$BoundedExists", "$BoundedForall", "$CartesianProd",
    "$Case", "$ConjList", "$DisjList", "$Except", "$FcnApply", "$FcnConstructor", "$IfThenElse",
    "$NonRecursiveFcnSpec", "$Pair", "$RcdConstructor", "$RcdSelect", "$RecursiveFcnSpec", "$Seq",
    "$SetEnumerate", "$SetOfAll", "$SetOfFcns", "$SetOfRcds", "$SF", "$SquareAct", "$SubsetOf",
    "$TemporalExists", "$TemporalForall", "$TemporalWhile", "$Tuple", "$UnboundedChoose",
    "$UnboundedExists", "$UnboundedForall", "$WF", "$Nop", "$Qed", "$Pfcase", "$Have", "$Take",
    "$Pick", "$Witness", "$Suffices", NULL
};

static void ctx_put(CtxNames *c, CtxName e) {
    for (int i = 0; i < c->n; i++) if (c->a[i].module == e.module && strcmp(c->a[i].name, e.name) == 0) return;
    if (c->n == c->cap) {
        c->cap = c->cap ? c->cap * 2 : 64;
        c->a = xrealloc(c->a, sizeof(CtxName) * (size_t)c->cap);
    }
    c->a[c->n++] = e;
}

static CtxNames context_enumeration(Module *m);

/* The symbols of m's context, in the order SANY adds them. */
static CtxNames context_names(Module *m) {
    CtxNames c = {0};
    for (int i = 0; i < m->nextends; i++) {
        CtxNames x = context_names(load_module(m->extends[i], m));
        for (int k = 0; k < x.n; k++) if (!x.a[k].local) ctx_put(&c, x.a[k]);
        free(x.a);
    }
    for (int i = 0; i < m->nunits; i++) {
        Unit *u = &m->units[i];
        Def *d = u->def;
        if (u->kind == 2) continue;
        if (u->kind == 3) { ctx_put(&c, (CtxName){S(u->module->name), 1, 0, NULL}); continue; }
        if (u->kind == 1 || d->kind == D_INST) {
            /* An instance brings its module's definitions, then its theorems
               and assumptions, as that module's context enumerates them;
               a named instance I brings Op as I!Op, and instances too. */
            CtxNames t = context_enumeration(d->target);
            for (int pass = 0; pass < 2; pass++)
                for (int k = 0; k < t.n; k++) {
                    CtxName e = t.a[k];
                    if (e.local || e.module) continue;
                    int kind = e.def->kind;
                    int op = kind == D_OP || kind == D_FCN || kind == D_RECURSIVE || (kind == D_INST && u->kind == 0);
                    if (pass == 0 ? !op : kind != D_THM) continue;
                    if (u->kind == 0) {
                        Buf name = {0};
                        buf_printf(&name, "%s!%s", S(d->name), e.name);
                        int id = intern(name.s);   /* before S reads strs, which interning moves */
                        e.name = S(id);
                        free(name.s);
                    }
                    e.local = u->local;
                    ctx_put(&c, e);
                }
            free(t.a);
            if (u->kind == 1) continue;
        }
        ctx_put(&c, (CtxName){S(d->name), 0, u->local, d});
    }
    return c;
}

static unsigned java_hash(const char *s) {
    unsigned h = 0;
    for (; *s; s++) h = 31 * h + (unsigned char)*s;
    return h & 0x7fffffff;
}

/* The symbols of m's context, in the order its Hashtable enumerates them:
   the table holds SANY's built-in operators, put in reverse, then the
   symbols. It starts with 11 buckets and grows to 2n + 1 when it is three
   quarters full, putting each bucket's entries, from the last bucket to
   the first, at the head of their new bucket. */
static CtxNames context_enumeration(Module *m) {
    CtxNames c = context_names(m);
    int nbuiltins = (int)(sizeof sany_builtins / sizeof *sany_builtins) - 1, nkeys = nbuiltins + c.n;
    unsigned *hash = xmalloc(sizeof(unsigned) * (size_t)nkeys);
    int *link = xmalloc(sizeof(int) * (size_t)nkeys);
    for (int k = 0; k < nkeys; k++) hash[k] = java_hash(k < nbuiltins ? sany_builtins[nbuiltins - 1 - k] : c.a[k - nbuiltins].name);
    int cap = 11, count = 0, *head = xmalloc(sizeof(int) * (size_t)cap);
    for (int i = 0; i < cap; i++) head[i] = -1;
    for (int k = 0; k < nkeys; k++) {
        if (count >= cap * 3 / 4) {
            int bigger = cap * 2 + 1, *heads = xmalloc(sizeof(int) * (size_t)bigger);
            for (int i = 0; i < bigger; i++) heads[i] = -1;
            for (int i = cap - 1; i >= 0; i--)
                for (int e = head[i], next; e >= 0; e = next) {
                    next = link[e];
                    link[e] = heads[hash[e] % (unsigned)bigger];
                    heads[hash[e] % (unsigned)bigger] = e;
                }
            free(head);
            cap = bigger;
            head = heads;
        }
        link[k] = head[hash[k] % (unsigned)cap];
        head[hash[k] % (unsigned)cap] = k;
        count++;
    }
    CtxNames out = {0};
    for (int i = cap - 1; i >= 0; i--)
        for (int e = head[i]; e >= 0; e = link[e])
            if (e >= nbuiltins) ctx_put(&out, c.a[e - nbuiltins]);
    free(hash);
    free(link);
    free(head);
    free(c.a);
    return out;
}

/* Puts the variables in TLC's order: its context's, reversed. */
static void order_variables(void) {
    CtxNames c = context_enumeration(root);
    Def **order = NEWN(Def *, nvars);
    int n = nvars;
    for (int i = 0; i < c.n; i++)
        if (c.a[i].def && c.a[i].def->kind == D_VAR && n > 0) order[--n] = c.a[i].def;
    if (n == 0 && nvars) memcpy(vars, order, sizeof(Def *) * (size_t)nvars);
    for (int i = 0; i < nvars; i++) vars[i]->var_index = i;
    free(c.a);
}

/* The text of e as SANY's human-readable image: its tokens, without the
   spaces between them. */
static void expr_image(Buf *b, Expr *e) {
    for (int i = 0; i < e->mod->ntoks; i++) {
        Tok *t = &e->mod->toks[i];
        if (t->line < e->l1 || (t->line == e->l1 && t->col < e->c1)) continue;
        if (t->line > e->l2 || (t->line == e->l2 && t->col > e->c2)) break;
        if (t->kind == T_STR) buf_printf(b, "\"%.*s\"", t->len, t->text);
        else buf_puts(b, S(t->id));
    }
}

/* Whether a permutation of g moves the model value m. */
static int symmetry_moves(Value *g, Value *m) {
    for (int i = 0; i < g->n; i++) {
        Value *f = realize(g->u.set.elems[i]);
        for (int j = 0; j < f->n; j++)
            if (veq(f->u.fcn.keys[j], m)) { if (!veq(f->u.fcn.vals[j], m)) return 1; break; }
    }
    return 0;
}

/* TLC's warning for the sets of SYMMETRY body, with value g, that permute
   nothing, found as TLC's Tool.getSymmetryPerms finds them: among the
   arguments of the body, all of them when there are as many as functions
   in g, else each Permutations(C) none of whose model values g moves. */
static void warn_symmetry_sets(Expr *body, Value *g) {
    Buf names = {0};
    int n = 0;
    for (int i = 0; i < body->n; i++) {
        Expr *a = body->args[i];
        if (body->n < g->n) {
            if (a->kind != K_CALL || a->n != 1 || a->def->name != intern("Permutations")) continue;
            Expr *c = a->args[0];
            if (!(c->kind == K_DECL && c->def->kind == D_CONST) && !(c->kind == K_CALL && !c->n && !def_level(c->def))) continue;
            Value *set = eval(c, root_ctx);
            if (set->kind != V_SET) continue;
            int moves = 0;
            for (int j = 0; j < set->n && !moves; j++)
                moves = set->u.set.elems[j]->kind == V_MODEL && symmetry_moves(g, set->u.set.elems[j]);
            if (moves) continue;
        }
        Buf image = {0};
        expr_image(&image, a);
        char *name = image.s ? image.s : "";
        size_t len = strlen(name);
        if (strncmp(name, "Permutations", 12) == 0 && len > 13) { name[len - 1] = 0; name += 13; }
        int id = intern(name);
        for (int j = 0; j < ncfg; j++)
            if (strncmp(cfg[j].keyword, "CONSTANT", 8) == 0 && cfg[j].op != '=' && !cfg[j].module && cfg[j].target == id) { name = (char *)S(cfg[j].name); break; }
        buf_printf(&names, "%s%s", n++ ? ", and " : "", name);
        free(image.s);
    }
    if (n) {
        Buf b = {0};
        buf_printf(&b, "The set%s %s %s been defined to be a symmetry set but contain%s less than two elements.",
                   n > 1 ? "s" : "", names.s, n > 1 ? "have" : "has", n > 1 ? "" : "s");
        warning(b.s);
        free(b.s);
    }
    free(names.s);
}

/* Whether to check the invariant or property e the configuration names.
   As TLC, a constant definition is evaluated as the configuration is read,
   unless it is a literal or fails: TRUE is dropped, another value is an
   error. */
static int literal_def(Expr *e) { return e->def->body->kind == X_NUM || e->def->body->kind == X_STR; }

static int config_check(Expr *e, const char *what) {
    if (symbolic_mode) return 1;   /* Apalache checks a constant as it does any formula */
    Value *v = literal_def(e) ? NULL : constant_value(e);
    if (!v) return 1;
    if (v->kind == V_BOOL && v->u.i) {
        if (!strcmp(what, "invariant")) {
            Buf b = {0};
            buf_printf(&b, "The invariant %s is a constant-level formula (i.e., it contains no variables, primes, or temporal operators) and evaluates to TRUE. "
                       "To assert constant-level formulas in your spec, use ASSUME ConstInv. If you optionally want to give the assumption a name, write ASSUME YourAssumption == ConstInv instead. "
                       "See https://explain.tlapl.us/assumptions-and-invariants for additional details.", S(e->def->name));
            warning(b.s);
            free(b.s);
        }
        return 0;
    }
    config_error("The %s of %s is equal to %s", what, S(e->def->name), pretty(v));
}

/* The root module's constants in the order TLC takes them: SANY keeps the
   module's symbols, with its 72 built-in operators, in a Java Hashtable,
   and TLC reverses its enumeration, so a constant comes in the order of
   its name's bucket. */
static int java_bucket(int name, int cap) {
    uint32_t h = 0;
    for (const char *p = S(name); *p; p++) h = 31 * h + (unsigned char)*p;
    return (int)((h & 0x7fffffff) % (uint32_t)cap);
}

/* The capacity of SANY's Hashtable of the root module's symbols. */
static int root_table_cap(void) {
    int cap = 11, count = 72 + root->nsyms;
    for (int k = 0; k < count; k++) if (k >= (int)(cap * 0.75)) cap = cap * 2 + 1;
    return cap;
}

/* The root module's definitions and constants e names, once each. */
static void sym_calls(Expr *e, Def ***defs, int *n) {
    if (!e) return;
    if (e->kind == K_CALL || e->kind == X_OPREF || e->kind == K_DECL) {
        Sym *s = root_sym(e->def->name);
        int i = 0;
        while (i < *n && (*defs)[i] != e->def) i++;
        if (s && s->def == e->def && i == *n) PUSH(*defs, *n, e->def);
    }
    for (int i = 0; i < e->n; i++) sym_calls(e->args[i], defs, n);
    for (int i = 0; i < e->nb; i++) sym_calls(e->bounds[i].set, defs, n);
    if (e->kind == X_LET) for (int i = 0; i < e->ndefs; i++) sym_calls(e->defs[i]->body, defs, n);
    if (e->kind == X_LAMBDA) sym_calls(e->def->body, defs, n);
}

/* Apalache's OVERRIDE_X == e, a definition for X, a constant or an
   operator the configuration gives none: as X <- OVERRIDE_X. Apalache
   refuses a cycle they make among the definitions. */
static void sym_overrides(void) {
    for (int i = 0; i < root->nsyms; i++) {
        Def *o = root->syms[i].def;
        const char *name = S(o->name);
        if (o->kind != D_OP || strncmp(name, "OVERRIDE_", 9)) continue;
        Sym *t = root_sym(intern(name + 9));
        if (t && (t->def->kind == D_CONST || t->def->kind == D_OP) && !t->def->value && !t->def->replacement) t->def->replacement = o;
    }
    for (int i = 0; i < root->nsyms; i++) {
        Def *start = root->syms[i].def;
        if (!start->replacement) continue;
        Def **reached = NULL;   /* what start reaches, as replaced */
        int n = 0;
        PUSH(reached, n, start);
        for (int k = 0; k < n; k++) {
            Def *d = reached[k]->replacement ? reached[k]->replacement : reached[k], **calls = NULL;
            int ncalls = 0;
            sym_calls(d->body, &calls, &ncalls);
            for (int j = 0; j < ncalls; j++) {
                int m = 0;
                while (m < n && reached[m] != calls[j]) m++;
                if (m < n && calls[j] != start) continue;
                if (m == n) { PUSH(reached, n, calls[j]); continue; }
                Buf b = {0};
                for (m = 0; m < n; m++) buf_printf(&b, "%s%s", m ? ", " : "", S(reached[m]->name));
                printf("Configuration error (see the manual): Found a cyclic dependency among operators: %s\n", b.s);
                exit(MANYAN_ERROR_CONFIG);
            }
        }
    }
}

static Def **tlc_constants(int *n) {
    int cap = root_table_cap();
    Def **c = NEWN(Def *, root->ndecls);
    *n = 0;
    for (int i = 0; i < root->ndecls; i++) {
        Def *d = root->decls[i];
        if (d->kind != D_CONST) continue;
        int j = (*n)++;
        while (j > 0 && java_bucket(c[j - 1]->name, cap) > java_bucket(d->name, cap)) { c[j] = c[j - 1]; j--; }
        c[j] = d;
    }
    return c;
}

/* Whether the configuration substitutes for name, in module (0: the root). */
static int substituted(int name, int module) {
    for (int i = 0; i < ncfg; i++)
        if (cfg[i].op == '<' && cfg[i].name == name && cfg[i].module == module) return 1;
    return 0;
}

/* TLC's checks of a substitution for d, configured for module (0: the root). */
static void check_substitution(Def *d, int module) {
    if (!d->replacement && !d->bad_target) return;
    int target = d->bad_target ? d->bad_target : d->replacement->name;
    if (substituted(target, module))
        config_error("In the configuration file, the identifier %s appears\non the right-hand side of a <- after already appearing on the\nleft-hand side of one.", S(target));
    if (d->bad_target)
        config_error("The configuration file substitutes for %s with the undefined identifier %s.", S(d->name), S(d->bad_target));
    if (d->kind != D_CONST && d->replacement->kind != D_CONST && d->nparams != d->replacement->nparams)
        config_error("The configuration file substitutes for %s with %s of different number of arguments.", S(d->name), S(target));
}

static void collect_names(Expr *e, Def ***defs, int *n, int *cap);

/* Whether a definition or assumption of the root module names constant
   c: Apalache asks a value only of a constant the specification uses. */
static int names_const(Def *c) {
    Def **ds = NULL;
    int n = 0, cap = 0;
    for (int i = 0; i < root->nsyms; i++) {
        Def *d = root->syms[i].def;
        collect_names(d->body, &ds, &n, &cap);
        for (int k = 0; k < d->nb; k++) collect_names(d->bounds[k].set, &ds, &n, &cap);
        if (d->kind == D_INST) for (int k = 0; k < d->nsubst; k++) collect_names(d->subst_expr[k], &ds, &n, &cap);
    }
    for (int i = 0; i < root->nunits; i++) if (root->units[i].kind == 2) collect_names(root->units[i].expr, &ds, &n, &cap);
    int found = 0;
    for (int i = 0; i < n && !found; i++) found = ds[i] == c;
    free(ds);
    return found;
}

static int setup_model(void) {
    for (int i = 0; i < root->ndecls; i++)
        if (root->decls[i]->kind == D_VAR) {
            vars = xrealloc(vars, sizeof(Def *) * (size_t)(nvars + 1));
            vars[nvars++] = root->decls[i];
        }
    order_variables();
    Expr *spec = NULL, *init = NULL, *next = NULL, *e;
    int stray = 0, module_stray = 0, no_module = 0;   /* a name substituted for, or a module, the spec does not have */
    /* TLC takes the constants, then the invariants, then the rest but the
       constraints, then the constraints, then the action constraints. */
    /* As TLC: the constants, the invariants, the specification, its
       properties, the constraints, the action constraints. */
    for (int pass = 0; pass < 7; pass++) {
    if (pass == 3) {
        if (spec && (init || next)) config_error("The configuration file cannot specify both INIT/NEXT and SPECIFICATION fields.");
        if (spec) use_specification(spec);
        if (init) {
            init_expr = init;
            name_init(init);
        }
        if (next) next_expr = next;
    }
    if (pass == 1 && symbolic_mode) sym_overrides();
    if (pass == 1) {
        int n;
        Def **c = tlc_constants(&n);
        for (int i = 0; i < n; i++)
            if (!c[i]->value && !c[i]->replacement && !c[i]->bad_target && !sym_cinit_name && (!symbolic_mode || names_const(c[i])))
                config_error("The constant parameter %s is not assigned a value by the configuration file.", S(c[i]->name));
        for (int i = 0; i < n; i++) check_substitution(c[i], 0);
        for (int i = 0; i < root->nsyms; i++) check_substitution(root->syms[i].def, 0);
        if (stray) config_error("In the configuration file, the identifier %s does not appear in the specification.", S(stray));
        for (int i = 0; i < ncfg; i++) {
            Module *m = cfg[i].module ? find_module(cfg[i].module) : NULL;
            Sym *s = m ? module_lookup(m, cfg[i].name) : NULL;
            if (s) check_substitution(s->def, cfg[i].module);
        }
        if (module_stray) config_error("In the configuration file, the identifier %s does not appear in the specification.", S(module_stray));
        if (no_module) config_error("In the configuration file, the module name %s is not a module in the specification.", S(no_module));
    }
    for (int i = 0; i < ncfg; i++) {
        CfgItem *it = &cfg[i];
        const char *k = it->keyword;
        if (pass != (strncmp(k, "CONSTANT", 8) == 0 ? 0 : strncmp(k, "INVARIANT", 9) == 0 ? 1 : strncmp(k, "PROPERT", 7) == 0 ? 3
                     : strncmp(k, "CONSTRAINT", 10) == 0 ? 4 : strncmp(k, "ACTION_CONSTRAINT", 17) == 0 ? 5
                     : strcmp(k, "_POSSIBLE") == 0 ? 6 : 2)) continue;
        if (pass == 0) {
            Module *m = it->module ? find_module(it->module) : root;
            Sym *s = m ? module_lookup(m, it->name) : NULL;
            int *missing = !m ? &no_module : it->module ? &module_stray : &stray;
            if (!s && it->op != '=' && !*missing) *missing = m ? it->name : it->module;
            if (!s) continue;
            Def *d = s->def;
            if (it->op == '=' && it->args) d->value = table_add(d, it);
            else if (it->op == '=') d->value = it->value;
            else {
                Sym *t = root_sym(it->target);
                if (t) d->replacement = t->def;
                else d->bad_target = it->target;   /* reported with the constants, as TLC */
            }
        } else if (strcmp(k, "INIT") == 0 || strcmp(k, "NEXT") == 0) {
            const char *what = k[0] == 'I' ? "initial predicate" : "next state action";
            e = config_call(it->name, what, 'r');
            if (!symbolic_mode && !literal_def(e) && constant_value(e)) config_error("The %s %s cannot be a constant.", what, S(it->name));
            *(k[0] == 'I' ? &init : &next) = e;
        } else if (strcmp(k, "SPECIFICATION") == 0) spec = config_call(it->name, "name", 's');
        else if (strncmp(k, "INVARIANT", 9) == 0) {
            Sym *t = symbolic_mode ? root_sym(it->name) : NULL;
            if (t && t->def->kind == D_OP && t->def->nparams == 1) {   /* Apalache's trace invariant, of the behavior so far */
                add_check(&invariants, &ninvariants, t->def, t->def->body, root_ctx, it->name);
                continue;
            }
            e = config_call(it->name, "invariant", 'r');
            if (expr_level(e) >= 2 + symbolic_mode) {   /* Apalache checks an action invariant on each step */
                printf("Error: The invariant %s is not a state predicate (one with no primes or temporal operators).\n", S(it->name));
                if (level_params(e))
                    printf("Note that a bug can cause TLC to incorrectly report this error.\n"
                           "If you believe your TLA+ or PlusCal specification to be correct,\n"
                           "please check if this bug described in LevelNode.java starting at line 590ff affects you.\n");
                exit(MANYAN_FAILURE_SAFETY_EVAL);
            }
            if (config_check(e, "invariant")) add_check(&invariants, &ninvariants, e->def, e, root_ctx, e->def->name);
        } else if (strncmp(k, "PROPERT", 7) == 0) {
            e = config_call(it->name, "property", 's');
            if (expr_level(e) == 1) {
                Buf b = {0};
                const char *p = S(it->name);
                buf_printf(&b, "The formula %s is a state-level formula, but it was used as a PROPERTY (or PROPERTIES), "
                           "where a temporal formula is typically expected. State-level formulas used as PROPERTY "
                           "or PROPERTIES are only checked in the initial state. To verify that the formula %s "
                           "holds in all states of every behavior, use INVARIANT %s instead. Alternatively, "
                           "applying the \"always\" temporal operator ([]) to the state-level formula %s changes it "
                           "into a temporal formula, asserting that %s holds in all states of every behavior. "
                           "See https://explain.tlapl.us/invariants-and-properties for additional details.", p, p, p, p, p);
                warning(b.s);
                free(b.s);
            }
            if (symbolic_mode) add_check(&temporal_props, &ntemporal_props, e->def, e, root_ctx, it->name);   /* the whole formula, on a lasso */
            else if (config_check(e, "property")) use_property(e);
        } else if (strncmp(k, "CONSTRAINT", 10) == 0) {
            e = config_call(it->name, "constraint", 'r');
            if (config_check(e, "constraint")) add_check(&constraints, &nconstraints, e->def, e, root_ctx, e->def->name);
        } else if (strncmp(k, "ACTION_CONSTRAINT", 17) == 0) {
            e = config_call(it->name, "action constraint", 'r');
            if (config_check(e, "action constraint")) add_check(&action_constraints, &naction_constraints, e->def, e, root_ctx, e->def->name);
        } else if (strcmp(k, "VIEW") == 0) {
            view_expr = config_call(it->name, "view function", 'r');
            if (!literal_def(view_expr) && constant_value(view_expr)) config_error("The view function %s cannot be a constant.", S(it->name));
        }
        else if (strcmp(k, "SYMMETRY") == 0) {
            /* As TLC: an undefined name is reported, any other error as no set of functions. */
            sigjmp_buf here;
            handler = &here;
            if (sigsetjmp(here, 0)) {
                handler = NULL;
                if (error_status == MANYAN_ERROR_CONFIG) { print_error_message(); exit(MANYAN_ERROR_CONFIG); }
                print_exception("java.lang.RuntimeException", ": ");
                printf("The symmetry operator must specify a set of functions.\n");
                exit(MANYAN_ERROR);
            }
            Value *g = enumerate(eval(config_call(it->name, "symmetry function", 0), root_ctx));
            handler = NULL;
            for (int j = 0; j < g->n; j++)
                if (!is_fcn(realize(g->u.set.elems[j]))) {
                    print_exception("java.lang.RuntimeException", ": ");
                    printf("The symmetry values must be function records.\n");
                    exit(MANYAN_ERROR);
                }
            if (!nowarning) warn_symmetry_sets(root_sym(it->name)->def->body, g);
            Value *s = permutation_group(g);
            symmetry = s->u.set.elems;
            nsymmetry = s->n;
            symmetry_tables();
        } else if (strcmp(k, "ALIAS") == 0) alias_name = it->name;
        else if (strncmp(k, "POSTCONDITION", 13) == 0) {
            posts = xrealloc(posts, sizeof *posts * (size_t)(nposts + 1));
            posts[nposts].name = it->name;
            posts[nposts++].module = it->module;
        } else if (strcmp(k, "CHECK_DEADLOCK") == 0) {
            if (it->value->kind == V_BOOL && !it->value->u.i) check_deadlock = 0;
        } else if (strcmp(k, "_PERIODIC") == 0) periodic_expr = config_call(it->name, "periodic", 'r');
        else if (strcmp(k, "_RL_REWARD") == 0) config_call(it->name, "rlreward", 'r');   /* only TLC's reinforcement learning simulation reads it */
        else if (strcmp(k, "_POSSIBLE") == 0 && !symbolic_mode) {
            Sym *s = root_sym(it->name);
            if (s && s->def->kind != D_OP && s->def->kind != D_FCN) config_error("The possible %s cannot be a constant.", S(it->name));
            e = config_call(it->name, "possible", 'r');
            int level = expr_level(e);
            if (level > 2) config_error("The possible of %s is equal to a temporal formula; only state- and action-level predicates are supported", S(it->name));
            Check **list = level == 2 ? &action_constraints : &constraints;
            int *n = level == 2 ? &naction_constraints : &nconstraints;
            add_check(list, n, e->def, e, root_ctx, e->def->name);
            (*list)[*n - 1].possible = ++npossibles;
            possibles = xrealloc(possibles, sizeof(Check) * (size_t)npossibles);
            possibles[npossibles - 1] = (*list)[*n - 1];
            possible_counts = xrealloc(possible_counts, sizeof(int64_t) * (size_t)npossibles);
            possible_counts[npossibles - 1] = -1;
        } else if (k[0] == '_') {
            fprintf(stderr, "manyan: %s is not supported\n", k);
            exit(MANYAN_ERROR);
        }
    }
    }
    return 0;
}


/* ---------------------------------------------------------------- liveness */

/* A behavior violates a property when it satisfies the property's
   negation (§10.5). The negation, in negation normal form over state and
   action predicates, is expanded into a tableau; its product with the
   state graph, where every state may stutter, is searched for a strongly
   connected component that the tableau accepts and the fairness
   conditions allow (§10.6). */

enum { TF_ATOM, TF_AND, TF_OR, TF_ALWAYS, TF_EVENTUALLY, TF_TRUE, TF_FALSE };

typedef struct TF {
    int op;
    struct TF *a, *b;
    Expr *atom;        /* TF_ATOM: a predicate, negated when neg */
    Ctx c;
    int neg, action;   /* action: the predicate relates a state to its successor */
    int index;         /* TF_EVENTUALLY: its acceptance set; TF_ATOM: its cache slot */
} TF;

static TF **eventualities;
static int neventualities;
static TF **atoms;
static int natoms;

static TF *tf_new(int op, TF *a, TF *b) {
    if (op == TF_AND || op == TF_OR) {   /* TLC simplifies a junction with a constant */
        int unit = op == TF_AND ? TF_TRUE : TF_FALSE;
        if (a->op == unit) return b;
        if (b->op == unit) return a;
        if (a->op == TF_TRUE + TF_FALSE - unit) return a;
        if (b->op == TF_TRUE + TF_FALSE - unit) return b;
    }
    if ((op == TF_ALWAYS || op == TF_EVENTUALLY) && a->op == op) return a;   /* as TLC simplifies [][]A and <><>A */
    TF *t = NEW(TF);
    t->op = op; t->a = a; t->b = b;
    if (op == TF_EVENTUALLY) {
        t->index = neventualities;
        eventualities = xrealloc(eventualities, sizeof(TF *) * (size_t)(neventualities + 1));
        eventualities[neventualities++] = t;
    }
    return t;
}

static TF *tf_atom(Expr *e, Ctx c, int neg) {
    TF *t = tf_new(TF_ATOM, NULL, NULL);
    t->atom = e; t->c = c; t->neg = neg;
    t->action = level_in(e, c) >= 2;
    t->index = natoms;
    for (int i = 0; i < natoms; i++)   /* ~A has A's slot */
        if (atoms[i]->atom == e && atoms[i]->c.env == c.env && atoms[i]->c.inst == c.inst) { t->index = atoms[i]->index; break; }
    atoms = xrealloc(atoms, sizeof(TF *) * (size_t)(natoms + 1));
    atoms[natoms++] = t;
    return t;
}

static Expr *synth(int kind, Expr *at, int n, Expr *a, Expr *b) {
    Expr *e = NEW(Expr);
    *e = *at;
    e->kind = (short)kind;
    e->n = n;
    e->args = NEWN(Expr *, 2);
    e->args[0] = a;
    e->args[1] = b;
    e->nb = 0;
    return e;
}

static TF *to_tf(Expr *e, Ctx c, int neg);

/* TLC's error for a temporal formula it cannot handle, with why, if
   known: raised as it builds its tableau, without a stack. */
static _Noreturn void cannot_handle(Expr *e, const char *why) {
    Buf b = {0};
    buf_puts(&b, "TLC cannot handle the temporal formula ");
    loc_text(&b, e);
    if (why) buf_printf(&b, ":\n%s", why);
    error_reset();
    buf_puts(&error_message, b.s);
    free(b.s);
    stackless = 1;
    raise_error();
}

typedef struct { Expr *body; TF *acc; int op; } TfData;

static int tf_bound_fn(Ctx c, void *data) {
    TfData *d = data;
    TF *t = to_tf(d->body, c, 0);
    d->acc = d->acc ? tf_new(d->op, d->acc, t) : t;
    return 0;
}

/* e's value with no state, NULL if evaluating it fails. */
static Value *stateless_value(Expr *e, Ctx c) {
    EvalState s = eval_save();
    ErrorState er = error_save();
    Value **cur = cur_state, **next = next_state;
    cur_state = next_state = NULL;
    Value *volatile v = NULL;
    sigjmp_buf here;
    handler = &here;
    if (!sigsetjmp(here, 0)) v = eval(e, c);
    eval_restore(s);
    error_restore(&er);
    cur_state = cur;
    next_state = next;
    return v;
}

/* The formula e (negated when neg) in negation normal form. */
static TF *to_tf(Expr *e, Ctx c, int neg) {
    int level = level_in(e, c);
    if (level <= 2) {
        if (level == 0) {   /* as TLC, a constant is its value */
            Value *v = eval(e, c);
            if (v->kind != V_BOOL) not_boolean_formula(e);
            return tf_new((v->u.i != 0) != neg ? TF_TRUE : TF_FALSE, NULL, NULL);
        }
        return tf_atom(e, c, neg);
    }
    switch (e->kind) {
    case K_CALL: {
        Def *d = e->def->replacement ? e->def->replacement : e->def;
        if (d->kind != D_OP || d->native) break;
        Env *env = d->local == 2 ? env_find(c.env, d)->ctx_env : NULL;
        for (int i = 0; i < e->n; i++)
            env = d->params[i]->arity ? mk_binding(d->params[i], eval_operator_arg(e->args[i], c), env)
                                      : mk_thunk(d->params[i], e->args[i], c, env);
        deeper();
        TF *t = to_tf(d->body, (Ctx){env, c.inst}, neg);
        eval_depth--;
        return t;
    }
    case K_INSTCALL:
        if (e->def->kind != D_OP || e->def->native) break;
        return to_tf(e->def->body, instance_ctx(e, c), neg);
    case K_AND: case K_OR: {
        int op = (e->kind == K_AND) != neg ? TF_AND : TF_OR;
        TF *t = to_tf(e->args[0], c, neg);
        for (int i = 1; i < e->n; i++) t = tf_new(op, t, to_tf(e->args[i], c, neg));
        return t;
    }
    case K_NOT: return to_tf(e->args[0], c, !neg);
    case X_IF: {
        /* As TLC, a guard that evaluates without a state chooses its branch,
           which ends a recursion; else IF p THEN A ELSE B is
           (p /\ A) \/ (~p /\ B), negated in A and B. */
        Value *g = stateless_value(e->args[0], c);
        if (g && g->kind == V_BOOL) return to_tf(e->args[g->u.i ? 1 : 2], c, neg);
        TF *then = tf_new(TF_AND, to_tf(e->args[0], c, 0), to_tf(e->args[1], c, neg));
        TF *other = tf_new(TF_AND, to_tf(e->args[0], c, 1), to_tf(e->args[2], c, neg));
        return tf_new(TF_OR, then, other);
    }
    case K_IMPLIES: {
        TF *a = to_tf(e->args[0], c, !neg), *b = to_tf(e->args[1], c, neg);
        return tf_new(neg ? TF_AND : TF_OR, a, b);
    }
    case K_EQUIV: {
        TF *both = tf_new(TF_AND, to_tf(e->args[0], c, 0), to_tf(e->args[1], c, neg));
        TF *neither = tf_new(TF_AND, to_tf(e->args[0], c, 1), to_tf(e->args[1], c, !neg));
        return tf_new(TF_OR, both, neither);
    }
    case K_ALWAYS: return tf_new(neg ? TF_EVENTUALLY : TF_ALWAYS, to_tf(e->args[0], c, neg), NULL);
    case K_EVENTUALLY: return tf_new(neg ? TF_ALWAYS : TF_EVENTUALLY, to_tf(e->args[0], c, neg), NULL);
    case K_LEADSTO: {
        /* P ~> Q is [](~P \/ <>Q). */
        Expr *ev = synth(K_EVENTUALLY, e, 1, e->args[1], NULL);
        Expr *body = synth(K_IMPLIES, e, 2, e->args[0], ev);
        return to_tf(synth(K_ALWAYS, e, 1, body, NULL), c, neg);
    }
    case X_WF: case X_SF: {
        /* WF: []<>~ENABLED <<A>>_v \/ []<><<A>>_v; SF: <>[]~ENABLED <<A>>_v \/ []<><<A>>_v. */
        Expr *angle = synth(X_ANGLEACT, e, 2, e->args[1], e->args[0]);
        Expr *en = synth(K_ENABLED, e, 1, angle, NULL);
        if (!neg) {   /* built only so: its eventualities are the tableau's */
            TF *step = tf_new(TF_ALWAYS, tf_new(TF_EVENTUALLY, tf_atom(angle, c, 0), NULL), NULL);
            TF *off = e->kind == X_WF ? tf_new(TF_ALWAYS, tf_new(TF_EVENTUALLY, tf_atom(en, c, 1), NULL), NULL)
                                      : tf_new(TF_EVENTUALLY, tf_new(TF_ALWAYS, tf_atom(en, c, 1), NULL), NULL);
            return tf_new(TF_OR, off, step);
        }
        /* ~WF: <>[]ENABLED /\ <>[]~step; ~SF: []<>ENABLED /\ <>[]~step. */
        TF *nostep = tf_new(TF_EVENTUALLY, tf_new(TF_ALWAYS, tf_atom(angle, c, 1), NULL), NULL);
        TF *on = e->kind == X_WF ? tf_new(TF_EVENTUALLY, tf_new(TF_ALWAYS, tf_atom(en, c, 0), NULL), NULL)
                                 : tf_new(TF_ALWAYS, tf_new(TF_EVENTUALLY, tf_atom(en, c, 0), NULL), NULL);
        return tf_new(TF_AND, on, nostep);
    }
    case X_FORALL: case X_EXISTS: {
        TfData d = {e->args[0], NULL, (e->kind == X_FORALL) != neg ? TF_AND : TF_OR};
        Expr *body = e->args[0];
        if (neg) body = synth(K_NOT, e, 1, body, NULL);
        d.body = body;
        /* As TLC, its own error in the bindings or the body is one it
           cannot handle, saying why for \A. */
        EvalState es = eval_save();
        sigjmp_buf here;
        handler = &here;
        if (sigsetjmp(here, 0)) {
            eval_restore(es);
            if (eval_exception()) raise_error();
            Buf why = {0};
            buf_puts(&why, error_message.s ? error_message.s : "");
            loc_line(&why, error_expr);
            const char *text = buf_take(&why);
            cannot_handle(e, e->kind == X_FORALL ? text : NULL);
        }
        for_bindings(e->bounds, e->nb, c, tf_bound_fn, &d);
        eval_restore(es);
        return d.acc ? d.acc : tf_new(d.op == TF_AND ? TF_TRUE : TF_FALSE, NULL, NULL);
    }
    case X_LET:   /* which TLC cannot handle, and Apalache can */
        if (symbolic_mode) return to_tf(e->args[0], let_env(e, c), neg);
        break;
    default: break;
    }
    cannot_handle(e, NULL);
}

/* A tableau node: the literals that hold now and the formulas that must
   hold from the next state on, among them the eventualities <>A it defers. */
typedef struct { TF **lits; int nlits; TF **next; int nnext; int *succ; int nsucc; int expanded; } TNode;

static TNode *tnodes;
static int ntnodes;

typedef struct { TF **v; int n; } TFList;

static void tfl_add(TFList *l, TF *t) {
    for (int i = 0; i < l->n; i++) if (l->v[i] == t) return;
    TF **grown = NEWN(TF *, l->n + 1);
    if (l->n) memcpy(grown, l->v, sizeof(TF *) * (size_t)l->n);
    grown[l->n++] = t;
    l->v = grown;
}

static int tfl_same(TF **a, int na, TF **b, int nb) {
    if (na != nb) return 0;
    for (int i = 0; i < na; i++) {
        int found = 0;
        for (int j = 0; j < nb && !found; j++) found = a[i] == b[j];
        if (!found) return 0;
    }
    return 1;
}

static int tnode_add(TFList lits, TFList next) {
    for (int i = 0; i < lits.n; i++)
        for (int j = 0; j < lits.n; j++)
            if (lits.v[i]->atom == lits.v[j]->atom && lits.v[i]->c.env == lits.v[j]->c.env && lits.v[i]->neg != lits.v[j]->neg) return -1;
    for (int i = 0; i < ntnodes; i++)
        if (tfl_same(tnodes[i].lits, tnodes[i].nlits, lits.v, lits.n) &&
            tfl_same(tnodes[i].next, tnodes[i].nnext, next.v, next.n)) return i;
    tnodes = xrealloc(tnodes, sizeof(TNode) * (size_t)(ntnodes + 1));
    TNode *t = &tnodes[ntnodes];
    memset(t, 0, sizeof *t);
    t->lits = lits.v; t->nlits = lits.n; t->next = next.v; t->nnext = next.n;
    return ntnodes++;
}

/* Expands the formulas in todo into tableau nodes, adding their indices to out. */
static void expand(TFList todo, TFList lits, TFList next, List *out) {
    if (todo.n == 0) {
        int i = tnode_add(lits, next);
        if (i >= 0) list_add(out, mk_int(i));
        return;
    }
    TF *f = todo.v[todo.n - 1];
    TFList rest = {todo.v, todo.n - 1};
    switch (f->op) {
    case TF_TRUE: expand(rest, lits, next, out); return;
    case TF_FALSE: return;
    case TF_ATOM: { TFList l = lits; tfl_add(&l, f); expand(rest, l, next, out); return; }
    case TF_AND: { TFList r = rest; tfl_add(&r, f->a); tfl_add(&r, f->b); expand(r, lits, next, out); return; }
    case TF_OR: {
        TFList r1 = rest; tfl_add(&r1, f->a); expand(r1, lits, next, out);
        TFList r2 = rest; tfl_add(&r2, f->b); expand(r2, lits, next, out);
        return;
    }
    case TF_ALWAYS: { TFList r = rest; tfl_add(&r, f->a); TFList n = next; tfl_add(&n, f); expand(r, lits, n, out); return; }
    case TF_EVENTUALLY: {
        TFList r1 = rest; tfl_add(&r1, f->a); expand(r1, lits, next, out);
        TFList n = next; tfl_add(&n, f); expand(rest, lits, n, out);
        return;
    }
    }
}

static int tnode_defers(int t, int e) {
    for (int i = 0; i < tnodes[t].nnext; i++) if (tnodes[t].next[i] == eventualities[e]) return 1;
    return 0;
}

static void tnode_expand(int i) {
    if (tnodes[i].expanded) return;
    tnodes[i].expanded = 1;
    List out = {0};
    TFList todo = {tnodes[i].next, tnodes[i].nnext}, none = {0};
    expand(todo, none, none, &out);
    tnodes[i].succ = NEWN(int, out.n);
    for (int k = 0; k < out.n; k++) tnodes[i].succ[k] = (int)out.v[k]->u.i;
    tnodes[i].nsucc = out.n;
}

/* The values of the atoms, 0 unknown, 1 false, 2 true: natoms for each
   state, then from step_atoms[s] natoms for each step of the state graph
   from s, its edges and s stuttering. Shared: workers fill it. */
static signed char *atom_cache;
static size_t atom_cache_size, *step_atoms;
static Value ***decoded;

static Value **state_values(int s) {
    if (!decoded[s]) decoded[s] = decode_state(s);
    return decoded[s];
}

/* t in state s, or on the step from s to the state next. */
static int atom_holds_on(TF *t, int s, Value **next);

/* Whether e holds on the step from cur to next; what it evaluates is
   dropped after, unless the caller's arena is the scratch one. */
/* As TLC's LNAction, [A]_v or <<A>>_v of a temporal formula tests its
   subscript first: a step that leaves v unchanged decides it. */
static int stutters(Expr *e, Ctx c) {
    if (e->kind != X_SQACT && e->kind != X_ANGLEACT) return 0;
    Value *now = eval(e->args[1], c);
    int saved = primed;
    primed = 1;
    Value *then = eval(e->args[1], c);
    primed = saved;
    return veq(now, then);
}

static int holds_in(Expr *e, Ctx c, Value **cur, Value **next) {
    Value **saved_cur = cur_state, **saved_next = next_state;
    Arena *saved_arena = arena;
    cur_state = cur;
    next_state = next;
    arena = &scratch_arena;
    int v = next && stutters(e, c) ? e->kind == X_SQACT : eval_bool(e, c);
    cur_state = saved_cur;
    next_state = saved_next;
    arena = saved_arena;
    if (arena != &scratch_arena) arena_reset(&scratch_arena);
    return v;
}

static int atom_holds(TF *t, int s, int to) { return atom_holds_on(t, s, state_values(to)); }

static signed char *state_atom(TF *t, int s) { return &atom_cache[(size_t)s * (size_t)natoms + (size_t)t->index]; }
static signed char *step_atom(TF *t, int s, int e) { return &atom_cache[step_atoms[s] + (size_t)e * (size_t)natoms + (size_t)t->index]; }

/* t on the state graph's step e of s, to the state `to`. */
static int atom_holds_edge(TF *t, int s, int e, int to) {
    signed char *slot = step_atom(t, s, e);
    if (!*slot) *slot = (signed char)(holds_in(t->atom, t->c, state_values(s), state_values(to)) ? 2 : 1);
    return (*slot == 2) != t->neg;
}

static int atom_holds_on(TF *t, int s, Value **next) {
    int v;
    if (!t->action) {
        signed char *slot = state_atom(t, s);
        if (!*slot) *slot = (signed char)(holds_in(t->atom, t->c, state_values(s), NULL) ? 2 : 1);
        v = *slot == 2;
    } else {
        v = holds_in(t->atom, t->c, state_values(s), next);
    }
    return v != t->neg;
}

static void atom_fill(signed char *slot, TF *t, Value **cur, Value **next) {
    if (*slot) return;
    EvalState saved = eval_save();
    sigjmp_buf here;
    handler = &here;
    if (!sigsetjmp(here, 0)) *slot = (signed char)(holds_in(t->atom, t->c, cur, next) ? 2 : 1);
    eval_restore(saved);
}

/* A worker fills the cache with the action atoms of the steps from the states
   [lo, hi); one that fails, prints or draws it leaves to the search. */
static void worker_atoms(int lo, int hi) {
    Arena *saved = arena;
    arena = &scratch_arena;
    for (int s = lo; s < hi; s++) {
        StateRec *r = &states[s];
        Value **cur = decode_state(s);
        for (int e = 0; e <= r->nedges; e++) {
            Value **next = e < r->nedges ? decode_state(r->edges[2 * e]) : cur;
            for (int i = 0; i < natoms; i++)
                if (atoms[i]->action && atoms[i]->index == i) atom_fill(step_atom(atoms[i], s, e), atoms[i], cur, next);
        }
        arena_reset(&scratch_arena);
    }
    arena = saved;
}

/* Under symmetry or a view a state's successor is kept as the state found
   first with its fingerprint, which may be a permutation of it or another
   state with its view, so an action
   is evaluated, as TLC does, on the successors themselves: a state's
   successors, regenerated once, with their fingerprints. */
typedef struct { int n; Value ***v; uint64_t *fp; } Successors;
static Successors *real_succ;
static List real_found;

static int real_emit(void) {
    for (int i = 0; i < nvars; i++) if (!gen_target[i]) return 0;
    list_add(&real_found, (Value *)memcpy(NEWN(Value *, nvars), gen_target, sizeof(Value *) * (size_t)nvars));
    return 0;
}

static Successors *real_successors(int s) {
    Successors *r = &real_succ[s];
    if (r->v) return r;
    Value **saved_cur = cur_state, **saved_next = next_state, **saved_target = gen_target;
    int (*saved_emit)(void) = gen_emit;
    Value **st = NEWN(Value *, nvars);
    real_found = (List){0};   /* its storage is the arena's, which a simulation resets */
    gen_emit = real_emit;
    gen_target = st;
    cur_state = state_values(s);
    for (int a = 0; a < nactions; a++) {
        memset(st, 0, sizeof(Value *) * (size_t)nvars);
        next_state = st;
        gen(actions[a].e, actions[a].c, NULL);
    }
    cur_state = saved_cur; next_state = saved_next; gen_target = saved_target; gen_emit = saved_emit;
    r->n = real_found.n;
    r->v = NEWN(Value **, r->n + 1);
    r->fp = NEWN(uint64_t, r->n + 1);
    for (int i = 0; i < r->n; i++) { r->v[i] = (Value **)real_found.v[i]; r->fp[i] = fingerprint(r->v[i]); }
    return r;
}

static int tnode_admits(int n, int s) {
    for (int i = 0; i < tnodes[n].nlits; i++) {
        TF *t = tnodes[n].lits[i];
        if (!t->action && !atom_holds(t, s, s)) return 0;
    }
    return 1;
}

/* Whether the step from s to `to`, the state graph's step e of s if e
   is not negative, can satisfy tableau node n's actions: under symmetry
   or a view, some step of s to a state with to's fingerprint, or s
   stuttering, does. */
static int tnode_step(int n, int s, int e, int to) {
    if (!nsymmetry && !view_expr) {
        for (int i = 0; i < tnodes[n].nlits; i++) {
            TF *t = tnodes[n].lits[i];
            if (t->action && !(e >= 0 ? atom_holds_edge(t, s, e, to) : atom_holds(t, s, to))) return 0;
        }
        return 1;
    }
    Successors *r = real_successors(s);
    for (int k = -1; k < r->n; k++) {
        if (k < 0 ? to != s : r->fp[k] != states[to].fp) continue;
        Value **next = k < 0 ? state_values(s) : r->v[k];
        int ok = 1;
        for (int i = 0; i < tnodes[n].nlits && ok; i++) {
            TF *t = tnodes[n].lits[i];
            ok = !t->action || atom_holds_on(t, s, next);
        }
        if (ok) return 1;
    }
    return 0;
}

/* The product graph: nodes are (state, tableau node). */
typedef struct { int state, tnode; int *succ, *act, *edge; int nsucc; int index, low, onstack, mark; char late; } PNode;

static PNode *pnodes;
static int npnodes, cappnodes;
/* Each state's product nodes, as (tableau node, product node) pairs: a
   state has few, and the successors of a step share its target's. */
typedef struct { int tnode, node; } PRef;
typedef struct { PRef *v; int n; } PRefs;
static PRefs *pnodes_of;

static int live_step = -1;   /* the state TLC expands as live_build builds the product */

static int pnode_find(int s, int t, int create) {
    PRefs *l = &pnodes_of[s];
    for (int i = 0; i < l->n; i++) if (l->v[i].tnode == t) return l->v[i].node;
    if (!create) return -1;
    PUSH(l->v, l->n, ((PRef){t, npnodes}));
    if (npnodes == cappnodes) {
        cappnodes = cappnodes ? cappnodes * 2 : 1024;
        pnodes = xrealloc(pnodes, sizeof(PNode) * (size_t)cappnodes);
    }
    PNode *p = &pnodes[npnodes];
    memset(p, 0, sizeof *p);
    p->state = s; p->tnode = t; p->index = -1;
    p->late = live_step >= s;
    return npnodes++;
}


/* The size of the table TLC's worker holds a state's successors in to
   check liveness (SetOfStates): 16 times a multiplier, which grows by one
   after each state whose successors outgrew it, in the order of the
   search. */
static int *live_cap, nlive_cap, live_mult = 1;

static int succ_table_size(int s) {
    for (; nlive_cap <= s; nlive_cap++) {
        if (nlive_cap % 1024 == 0) live_cap = xrealloc(live_cap, sizeof(int) * (size_t)(nlive_cap + 1024));
        StateRec *r = &states[nlive_cap];
        int len = live_cap[nlive_cap] = 16 * live_mult, count = r->nedges + 1;
        for (int e = 0; e < r->nedges; e++) if (r->edges[2 * e] == nlive_cap) count--;
        for (int i = 0; i < count; i++) if (i >= len / 2) len = 2 * len + 1;
        if (len > 16 * live_mult) live_mult++;
    }
    return live_cap[s];
}

static int cmp_int(const void *x, const void *y) { return (*(const int *)x > *(const int *)y) - (*(const int *)x < *(const int *)y); }
static int cmp_u64(const void *x, const void *y) { return (*(const uint64_t *)x > *(const uint64_t *)y) - (*(const uint64_t *)x < *(const uint64_t *)y); }

/* The steps e of state s, edge n its stuttering one if stutter is set, in
   the order TLC's table of them holds the successors: by a fingerprint's
   slot, probing linearly, after the successors, the state itself. A node
   TLC adds once its state is expanded takes the stuttering step first,
   then the others as the actions make them; its simulator's take them so
   with the stuttering step first unless an action makes it. */
static void succ_order(int p, const int *edges, int n, int stutter, int *order) {
    int s = pnodes[p].state;
    if (pnodes[p].late || sim_n) {
        int k = 0, self = n;
        for (int e = 0; e < n && self == n && !sim_n; e++) if (edges[2 * e] == s) self = e;
        if (self < n || stutter) order[k++] = self;
        for (int e = 0; e < n; e++) if (e != self) order[k++] = e;
        return;
    }
    static int *slot, cap, *used, *pend, ncap;   /* slot: all -1 between calls; used: the slots taken */
    int len = succ_table_size(s), count = 0;
    if (n + 1 > ncap) {
        ncap = n + 1;
        used = xrealloc(used, sizeof(int) * (size_t)ncap);
        pend = xrealloc(pend, sizeof(int) * (size_t)ncap);
    }
    for (int e = 0; e < n + stutter; e++) {
        int npend = 0;
        if (count >= len / 2) {   /* TLC's grow: the old slots in order, put again */
            qsort(used, (size_t)count, sizeof(int), cmp_int);
            for (int i = 0; i < count; i++) pend[npend++] = slot[used[i]], slot[used[i]] = -1;
            len = 2 * len + 1;
            count = 0;
        }
        pend[npend++] = e;
        if (len > cap) {
            slot = xrealloc(slot, sizeof(int) * (size_t)len);
            for (int i = cap; i < len; i++) slot[i] = -1;
            cap = len;
        }
        for (int i = 0; i < npend; i++) {
            int x = pend[i], at = (int)((uint32_t)states[x < n ? edges[2 * x] : s].fp & 0x7fffffff) % len;
            while (slot[at] >= 0) at = (at + 1) % len;
            slot[at] = x;
            used[count++] = at;
        }
    }
    qsort(used, (size_t)count, sizeof(int), cmp_int);
    for (int i = 0; i < count; i++) order[i] = slot[used[i]], slot[used[i]] = -1;
}

/* The successors of a product node by the n steps of its state in edges,
   (target, action) pairs, then the stuttering step if stutter is set, with
   each successor of the tableau node; edge is the step's index in the
   state graph, n for stuttering. */
static void pnode_steps(int p, const int *edges, int n, int stutter) {
    static int *found, cap, *order, ncap;   /* (successor, action, step) triples */
    int s = pnodes[p].state, t = pnodes[p].tnode, m = 0, graph = edges == states[s].edges;
    tnode_expand(t);
    if (n + 1 > ncap) order = xrealloc(order, sizeof(int) * (size_t)(ncap = n + 1));
    succ_order(p, edges, n, stutter, order);
    for (int i = 0; i < n + stutter; i++) {
        int e = order[i];
        int target = e < n ? edges[2 * e] : s, action = e < n ? edges[2 * e + 1] : STUTTER;
        if (!tnode_step(t, s, graph ? e : -1, target)) continue;
        for (int k = tnodes[t].nsucc - 1; k >= 0; k--) {   /* in TLC's order */
            int u = tnodes[t].succ[k];
            if (!tnode_admits(u, target)) continue;
            if (3 * m + 3 > cap) found = xrealloc(found, sizeof(int) * (size_t)(cap = 2 * cap + 18));
            found[3 * m] = pnode_find(target, u, 1);
            found[3 * m + 1] = action;
            found[3 * m + 2] = e;
            m++;
        }
    }
    PNode *pn = &pnodes[p];
    pn->succ = alloc_raw(sizeof(int) * (size_t)(3 * m));
    pn->act = pn->succ + m;
    pn->edge = pn->act + m;
    for (int i = 0; i < m; i++) pn->succ[i] = found[3 * i], pn->act[i] = found[3 * i + 1], pn->edge[i] = found[3 * i + 2];
    pn->nsucc = m;
}

/* Each edge of the state graph, and the stuttering step unless an edge is
   one. A state the search stopped before expanding (TLCSet("exit")) has
   none, as TLC's graph has no such node. */
static void pnode_successors(int p) {
    StateRec *r = &states[pnodes[p].state];
    if (exit_requested && pnodes[p].state >= expanded) { pnode_steps(p, NULL, 0, 0); return; }
    int self = 0;
    for (int e = 0; e < r->nedges; e++) self |= r->edges[2 * e] == pnodes[p].state;
    pnode_steps(p, r->edges, r->nedges, !self);
}

/* The product as TLC's simulation builds it from a behavior
   (LiveCheck1.constructBEGraph): the initial nodes with the edges among
   them; then at each position the nodes new at the one before step to
   their tableau successors at its state, and the nodes new there stutter
   to theirs, until none is new. A node has no other successors. */
typedef struct { int *v, n; } Ints;
static Ints *sim_edges;   /* each node's (successor, action) pairs */
static int nsim_edges;

static void sim_link(int p, int to, int act, int **fresh, int *nfresh) {
    int s = pnodes[p].state, t = pnodes[p].tnode;
    tnode_expand(t);
    if (!tnode_step(t, s, -1, to)) return;
    for (int k = tnodes[t].nsucc - 1; k >= 0; k--) {   /* in TLC's order */
        int u = tnodes[t].succ[k], q = pnode_find(to, u, 0);
        if (q < 0) {
            if (!fresh || !tnode_admits(u, to)) continue;
            PUSH(*fresh, *nfresh, q = pnode_find(to, u, 1));
        }
        if (npnodes > nsim_edges) {
            sim_edges = xrealloc(sim_edges, sizeof(Ints) * (size_t)npnodes);
            memset(sim_edges + nsim_edges, 0, sizeof(Ints) * (size_t)(npnodes - nsim_edges));
            nsim_edges = npnodes;
        }
        Ints *e = &sim_edges[p];
        int seen = 0;
        for (int i = 0; i < e->n && !seen; i += 2) seen = e->v[i] == q;
        if (!seen) PUSH(e->v, e->n, q), PUSH(e->v, e->n, act);
    }
}

static void sim_product(int *roots, int nroots) {
    int *from = roots, nfrom = nroots;
    for (int i = 0; i < nfrom; i++) sim_link(from[i], sim_order[0], STUTTER, NULL, NULL);
    for (int i = 1; i < sim_n && nfrom; i++) {
        int *fresh = NULL, nfresh = 0;
        for (int j = 0; j < nfrom; j++) sim_link(from[j], sim_order[i], sim_acts[i], &fresh, &nfresh);
        for (int j = 0; j < nfresh; j++) sim_link(fresh[j], sim_order[i], STUTTER, &fresh, &nfresh);
        from = fresh, nfrom = nfresh;
    }
    for (int p = 0; p < npnodes; p++) {
        Ints none = {0}, *e = p < nsim_edges ? &sim_edges[p] : &none;
        PNode *pn = &pnodes[p];
        pn->nsucc = e->n / 2;
        pn->succ = alloc_raw(sizeof(int) * (size_t)(e->n + 1));
        pn->act = pn->succ + pn->nsucc;
        for (int i = 0; i < pn->nsucc; i++) pn->succ[i] = e->v[2 * i], pn->act[i] = e->v[2 * i + 1];
        *e = (Ints){0};
    }
}

/* Fairness of the specification: WF_v(A) or SF_v(A), as an enabledness
   predicate on states and a step predicate on edges. */
typedef struct { int strong; Expr *enabled, *step; Ctx c; } Fair;

static Fair *fairs;
static int nfairs;

/* The rest of the fairness, such as <>[][A]_v, which TLC checks as a
   conjunct of each negated property. */
static Expr **fair_rest;
static Ctx *fair_rest_c;
static int nfair_rest;

static int fair_enabled(Fair *f, int s) { return holds_in(f->enabled, f->c, state_values(s), next_state); }

static int fair_step(Fair *f, int s, int to) {
    if (to == STUTTER) return 0;
    return holds_in(f->step, f->c, state_values(s), state_values(to));
}

/* Whether the lasso of the n states ls, back to ls[cyc], is fair. */
static int fair_on_lasso(Value ***ls, int n, int cyc) {
    for (int f = 0; f < nfairs; f++) {
        int took = 0, on = 0, off = 0;
        for (int i = cyc; i < n; i++) {
            cur_state = ls[i], next_state = ls[i + 1 < n ? i + 1 : cyc];
            took |= eval_bool(fairs[f].step, fairs[f].c);
            next_state = NULL;
            if (eval_bool(fairs[f].enabled, fairs[f].c)) on = 1;
            else off = 1;
        }
        if (!took && (fairs[f].strong ? on : !off)) return 0;
    }
    return 1;
}

static void collect_fairness(Expr *e, Ctx c);

static int fairness_bound_fn(Ctx c, void *body) {
    collect_fairness(body, c);
    return 0;
}

static void collect_fairness(Expr *e, Ctx c) {
    e = unfold(e);
    if (e->kind == K_AND) { for (int i = 0; i < e->n; i++) collect_fairness(e->args[i], c); return; }
    if (e->kind == X_FORALL) { for_bindings(e->bounds, e->nb, c, fairness_bound_fn, e->args[0]); return; }
    if (e->kind == X_WF || e->kind == X_SF) {
        Expr *angle = synth(X_ANGLEACT, e, 2, e->args[1], e->args[0]);
        fairs = xrealloc(fairs, sizeof(Fair) * (size_t)(nfairs + 1));
        fairs[nfairs].strong = e->kind == X_SF;
        fairs[nfairs].enabled = synth(K_ENABLED, e, 1, angle, NULL);
        fairs[nfairs].step = angle;
        fairs[nfairs].c = c;
        nfairs++;
        return;
    }
    if (e->kind == K_IMPLIES && expr_level(e->args[0]) == 0) {   /* TLC evaluates a constant P of P => F */
        if (eval_bool(e->args[0], c)) collect_fairness(e->args[1], c);
        return;
    }
    if (e->kind == K_CALL && e->def->kind == D_OP && !e->def->native) {
        Env *env = NULL;
        for (int i = 0; i < e->n; i++) env = mk_thunk(e->def->params[i], e->args[i], c, env);
        collect_fairness(e->def->body, (Ctx){env, c.inst});
        return;
    }
    if (e->kind == K_INSTCALL && e->def->kind == D_OP && !e->def->native) {
        collect_fairness(e->def->body, instance_ctx(e, c));
        return;
    }
    if (e->kind != K_ALWAYS && e->kind != K_EVENTUALLY && e->kind != K_LEADSTO) fail_at(e, "TLC cannot handle the fairness condition.");
    fair_rest = xrealloc(fair_rest, sizeof(Expr *) * (size_t)(nfair_rest + 1));
    fair_rest_c = xrealloc(fair_rest_c, sizeof(Ctx) * (size_t)(nfair_rest + 1));
    fair_rest[nfair_rest] = e;
    fair_rest_c[nfair_rest++] = c;
}

static int accept_component(int *nodes, int n);

/* The search's arrays, dropped when the next one starts: an evaluation
   error may end it anywhere. */
static Arena search_arena;

static int *search_ints(int n, const int *from, int nfrom) {
    Arena *saved = arena;
    arena = &search_arena;
    int *a = alloc_raw(sizeof(int) * (size_t)n);
    arena = saved;
    if (nfrom) memcpy(a, from, sizeof(int) * (size_t)nfrom);
    return a;
}

/* Tarjan's algorithm over the product nodes reachable from roots whose
   mark equals `mark`; each component goes to accept_component in
   completion order. Returns the first accepted node or -1. */
/* The product grows as it is explored; the stacks hold at most every node. */
static void grow_stacks(int **stack, int **cstack, int **cedge, int *cap) {
    if (*cap > npnodes) return;
    int was = *cap;
    *cap = npnodes * 2 + 16;
    *stack = search_ints(*cap, *stack, was);
    *cstack = search_ints(*cap, *cstack, was);
    *cedge = search_ints(*cap, *cedge, was);
}

/* TLC's possible error model the search is in, to choose the
   counterexample (pem_search): for each strong fairness condition,
   whether it is to hold as its action is eventually never enabled, else as
   it is taken infinitely often; NULL in the search for the verdict. */
static char *pem_off, *pem_blocked;   /* blocked: by node, 1 where such an action is enabled, 2 where none */
static int npem_blocked;

/* How many of v's successors the search follows: none where an action
   the error model has never enabled is enabled. */
static int pem_succs(int v) {
    if (!pem_off) return pnodes[v].nsucc;
    if (v >= npem_blocked) {
        pem_blocked = xrealloc(pem_blocked, (size_t)npnodes);
        memset(pem_blocked + npem_blocked, 0, (size_t)(npnodes - npem_blocked));
        npem_blocked = npnodes;
    }
    if (!pem_blocked[v]) {
        pem_blocked[v] = 2;
        for (int f = 0; f < nfairs && pem_blocked[v] == 2; f++)
            if (pem_off[f] && fair_enabled(&fairs[f], pnodes[v].state)) pem_blocked[v] = 1;
    }
    return pem_blocked[v] == 1 ? 0 : pnodes[v].nsucc;
}

static int scc_search(int *roots, int nroots, int mark) {
    int index = 0, found = -1, sp = 0, cap = 0;
    int *stack = NULL, *cstack = NULL, *cedge = NULL;
    for (int r = 0; r < nroots && found < 0; r++) {
        int root = roots[r];
        if (pnodes[root].index >= 0 || pnodes[root].mark != mark) continue;
        grow_stacks(&stack, &cstack, &cedge, &cap);
        int cp = 0;
        cstack[cp] = root; cedge[cp] = 0; cp++;
        pnodes[root].index = pnodes[root].low = index++;
        stack[sp++] = root;
        pnodes[root].onstack = 1;
        while (cp > 0 && found < 0) {
            int v = cstack[cp - 1];
            if (!pnodes[v].succ) pnode_successors(v);
            grow_stacks(&stack, &cstack, &cedge, &cap);
            int ns = pem_succs(v);
            if (cedge[cp - 1] < ns) {
                int w = pnodes[v].succ[ns - 1 - cedge[cp - 1]++];   /* the last first, as TLC's stack */
                if (pnodes[w].mark != mark) continue;
                if (pnodes[w].index < 0) {
                    pnodes[w].index = pnodes[w].low = index++;
                    stack[sp++] = w;
                    pnodes[w].onstack = 1;
                    cstack[cp] = w; cedge[cp] = 0; cp++;
                } else if (pnodes[w].onstack && pnodes[w].index < pnodes[v].low) {
                    pnodes[v].low = pnodes[w].index;
                }
                continue;
            }
            cp--;
            if (cp > 0) {
                int u = cstack[cp - 1];
                if (pnodes[v].low < pnodes[u].low) pnodes[u].low = pnodes[v].low;
            }
            if (pnodes[v].low == pnodes[v].index) {
                int start = sp;
                do start--; while (stack[start] != v);
                int n = sp - start;
                for (int i = start; i < sp; i++) pnodes[stack[i]].onstack = 0;
                sp = start;
                found = accept_component(stack + start, n);   /* a nested search has its own stacks */
            }
        }
    }
    return found;
}

static int in_set(int *nodes, int n, int x) {
    for (int i = 0; i < n; i++) if (nodes[i] == x) return 1;
    return 0;
}

static int *accepted;   /* the accepted component */
static int naccepted;

static int tf_tableau(TF *f);
static TF *live_negated;   /* the negated property being checked */

/* Whether the edge k of the node p meets the fairness condition f: a
   step of its action, or for weak fairness one where it is disabled. */
static int fair_edge(int f, int p, int k) {
    int to = pnodes[p].act[k] == STUTTER ? STUTTER : pnodes[pnodes[p].succ[k]].state;
    return fair_step(&fairs[f], pnodes[p].state, to) || (!fairs[f].strong && !fair_enabled(&fairs[f], pnodes[p].state));
}

static int accept_component(int *nodes, int n) {
    /* A component must have an edge inside it. */
    int internal = 0;
    for (int i = 0; i < n && !internal; i++)
        for (int k = 0; k < pem_succs(nodes[i]) && !internal; k++) internal = in_set(nodes, n, pnodes[nodes[i]].succ[k]);
    if (!internal) return -1;
    for (int e = 0; e < neventualities; e++) {
        int ok = 0;
        for (int i = 0; i < n && !ok; i++) ok = !tnode_defers(pnodes[nodes[i]].tnode, e);
        if (!ok) return -1;
    }
    for (int f = 0; f < nfairs; f++) {
        Fair *fr = &fairs[f];
        if (pem_off) {   /* in TLC's error model, met on an edge inside, unless left to its action never enabled */
            int ok = pem_off[f];
            for (int i = 0; i < n && !ok; i++)
                for (int k = 0; k < pem_succs(nodes[i]) && !ok; k++)
                    ok = in_set(nodes, n, pnodes[nodes[i]].succ[k]) && fair_edge(f, nodes[i], k);
            if (!ok) return -1;
            continue;
        }
        int step = 0, disabled = 0, enabled_any = 0;
        for (int i = 0; i < n && !step; i++)
            for (int k = 0; k < pnodes[nodes[i]].nsucc && !step; k++)
                if (in_set(nodes, n, pnodes[nodes[i]].succ[k]))
                    step = fair_step(fr, pnodes[nodes[i]].state, pnodes[nodes[i]].act[k] == STUTTER ? STUTTER : pnodes[pnodes[nodes[i]].succ[k]].state);
        if (step) continue;
        for (int i = 0; i < n; i++) {
            if (fair_enabled(fr, pnodes[nodes[i]].state)) enabled_any = 1;
            else disabled = 1;
        }
        if (!fr->strong) { if (disabled) continue; return -1; }
        if (!enabled_any) continue;
        /* Strong fairness: drop the states where the action is enabled and
           look for components among the rest. */
        int mark = f + 1;
        int *roots = search_ints(n, NULL, 0);
        int nroots = 0;
        for (int i = 0; i < n; i++)
            if (!fair_enabled(fr, pnodes[nodes[i]].state)) { pnodes[nodes[i]].mark = mark; roots[nroots++] = nodes[i]; }
        int found = -1;
        if (nroots) {
            /* The outer search is done with these nodes; search them afresh. */
            int *saved = search_ints(nroots, NULL, 0);
            for (int i = 0; i < nroots; i++) { saved[i] = pnodes[roots[i]].index; pnodes[roots[i]].index = -1; }
            found = scc_search(roots, nroots, mark);
            for (int i = 0; i < nroots; i++) pnodes[roots[i]].index = saved[i];
        }
        for (int i = 0; i < nroots; i++) pnodes[roots[i]].mark = 0;
        return found;
    }
    accepted = xmalloc(sizeof(int) * (size_t)n);
    memcpy(accepted, nodes, sizeof(int) * (size_t)n);
    naccepted = n;
    return nodes[0];
}

/* The shortest path in the product from any of `from` to `to`, within
   nodes accepted by `allowed` (all if NULL): nodes and the actions of the
   edges into them. */
static int product_path(int *from, int nfrom, int to, int *allowed, int nallowed, List *path, List *acts) {
    int n = npnodes;   /* expanding a node may add nodes, which the path does not go through */
    int *prev = xmalloc(sizeof(int) * (size_t)n);
    int *pact = xmalloc(sizeof(int) * (size_t)n);
    int *queue = xmalloc(sizeof(int) * (size_t)n);
    for (int i = 0; i < n; i++) prev[i] = -2;
    int qh = 0, qt = 0;
    for (int i = 0; i < nfrom; i++) if (prev[from[i]] == -2) { prev[from[i]] = -1; pact[from[i]] = -1; queue[qt++] = from[i]; }
    int found = 0;
    while (qh < qt) {
        int v = queue[qh++];
        if (v == to) { found = 1; break; }
        if (!pnodes[v].succ) pnode_successors(v);
        for (int k = 0; k < pnodes[v].nsucc; k++) {
            int w = pnodes[v].succ[k];
            if (w >= n || prev[w] != -2) continue;
            if (allowed && !in_set(allowed, nallowed, w)) continue;
            prev[w] = v;
            pact[w] = pnodes[v].act[k];
            queue[qt++] = w;
        }
    }
    if (found) {
        int n = 0;
        for (int v = to; v >= 0; v = prev[v]) n++;
        int *rev = xmalloc(sizeof(int) * (size_t)n);
        int k = n;
        for (int v = to; v >= 0; v = prev[v]) rev[--k] = v;
        for (int i = 0; i < n; i++) { list_add(path, mk_int(rev[i])); list_add(acts, mk_int(pact[rev[i]])); }
        free(rev);
    }
    free(prev); free(pact); free(queue);
    return found;
}

/* State number of a counterexample, state s, after the state prev (-1 for none). */
static void print_live_state(int number, int s, int action, int prev, int next) {
    print_numbered(number, action, state_values(s), prev < 0 ? NULL : state_values(prev), state_values(next));
}

/* Whether t holds from position pos of the lasso of the n states ls,
   whose last is followed by the one at cyc. */
static int holds_on_lasso(TF *t, Value ***ls, int n, int cyc, int pos) {
    switch (t->op) {
    case TF_TRUE: return 1;
    case TF_FALSE: return 0;
    case TF_AND: return holds_on_lasso(t->a, ls, n, cyc, pos) && holds_on_lasso(t->b, ls, n, cyc, pos);
    case TF_OR: return holds_on_lasso(t->a, ls, n, cyc, pos) || holds_on_lasso(t->b, ls, n, cyc, pos);
    case TF_ATOM:
        return holds_in(t->atom, t->c, ls[pos], t->action ? ls[pos + 1 < n ? pos + 1 : cyc] : NULL) != t->neg;
    default: {   /* from pos on, which in the cycle is all of it */
        int always = t->op == TF_ALWAYS;
        for (int i = pos < cyc ? pos : cyc; i < n; i++)
            if (holds_on_lasso(t->a, ls, n, cyc, i) != always) return !always;
        return always;
    }
    }
}

/* The values of the n states ls. */
static Value ***lasso_values(int *ls, int n) {
    Value ***v = NEWN(Value **, n);
    for (int i = 0; i < n; i++) v[i] = state_values(ls[i]);
    return v;
}

/* Prints, as TLC, the properties the lasso violates, each by the name of
   its PROPERTY; one that fails to evaluate is left out. */
static void print_violated(Value ***ls, int n, int cyc) {
    int saved_atoms = natoms, saved_eventualities = neventualities;
    int *names = NEWN(int, ntemporal_props + 1), nnames = 0;
    for (int p = 0; p < ntemporal_props; p++) {
        EvalState saved = eval_save();
        sigjmp_buf here;
        handler = &here;
        volatile int violated = 0;
        if (!sigsetjmp(here, 0)) violated = !holds_on_lasso(to_tf(temporal_props[p].expr, temporal_props[p].ctx, 0), ls, n, cyc, 0);
        eval_restore(saved);
        int name = temporal_props[p].def->name, seen = 0;
        for (int i = 0; i < nnames; i++) seen |= names[i] == name;
        if (violated && !seen) names[nnames++] = name;
    }
    natoms = saved_atoms;
    neventualities = saved_eventualities;
    if (nnames == 1) printf("Error: Temporal property %s was violated.\n\n", S(names[0]));
    else if (nnames == 0) printf("Error: Temporal properties were violated.\n\n");
    else {
        printf("Error: Temporal properties ");
        for (int i = 0; i < nnames; i++)
            printf("%s%s", i == 0 ? "" : i < nnames - 1 ? ", " : nnames == 2 ? " and " : ", and ", S(names[i]));
        printf(" were violated.\n\n");
    }
}

/* Whether the node p meets the eventuality e on the walk: its tableau node
   has it met, or, where TLC checks the property without a tableau, as
   []<>P, P holds in its state. */
static int eventuality_met(int e, int p) {
    TF *a = eventualities[e]->a;
    if (a->op == TF_ATOM && a->action) return 0;   /* met on an edge: eventuality_step */
    return !tnode_defers(pnodes[p].tnode, e) ||
           (!tf_tableau(live_negated) && a->op == TF_ATOM && !a->action && atom_holds_on(a, pnodes[p].state, NULL));
}

/* Whether the edge k of the node p meets the eventuality e of an action,
   which TLC checks on the edges of the cycle, as []<>A. */
static int eventuality_step(int e, int p, int k) {
    TF *a = eventualities[e]->a;
    int w = pnodes[p].succ[k];
    return a->op == TF_ATOM && a->action && atom_holds_on(a, pnodes[p].state, state_values(pnodes[w].state));
}

/* The cycle as TLC's printTrace starts it (LiveWorker.dfsPostFix): a walk
   through the accepted component from the entry that takes an edge
   meeting a fairness condition as soon as it sees one, and else goes on to
   a node not seen since the last condition met, back up where there is
   none, until each eventuality and condition is met. A strong one without
   a step in the component holds as its action is never enabled there.
   Adds the nodes after the entry to cyc, the action into each to acts,
   and returns the last. */
static int live_walk(int entry, List *cyc, List *acts) {
    char *where = xcalloc((size_t)npnodes, 1);   /* 1 in the component, 2 seen too */
    for (int i = 0; i < naccepted; i++) where[accepted[i]] = 1;
    int nmet = neventualities + nfairs, cnt = 0;
    char *met = xcalloc((size_t)nmet + 1, 1);
    for (int f = 0; f < nfairs; f++) {
        met[neventualities + f] = fairs[f].strong;
        for (int i = 0; i < naccepted && met[neventualities + f]; i++)
            for (int k = 0; k < pnodes[accepted[i]].nsucc; k++)
                if (where[pnodes[accepted[i]].succ[k]] && fair_edge(f, accepted[i], k)) { met[neventualities + f] = 0; break; }
    }
    for (int i = 0; i < nmet; i++) cnt += !met[i];
    List stack = {0}, sacts = {0};   /* the walk before cur, and the action into each */
    int cur = entry, act = -1;
    where[entry] = 2;
    while (cnt > 0) {
        int cnt0 = cnt, to = -1, to_act = 0, reset = 0;
        while (to < 0) {
            for (int e = 0; e < neventualities; e++)
                if (!met[e] && eventuality_met(e, cur)) met[e] = 1, cnt--;
            if (cnt <= 0) break;
            int next = -1, next_act = 0, unseen = -1, unseen_act = 0, cnt1 = cnt;
            for (int k = 0; k < pnodes[cur].nsucc && to < 0; k++) {
                int w = pnodes[cur].succ[k];
                if (!where[w]) continue;
                next = w, next_act = pnodes[cur].act[k];
                for (int e = 0; e < neventualities; e++)
                    if (!met[e] && eventuality_step(e, cur, k)) met[e] = 1, cnt--;
                for (int f = 0; f < nfairs; f++)
                    if (!met[neventualities + f] && fair_edge(f, cur, k)) met[neventualities + f] = 1, cnt--;
                if (cnt < cnt1) to = w, to_act = next_act, reset = 1;
                else if (where[w] == 1) unseen = w, unseen_act = next_act;
            }
            if (to < 0 && cnt < cnt0) to = next, to_act = next_act, reset = 1;
            if (to >= 0) break;
            while (unseen < 0 && stack.n > 0) {   /* back up */
                cur = (int)stack.v[--stack.n]->u.i, act = (int)sacts.v[--sacts.n]->u.i;
                for (int k = 0; k < pnodes[cur].nsucc && unseen < 0; k++)
                    if (where[pnodes[cur].succ[k]] == 1) unseen = pnodes[cur].succ[k], unseen_act = pnodes[cur].act[k];
            }
            if (unseen < 0) break;
            to = unseen, to_act = unseen_act;
            where[to] = 2;
        }
        if (to < 0) break;
        list_add(&stack, mk_int(cur));
        list_add(&sacts, mk_int(act));
        cur = to, act = to_act;
        if (reset)
            for (int i = 0; i < naccepted; i++) where[accepted[i]] = 1;
    }
    for (int i = 1; i < stack.n; i++) { list_add(cyc, stack.v[i]); list_add(acts, sacts.v[i]); }
    if (stack.n) { list_add(cyc, mk_int(cur)); list_add(acts, mk_int(act)); }
    free(where); free(met);
    return cur;
}

/* Closes the cycle as TLC does (LiveWorker.bfsPostFix): the shortest way
   from the state of the node from to the entry, by states of the accepted
   component, each taking the edges of all its nodes there. */
static void live_back(int from, int entry, List *cyc, List *acts) {
    int *first = xmalloc(sizeof(int) * (size_t)nstates), *next = xmalloc(sizeof(int) * (size_t)naccepted);
    int *prev = xmalloc(sizeof(int) * (size_t)nstates), *pact = xmalloc(sizeof(int) * (size_t)nstates);
    int *queue = xmalloc(sizeof(int) * (size_t)nstates);
    for (int s = 0; s < nstates; s++) first[s] = -1, prev[s] = -2;
    for (int i = naccepted - 1; i >= 0; i--) next[i] = first[pnodes[accepted[i]].state], first[pnodes[accepted[i]].state] = i;
    int qh = 0, qt = 0, last = -1, back = 0;
    queue[qt++] = pnodes[from].state;
    prev[pnodes[from].state] = -1;
    while (qh < qt && last < 0) {
        int s = queue[qh++];
        for (int i = first[s]; i >= 0 && last < 0; i = next[i]) {
            int p = accepted[i];
            for (int k = 0; k < pnodes[p].nsucc && last < 0; k++) {
                int w = pnodes[p].succ[k], ws = pnodes[w].state;
                if (w == p) continue;
                if (w == entry) last = s, back = pnodes[p].act[k];
                else if (first[ws] >= 0 && prev[ws] == -2) prev[ws] = s, pact[ws] = pnodes[p].act[k], queue[qt++] = ws;
            }
        }
    }
    int n = 0;
    for (int s = last; s >= 0 && prev[s] >= 0; s = prev[s]) queue[n++] = s;
    while (n > 0) {
        int s = queue[--n];
        list_add(cyc, mk_int(accepted[first[s]]));
        list_add(acts, mk_int(pact[s]));
    }
    list_add(cyc, mk_int(entry));
    list_add(acts, mk_int(back));
    free(first); free(next); free(prev); free(pact); free(queue);
}

/* Drops each of the first n nodes whose state is the one before it, prev
   before the first, and the node before the last one of its state: as
   TLC, a state is printed once where the lasso only moves between its
   tableau nodes. */
static void drop_repeats(List *nodes, List *acts, int n, int prev) {
    int k = 0;
    for (int i = 0; i < nodes->n; i++) {
        int s = pnodes[nodes->v[i]->u.i].state;
        if (i < n && s == prev) continue;
        prev = s;
        nodes->v[k] = nodes->v[i];
        acts->v[k++] = acts->v[i];
    }
    if (n < nodes->n && k > 1 && pnodes[nodes->v[k - 1]->u.i].state == pnodes[nodes->v[k - 2]->u.i].state)
        nodes->v[k - 2] = nodes->v[k - 1], k--;   /* the last kept, with the step into its state */
    nodes->n = acts->n = k;
}

/* Prints a lasso through the accepted component: the shortest path to it,
   then a cycle that meets each eventuality and fairness condition. */
static void warn_stuttering(void);
/* Prints the lasso of the n states ls, entered by the actions la (la[0]
   -1), its cycle back to ls[entry] by the action back, or with entry
   negative its last state stuttering, by back for a CounterExample; cyc
   is where the properties are evaluated to loop back. */
static void print_lasso(int *ls, int *la, int n, int entry, int back, int cyc) {
    int stutter = entry < 0;
    print_violated(lasso_values(ls, n), n, cyc);
    printf("Error: The following behavior constitutes a counter-example:\n\n");
    for (int i = 0; i < n; i++) {
        print_live_state(i + 1, ls[i], i ? la[i] : -1, i ? ls[i - 1] : -1, ls[i + 1 < n ? i + 1 : stutter ? i : entry]);
        if (i == entry) post_behavior(lasso_values(ls, n), la, n, entry + 1, back, 0);
    }
    if (stutter) {
        printf("State %d: Stuttering\n", n + 1);
        warn_stuttering();
        post_behavior(lasso_values(ls, n), la, n, n, back, 0);
        return;
    }
    printf("Back to state %d: ", entry + 1);
    action_label(back);
    printf("\n\n");
}

static void print_counterexample(int *inits, int ninits) {
    List path = {0}, acts = {0};
    int entry = accepted[0];   /* as TLC, the root of the component in the search */
    product_path(inits, ninits, entry, NULL, 0, &path, &acts);
    List cyc = {0}, cacts = {0};
    int cur = live_walk(entry, &cyc, &cacts);
    int stutter_only = cyc.n == 0;
    if (cur != entry) live_back(cur, entry, &cyc, &cacts);
    drop_repeats(&path, &acts, path.n, -1);
    if (!stutter_only) {
        drop_repeats(&cyc, &cacts, cyc.n - 1, pnodes[entry].state);
        stutter_only = cyc.n == 1;
    }
    int n = path.n + (stutter_only ? 0 : cyc.n - 1);
    int *ls = NEWN(int, n + 1), *la = NEWN(int, n + 1);
    for (int i = 0; i < n; i++) {
        ls[i] = pnodes[(i < path.n ? path.v[i] : cyc.v[i - path.n])->u.i].state;
        la[i] = i ? (int)(i < path.n ? acts.v[i] : cacts.v[i - path.n])->u.i : -1;
    }
    if (stutter_only) print_lasso(ls, la, n, -1, sim_n ? -2 : la[n - 1], n - 1);   /* by the step into it, as TLC's search; none, as its simulator */
    else print_lasso(ls, la, n, path.n - 1, (int)cacts.v[cyc.n - 1]->u.i, path.n - 1);
}

/* Whether TLC checks a formula with a tableau: it has a temporal part
   other than []<>P and <>[]P. */
static int tf_tableau(TF *f) {
    switch (f->op) {
    case TF_AND: case TF_OR: return tf_tableau(f->a) || tf_tableau(f->b);
    case TF_ALWAYS: case TF_EVENTUALLY:
        return f->a->op == f->op || (f->a->op != TF_ALWAYS && f->a->op != TF_EVENTUALLY) || f->a->a->op != TF_ATOM;
    default: return 0;
    }
}

/* Whether f has a temporal operator, or else an action. */
static int tf_has(TF *f, int temporal) {
    if (!f) return 0;
    if (f->op == TF_ATOM) return !temporal && f->action;
    return (temporal && (f->op == TF_ALWAYS || f->op == TF_EVENTUALLY)) || tf_has(f->a, temporal) || tf_has(f->b, temporal);
}

static int tf_box(TF *f) { return f && (f->op == TF_ALWAYS || tf_box(f->a) || tf_box(f->b)); }

/* Whether the negation f is more than a tableau without cycle conditions
   TLC's way: a conjunct <>[]A or []<>A, or a promise <>F with a [] in F. */
static int tf_promise_box(TF *f);
static int tf_conditions(TF *f) {
    if (f->op == TF_AND || f->op == TF_OR) return tf_conditions(f->a) || tf_conditions(f->b);
    if ((f->op == TF_EVENTUALLY && f->a->op == TF_ALWAYS) || (f->op == TF_ALWAYS && f->a->op == TF_EVENTUALLY))
        if (!tf_has(f->a->a, 1)) return 1;
    return tf_promise_box(f);
}

static int tf_promise_box(TF *f) {
    return f && ((f->op == TF_EVENTUALLY && tf_box(f->a)) || tf_promise_box(f->a) || tf_promise_box(f->b));
}

/* TLC's warning after a counterexample that ends stuttering, that the
   behavior specification may lack fairness. */
static void warn_stuttering(void) {
    if (simulating || !tf_conditions(live_negated)) return;
    if (!spec_def) {
        warning("The stuttering counterexample above may be caused by the absence of a behavior specification "
                "(SPECIFICATION). Only INIT and NEXT have been provided, so TLC permits infinite stuttering. "
                "To rule out such counterexamples, use SPECIFICATION Spec, with Spec asserting a suitable fairness "
                "constraint (compare Chapter 8, page 87ff of Specifying Systems at "
                "https://lamport.azurewebsites.net/tla/book.html).");
        return;
    }
    if (nfairness) return;
    Buf at = {0}, b = {0};
    Expr whole = *spec_def->where;   /* the definition, from its name to its body's end */
    whole.l2 = spec_def->body->l2;
    whole.c2 = spec_def->body->c2;
    loc_text(&at, &whole);
    const char *name = S(spec_def->name);
    buf_printf(&b, "The stuttering counterexample above may be caused by the absence of a fairness constraint "
               "in the behavior specification %s defined at %s. To rule out such counterexamples, conjoin a "
               "suitable fairness constraint to %s (compare Chapter 8, page 87ff of Specifying Systems at "
               "https://lamport.azurewebsites.net/tla/book.html).", name, at.s, name);
    warning(b.s);
    free(at.s);
    free(b.s);
}

/* The product nodes of the initial states, as TLC adds them. */
static int live_roots(TF *negated, int **roots) {
    List init = {0};
    TFList todo = {0}, empty = {0};
    tfl_add(&todo, negated);
    expand(todo, empty, empty, &init);
    int n = 0;
    *roots = NULL;
    for (int s = 0; s < nstates; s++) {
        if (states[s].parent != -1) continue;
        for (int i = 0; i < init.n; i++) {
            int t = (int)init.v[i]->u.i;
            if (tnode_admits(t, s)) PUSH(*roots, n, pnode_find(s, t, 1));
        }
    }
    return n;
}

/* Chooses the component a counterexample goes through as TLC does when
   there is strong fairness: TLC checks SF_v(A), <>[]~ENABLED <<A>>_v \/
   []<><<A>>_v, as each of its disjuncts in turn, and prints a component
   of the first of these error models that has one. */
static void pem_search(int *roots, int nroots) {
    int strong[10], k = 0;
    for (int f = 0; f < nfairs; f++)
        if (fairs[f].strong) {
            if (k == 10) return;   /* 1024 error models: keep the verdict's */
            strong[k++] = f;
        }
    if (!k) return;
    for (int p = 0; p < npnodes; p++)
        if (!pnodes[p].succ) pnode_successors(p);
    int nall = nroots + npnodes, *all = xmalloc(sizeof(int) * (size_t)nall);
    memcpy(all, roots, sizeof(int) * (size_t)nroots);
    for (int p = 0; p < npnodes; p++) all[nroots + p] = p;
    int *was = accepted, nwas = naccepted, found = -1;
    pem_off = xcalloc((size_t)nfairs, 1);
    for (int m = 0; m < 1 << k && found < 0; m++) {
        for (int i = 0; i < k; i++) pem_off[strong[i]] = !(m >> (k - 1 - i) & 1);
        for (int p = 0; p < npnodes; p++) pnodes[p].index = -1, pnodes[p].onstack = 0;
        npem_blocked = 0;
        arena_reset(&search_arena);
        found = scc_search(all, nall, 0);
    }
    if (found < 0) accepted = was, naccepted = nwas;
    else free(was);
    free(pem_off); free(all);
    pem_off = NULL;
}

/* TLC's simulator's search of a behavior's product with no fairness and
   no []<> or <>[] conditions (LiveCheck1): Tarjan's from each initial
   node in turn, numbering nodes as TLC does; the first component with an
   edge inside that meets each eventuality is printed with the cycle TLC
   walks from its root, after the shortest path to it. */
#define SIM_FIRST 0x2000000000000000LL
#define SIM_SECOND 0x5000000000000000LL
static int64_t *snum, sn1, sn2, sn3, snfirst, snsecond, snstart2, snstart3;
static Ints scom;   /* the component stack */
static int sim_hit = -1;   /* the root of the component found */

static int self_edge(int p) {
    for (int i = 0; i < pnodes[p].nsucc; i++) if (pnodes[p].succ[i] == p) return 1;
    return 0;
}

static void sim_subcomponent(int node) {   /* checkSubcomponent */
    char *met = xcalloc((size_t)neventualities + 1, 1);
    int *stack = NULL, n = 0;
    snum[node]++;
    PUSH(stack, n, node);
    while (n) {
        int cur = stack[--n];
        for (int i = 0; i < pnodes[cur].nsucc; i++) {
            int d = pnodes[cur].succ[i];
            if (snum[d] == sn3) snum[d]++, PUSH(stack, n, d);
        }
        for (int e = 0; e < neventualities; e++) if (!tnode_defers(pnodes[cur].tnode, e)) met[e] = 1;
    }
    sn3 += 2;
    int all = 1;
    for (int e = 0; e < neventualities; e++) all &= met[e];
    free(met);
    if (all) sim_hit = node;
}

/* Tarjan's from root: over all nodes (checkSccs), or within the
   component just taken (checkSccs1); each component found is checked. */
static void sim_sccs(int root, int second) {
    typedef struct { int node, i; int64_t low; } Frame;
    Frame *f = NULL;
    int nf = 0;
    PUSH(f, nf, ((Frame){root, 0, snum[root] = second ? sn2++ : sn1++}));
    PUSH(scom.v, scom.n, root);
    while (nf && sim_hit < 0) {
        Frame *t = &f[nf - 1];
        if (t->i < pnodes[t->node].nsucc) {
            int d = pnodes[t->node].succ[t->i++];
            int64_t dn = snum[d];
            if (second ? snfirst <= dn && (dn < snstart2 || (snsecond <= dn && dn < snstart3)) : dn == 0) {
                PUSH(f, nf, ((Frame){d, 0, snum[d] = second ? sn2++ : sn1++}));
                PUSH(scom.v, scom.n, d);
                continue;
            }
            if ((!second || snfirst <= dn) && dn < t->low) t->low = dn;
            continue;
        }
        Frame done = f[--nf];
        if (nf && done.low < f[nf - 1].low) f[nf - 1].low = done.low;
        if (done.low != snum[done.node]) continue;
        int top = scom.v[--scom.n];
        if (second) {   /* extractComponent1 */
            if (top == done.node && !self_edge(top)) { snum[top] = sn3++; continue; }
            snum[top] = sn3;
            while (top != done.node) snum[top = scom.v[--scom.n]] = sn3;
            sim_subcomponent(done.node);
            continue;
        }
        if (top == done.node && !self_edge(top)) { snum[top] = SIM_FIRST; continue; }   /* extractComponent */
        int *nodes = NULL, nn = 0;
        snfirst = sn2++;
        snsecond = sn3;
        snum[top] = snfirst;
        PUSH(nodes, nn, top);
        while (top != done.node) snum[top = scom.v[--scom.n]] = snfirst, PUSH(nodes, nn, top);
        snstart2 = sn2;
        snstart3 = sn3;
        for (int j = nn - 1; j >= 0 && sim_hit < 0; j--)
            if (snum[nodes[j]] < snstart3) sim_sccs(nodes[j], 1);
    }
}

/* The cycle printErrorTrace walks from node through its component,
   meeting each eventuality, back to node: its nodes from node on. */
static void sim_cycle(int node, Ints *cyc) {
    int64_t low = sn3 - 1;
    char *met = xcalloc((size_t)neventualities + 1, 1);
    int cnt = neventualities, cur = node;
    while (cnt > 0) {
        snum[cur] = sn3;
        int cnt0 = cnt;
        for (;;) {
            for (int e = 0; e < neventualities; e++)
                if (!met[e] && !tnode_defers(pnodes[cur].tnode, e)) met[e] = 1, cnt--;
            if (cnt <= 0) break;
            int next1 = -1, next2 = -1;
            for (int i = 0; i < pnodes[cur].nsucc; i++) {
                int d = pnodes[cur].succ[i];
                if (low <= snum[d] && snum[d] <= sn3) next1 = d;
                if (low <= snum[d] && snum[d] < sn3) next2 = d;
            }
            if (cnt < cnt0) { PUSH(cyc->v, cyc->n, cur); cur = next1; sn3++; break; }
            while (next2 < 0) {
                cur = cyc->v[--cyc->n];
                for (int i = 0; i < pnodes[cur].nsucc && next2 < 0; i++) {
                    int d = pnodes[cur].succ[i];
                    if (low <= snum[d] && snum[d] < sn3) PUSH(cyc->v, cyc->n, cur), next2 = d;
                }
            }
            PUSH(cyc->v, cyc->n, cur);
            cur = next2;
            snum[cur] = sn3;
        }
    }
    free(met);
    snum[cur] = ++sn3;
    while (cur != node) {
        int found = 0, i;
        for (i = 0; i < pnodes[cur].nsucc; i++) {
            int d = pnodes[cur].succ[i];
            if (low <= snum[d] && snum[d] < sn3) break;
        }
        if (i < pnodes[cur].nsucc) {
            int d = pnodes[cur].succ[i];
            PUSH(cyc->v, cyc->n, cur);
            if (d == node) break;
            found = 1;
            snum[cur = d] = sn3;
        }
        if (!found) cur = cyc->v[--cyc->n];
    }
    if (!cyc->n) PUSH(cyc->v, cyc->n, cur);
}

/* The action of the edge from p to q. */
static int edge_act(int p, int q) {
    for (int i = 0; i < pnodes[p].nsucc; i++) if (pnodes[p].succ[i] == q) return pnodes[p].act[i];
    return STUTTER;
}

static int sim_search(int *roots, int nroots) {
    snum = xcalloc((size_t)npnodes, sizeof *snum);
    sn1 = 1, sn2 = SIM_FIRST + 1, sn3 = SIM_SECOND + 1, snfirst = sn2, snsecond = sn3;
    scom.n = 0;
    sim_hit = -1;
    int init = -1;
    for (int r = 0; r < nroots && sim_hit < 0; r++)
        if (snum[roots[r]] == 0) sim_sccs(init = roots[r], 0);
    if (sim_hit < 0) { free(snum); return 0; }
    Ints cyc = {0};
    sim_cycle(sim_hit, &cyc);
    free(snum);
    /* The shortest path from the initial node to the root (BEGraph.getPath). */
    int *parent = xmalloc(sizeof(int) * (size_t)npnodes), *queue = xmalloc(sizeof(int) * (size_t)npnodes), head = 0, tail = 0;
    for (int p = 0; p < npnodes; p++) parent[p] = -2;
    parent[init] = -1;
    queue[tail++] = init;
    while (init != sim_hit && parent[sim_hit] == -2) {
        int cur = queue[head++];
        for (int i = 0; i < pnodes[cur].nsucc && parent[sim_hit] == -2; i++) {
            int d = pnodes[cur].succ[i];
            if (parent[d] == -2) parent[d] = cur, queue[tail++] = d;
        }
    }
    int np = 0;
    for (int p = sim_hit; p >= 0; p = parent[p]) queue[np++] = p;
    int *ls = NEWN(int, np + cyc.n + 1), *la = NEWN(int, np + cyc.n + 1), n = 0;
    for (int i = np - 1; i >= 0; i--) {   /* each state once, entered by its first node */
        int p = queue[i];
        if (n && ls[n - 1] == pnodes[p].state) continue;
        la[n] = n ? edge_act(queue[i + 1], p) : -1;
        ls[n++] = pnodes[p].state;
    }
    int entry = n - 1;
    for (int i = 1; i < cyc.n; i++)
        if (pnodes[cyc.v[i]].state != pnodes[cyc.v[i - 1]].state)
            la[n] = edge_act(cyc.v[i - 1], cyc.v[i]), ls[n++] = pnodes[cyc.v[i]].state;
    free(parent);
    free(queue);
    if (ls[n - 1] == pnodes[sim_hit].state) print_lasso(ls, la, n, -1, -2, entry);   /* by no action, as TLC's simulator */
    else print_lasso(ls, la, n, entry, edge_act(cyc.v[cyc.n - 1], sim_hit), entry);
    return 1;
}

static int has_actions(void) {
    for (int i = 0; i < natoms; i++) if (atoms[i]->action) return 1;
    return 0;
}

static int live_build(TF *negated, int cut, int *at);

static int check_property(TF *negated) {
    live_negated = negated;
    int *r, n = live_roots(negated, &r);
    if (sim_n && tf_tableau(negated)) {
        sim_product(r, n);
        if (!nfairs && !nfair_rest && !tf_conditions(negated)) return sim_search(r, n);
    }
    else if (nworkers > 1 && !nsymmetry && !view_expr && has_actions()) {
        stop_workers();   /* to fork with this property's atoms */
        run_level(0, nstates, BATCH, 0, ATOMS);
    }
    if (!sim_n) live_build(negated, 0, NULL);
    arena_reset(&search_arena);
    if (scc_search(r, n, 0) >= 0) {
        pem_search(r, n);
        print_counterexample(r, n);
        return 1;
    }
    return 0;
}

/* Whether a disjunct of f, in TLC's disjunctive normal form, has no
   conjunct <>[]A or []<>A with A no temporal formula. */
static int tf_cycle_free(TF *f) {
    if (f->op == TF_OR) return tf_cycle_free(f->a) || tf_cycle_free(f->b);
    if (f->op == TF_AND) return tf_cycle_free(f->a) && tf_cycle_free(f->b);
    return !((f->op == TF_EVENTUALLY && f->a->op == TF_ALWAYS) || (f->op == TF_ALWAYS && f->a->op == TF_EVENTUALLY)) ||
           tf_has(f->a->a, 1);
}

/* TLC builds the product as it expands each state: the edges of the
   state's nodes, then those of each node new to it whose state is
   expanded already. When such a node's tableau node has nothing left to
   do, a negation with a disjunct free of cycle conditions, and no
   fairness, is met by any continuation of the path to it, and TLC stops
   there (§10.7), if cut is set. Returns the state being expanded then,
   or -1; *at is the node. */
static int live_build(TF *negated, int cut, int *at) {
    int *stack = NULL, n = 0, *roots, found = -1;
    live_roots(negated, &roots);   /* the graph starts with them */
    for (int s0 = 0; s0 < expanded && found < 0; s0++)
        for (int i = 0; i < pnodes_of[s0].n && found < 0; i++) {
            if (pnodes[pnodes_of[s0].v[i].node].succ) continue;
            live_step = s0;
            PUSH(stack, n, pnodes_of[s0].v[i].node);
            while (n && found < 0) {
                int v = stack[--n];
                if (pnodes[v].succ) continue;
                pnode_successors(v);
                for (int k = 0; k < pnodes[v].nsucc && cut && found < 0; k++) {
                    int w = pnodes[v].succ[k];
                    if (!pnodes[w].succ && pnodes[w].state <= s0 && !tnodes[pnodes[w].tnode].nnext) *at = w, found = s0;
                }
                for (int k = pnodes[v].nsucc - 1; k >= 0; k--) {
                    int w = pnodes[v].succ[k];
                    if (!pnodes[w].succ && pnodes[w].state <= s0) PUSH(stack, n, w);
                }
            }
        }
    live_step = -1;
    return found;
}

static int live_cut_at(TF *negated, int *at) {
    if (sim_n || nfairs || nfair_rest || !tf_tableau(negated) || !tf_cycle_free(negated)) return -1;
    return live_build(negated, 1, at);
}

/* Prints, as TLC, the path to node `at` as a finite counterexample, its
   last state stuttering forever; the graph is as built so far. */
static void print_cut(int at) {
    int *r, nr = live_roots(live_negated, &r);
    for (int p = 0; p < npnodes; p++) if (!pnodes[p].succ) pnode_steps(p, NULL, 0, 0);
    List path = {0}, acts = {0};
    product_path(r, nr, at, NULL, 0, &path, &acts);
    int *ls = NEWN(int, path.n), *act = NEWN(int, path.n), n = 0;
    for (int i = 0; i < path.n; i++) {   /* without its finite stuttering */
        int s = pnodes[path.v[i]->u.i].state;
        if (n && ls[n - 1] == s) continue;
        ls[n] = s;
        act[n++] = (int)acts.v[i]->u.i;
    }
    print_violated(lasso_values(ls, n), n, n - 1);
    printf("Error: The following behavior constitutes a counter-example:\n\n");
    for (int i = 0; i < n; i++) print_live_state(i + 1, ls[i], i ? act[i] : -1, i ? ls[i - 1] : -1, ls[i + 1 < n ? i + 1 : i]);
    act[0] = -1;
    post_behavior(lasso_values(ls, n), act, n, 0, 0, 2);
}

/* What TLC evaluates of the properties on each initial state, before its
   invariants: the literals of each initial node of a tableau, up to a
   false one. */
static TFList *init_lits;
static int ninit_lits;

static void add_init_lits(TF **v, int n) {
    TFList l = {NEWN(TF *, n), 0};
    for (int i = 0; i < n; i++) if (!v[i]->action) l.v[l.n++] = v[i];
    init_lits = xrealloc(init_lits, sizeof(TFList) * (size_t)(ninit_lits + 1));
    init_lits[ninit_lits++] = l;
}

static void live_init_lits(void) {
    for (int p = 0; p < ntemporal_props; p++) {
        natoms = 0;
        neventualities = 0;
        ntnodes = 0;
        TF *neg = to_tf(temporal_props[p].expr, temporal_props[p].ctx, 1);
        if (!tf_tableau(neg)) continue;
        List init = {0};
        TFList todo = {0}, empty = {0};
        tfl_add(&todo, neg);
        expand(todo, empty, empty, &init);
        for (int i = 0; i < init.n; i++) {
            TNode *n = &tnodes[init.v[i]->u.i];
            add_init_lits(n->lits, n->nlits);
        }
    }
}

/* A node's literals come last first: TLC takes them in the formula's order. */
static void eval_init_lits(Value **st) {
    for (int i = 0; i < ninit_lits; i++)
        for (int j = init_lits[i].n - 1; j >= 0; j--) {
            TF *t = init_lits[i].v[j];
            if (holds_in(t->atom, t->c, st, NULL) == t->neg) break;
        }
}

/* TLC reports the first error there and goes on; a second ends the
   search. */
static void live_init(Value **st) {
    if (live_init_failed) { eval_init_lits(st); return; }
    EvalState saved = eval_save();
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        live_init_failed = error_status;
        eval_restore(saved);
        print_error_message();
        if (error_module != 1) {   /* as for Init: not for a standard module's operator */
            printf("While working on the initial state:\n");
            print_state(st);
            printf("\n");
        }
        return;
    }
    eval_init_lits(st);
    eval_restore(saved);
}

/* An error checking the temporal properties, reported as TLC reports it:
   TLC evaluates their predicates as it expands each state: the actions
   on each step and on stuttering, weak fairness's ENABLED among them,
   then ENABLED and, without a tableau,
   the other state predicates on the state, then a tableau's on each
   successor. It reports the first error then, as one in Next, with the
   behavior to the state and the counts of that moment. */
static int live_at;   /* the state live_eval is at; read after an error jumps back */

static void live_eval(void) {
    natoms = 0;
    neventualities = 0;
    static char *on_state;   /* each atom: of a property without a tableau */
    for (int p = 0; p < ntemporal_props; p++) {
        int from = natoms;
        int flat = !tf_tableau(to_tf(temporal_props[p].expr, temporal_props[p].ctx, 1));
        on_state = xrealloc(on_state, (size_t)natoms + 1);
        memset(on_state + from, flat, (size_t)(natoms - from));
    }
    for (live_at = 0; live_at < nstates; live_at++) {
        int s = live_at;
        StateRec *r = &states[s];
        for (int e = 0; e <= r->nedges; e++) {
            int t = e < r->nedges ? r->edges[2 * e] : s;   /* the last, stuttering */
            for (int i = 0; i < natoms; i++)
                if (atoms[i]->action) holds_in(atoms[i]->atom, atoms[i]->c, state_values(s), state_values(t));
            for (int i = 0; i < nfairs; i++) {   /* WF as TLC's action ~ENABLED A \/ A */
                if (!fairs[i].strong) holds_in(fairs[i].enabled, fairs[i].c, state_values(s), NULL);
                holds_in(fairs[i].step, fairs[i].c, state_values(s), state_values(t));
            }
        }
        for (int i = 0; i < natoms; i++)
            if (atoms[i]->atom->kind == K_ENABLED) holds_in(atoms[i]->atom, atoms[i]->c, state_values(s), NULL);
        for (int i = 0; i < nfairs; i++) holds_in(fairs[i].enabled, fairs[i].c, state_values(s), NULL);
        for (int i = 0; i < natoms; i++)
            if (!atoms[i]->action && atoms[i]->atom->kind != K_ENABLED && on_state[i])
                holds_in(atoms[i]->atom, atoms[i]->c, state_values(s), NULL);
        for (int e = 0; e <= r->nedges; e++)
            for (int i = 0; i < natoms; i++)
                if (!atoms[i]->action && atoms[i]->atom->kind != K_ENABLED && !on_state[i])
                    holds_in(atoms[i]->atom, atoms[i]->c, state_values(e < r->nedges ? r->edges[2 * e] : s), NULL);
    }
}

static int live_error(void) {
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        handler = NULL;
        printf("\n");
        if (eval_failure_status() == MANYAN_FAILURE_EVAL && error_module != 1) print_exception("java.lang.RuntimeException", ": ");
        else printf("Error: ");
        print_error_text();
        print_trace(live_at, NULL, 0);
        print_counts_after(live_at);
        return MANYAN_ERROR;
    }
    live_eval();
    /* Not found so: as it came. */
    handler = NULL;
    print_error_message();
    return MANYAN_FAILURE_EVAL;
}

static void collect_fairnesses(void) {
    nfairs = nfair_rest = 0;
    for (int i = 0; i < nfairness; i++) collect_fairness(fairness[i], root_ctx);
}

/* An empty cache for the natoms atoms on each state and step. */
static void atom_cache_reset(void) {
    size_t n = (size_t)nstates * (size_t)natoms;
    free(step_atoms);
    step_atoms = xmalloc(sizeof(size_t) * (size_t)(nstates + 1));
    for (int s = 0; s < nstates; s++) { step_atoms[s] = n; n += (size_t)(states[s].nedges + 1) * (size_t)natoms; }
    if (atom_cache) munmap(atom_cache, atom_cache_size);
    atom_cache = shared(atom_cache_size = n + 1);
}

static TF *live_setup(int p) {
    neventualities = 0;
    natoms = 0;
    ntnodes = 0;
    npnodes = 0;
    free(pnodes_of);
    pnodes_of = xcalloc((size_t)nstates, sizeof(PRefs));
    TF *neg = to_tf(temporal_props[p].expr, temporal_props[p].ctx, 1);
    for (int i = nfair_rest - 1; i >= 0; i--) neg = tf_new(TF_AND, to_tf(fair_rest[i], fair_rest_c[i], 0), neg);
    atom_cache_reset();
    return live_negated = neg;
}

/* Whether a temporal property fails on the state graph; if so, its
   counterexample is printed and the exit status returned. TLC stops
   first at the earliest finite counterexample (live_cut_violated). */
static int live_cut_violated(void) {
    free(decoded);
    decoded = xcalloc((size_t)nstates, sizeof(Value **));
    free(real_succ);
    real_succ = xcalloc((size_t)nstates, sizeof(Successors));
    int first = -1, at = -1;   /* the last set up is the first property, whose product the check takes on */
    for (int p = ntemporal_props - 1; p >= 0; p--) {
        int node, s = live_cut_at(live_setup(p), &node);
        if (s >= 0 && (first < 0 || s <= live_cut)) { first = p; live_cut = s; at = node; }
    }
    if (first < 0) return 0;
    if (first) live_cut_at(live_setup(first), &at);
    print_cut(at);
    return MANYAN_VIOLATION_SAFETY;
}

/* Where TLC checks the properties without a tableau, as it does when
   each disjunct of the disjunctive normal form of the fairness and the
   negated properties is a conjunction of <>[]X, []<>S and []<>A
   (Liveness.processLiveness): each disjunct is a possible error model,
   searched in turn on the state graph (LiveWorker). */
typedef struct { TFList ea, aes, aea, tf; uint64_t s_bits, ea_bits, aea_bits; } Pem;   /* <>[]X, []<>S, []<>A, the rest, for a tableau; bits of conds */
typedef struct { TFList *v; int n; } Dnf;     /* n negative: too large */

static Dnf dnf_one(TF *f) {
    Dnf d = {NEWN(TFList, 1), 1};
    d.v[0].v = NEWN(TF *, 1);
    d.v[0].v[0] = f;
    d.v[0].n = 1;
    return d;
}

/* As TLC's toDNF: a conjunction's disjuncts are its conjuncts', crossed,
   the first varying slowest; a disjunction's are its disjuncts', those
   []<>X merged into one []<>(X1 \/ X2 ...) at the end. */
static Dnf tf_dnf(TF *f) {
    if (f->op != TF_AND && f->op != TF_OR) return dnf_one(f);
    Dnf a = tf_dnf(f->a), b = tf_dnf(f->b), d = {0};
    if (a.n < 0 || b.n < 0 || (long)a.n * b.n > 4096) return (Dnf){NULL, -1};
    if (f->op == TF_AND) {
        d.v = NEWN(TFList, a.n * b.n);
        for (int i = 0; i < a.n; i++)
            for (int j = 0; j < b.n; j++) {
                TFList *l = &d.v[d.n++];
                l->v = NEWN(TF *, a.v[i].n + b.v[j].n);
                memcpy(l->v, a.v[i].v, sizeof(TF *) * (size_t)a.v[i].n);
                memcpy(l->v + a.v[i].n, b.v[j].v, sizeof(TF *) * (size_t)b.v[j].n);
                l->n = a.v[i].n + b.v[j].n;
            }
        return d;
    }
    TF *ae = NULL;
    d.v = NEWN(TFList, a.n + b.n + 1);
    for (int i = 0; i < a.n + b.n; i++) {
        TFList x = i < a.n ? a.v[i] : b.v[i - a.n];
        if (x.n == 1 && x.v[0]->op == TF_ALWAYS && x.v[0]->a->op == TF_EVENTUALLY)
            ae = ae ? tf_new(TF_OR, ae, x.v[0]->a->a) : x.v[0]->a->a;
        else d.v[d.n++] = x;
    }
    if (ae) d.v[d.n++] = dnf_one(tf_new(TF_ALWAYS, tf_new(TF_EVENTUALLY, ae, NULL), NULL)).v[0];
    return d;
}

/* The error model of a disjunct, as TLC's classifyExpr; 0 if a conjunct
   for the tableau has an action, which TLC's tableau cannot take. */
static int pem_of(TFList x, Pem *m) {
    *m = (Pem){0};
    for (int i = 0; i < x.n; i++) {
        TF *t = x.v[i];
        if (t->op == TF_EVENTUALLY && t->a->op == TF_ALWAYS && !tf_has(t->a->a, 1)) tfl_add(&m->ea, t->a->a);
        else if (t->op == TF_ALWAYS && t->a->op == TF_EVENTUALLY && !tf_has(t->a->a, 1))
            tfl_add(tf_has(t->a->a, 0) ? &m->aea : &m->aes, t->a->a);
        else if (tf_has(t, 0)) return 0;
        else tfl_add(&m->tf, t);
    }
    return 1;
}

/* f, of no temporal operator, on state s, or on its step e to `to`. */
static int pem_holds(TF *f, int s, int e, int to) {
    switch (f->op) {
    case TF_TRUE: return 1;
    case TF_FALSE: return 0;
    case TF_AND: return pem_holds(f->a, s, e, to) && pem_holds(f->b, s, e, to);
    case TF_OR: return pem_holds(f->a, s, e, to) || pem_holds(f->b, s, e, to);
    default: return f->action ? atom_holds_edge(f, s, e, to) : atom_holds_on(f, s, NULL);
    }
}

static Pem *pem;          /* the error model searched */
static TFList promises;   /* the <>F of its tableau */
static char *pem_in;      /* by node: in the component */

static void tf_promises(TF *f) {
    if (!f) return;
    if (f->op == TF_EVENTUALLY) tfl_add(&promises, f);
    tf_promises(f->a);
    tf_promises(f->b);
}

static int pem_fulfils(int p, int i) { return !tnode_defers(pnodes[p].tnode, promises.v[i]->index); }

/* Whether each promise is fulfilled in a node of a component. */
static int pem_promised(int *nodes, int n) {
    for (int i = 0; i < promises.n; i++) {
        int ok = 0;
        for (int j = 0; j < n && !ok; j++) ok = pem_fulfils(nodes[j], i);
        if (!ok) return 0;
    }
    return 1;
}

/* Whether the edge k of node p holds pem's <>[] conditions, and, with a,
   the action a. */
static int pem_step(int p, int k, TF *a) {
    int s = pnodes[p].state, to = pnodes[pnodes[p].succ[k]].state, e = pnodes[p].edge[k];
    for (int i = 0; i < pem->ea.n; i++) if (!pem_holds(pem->ea.v[i], s, e, to)) return 0;
    return !a || pem_holds(a, s, e, to);
}

/* TLC's checkComponent: a component of one node needs a step to itself;
   each promise is fulfilled in a node, each []<>S holds in one, each
   []<>A on an edge inside. */
static int pem_accept(int *nodes, int n) {
    if (n == 1) {
        int p = nodes[0], k = 0;
        while (k < pnodes[p].nsucc && pnodes[p].succ[k] != p) k++;
        if (k == pnodes[p].nsucc || !pem_step(p, k, NULL)) return 0;
    }
    if (!pem_promised(nodes, n)) return 0;
    for (int i = 0; i < pem->aes.n; i++) {
        int ok = 0;
        for (int j = 0; j < n && !ok; j++) ok = pem_holds(pem->aes.v[i], pnodes[nodes[j]].state, -1, -1);
        if (!ok) return 0;
    }
    for (int i = 0; i < pem->aea.n; i++) {
        int ok = 0;
        for (int j = 0; j < n && !ok; j++)
            for (int k = 0; k < pnodes[nodes[j]].nsucc && !ok; k++)
                ok = pem_in[pnodes[nodes[j]].succ[k]] && pem_step(nodes[j], k, pem->aea.v[i]);
        if (!ok) return 0;
    }
    return 1;
}

/* TLC's checkSccs: Tarjan's from each initial node, by the edges that
   hold the <>[] conditions, the last first; the target of another edge
   not yet seen is a root after them. Returns the root of the first
   accepted component, its nodes marked in pem_in and in *com. */
static int pem_sccs(int *roots, int nroots, Ints *com, int (*accept)(int *, int)) {
    int nq = nroots, *queue = xmalloc(sizeof(int) * (size_t)(nroots + 1)), qcap = nroots + 1;
    memcpy(queue, roots, sizeof(int) * (size_t)nroots);
    for (int p = 0; p < npnodes; p++) pnodes[p].index = -1, pnodes[p].onstack = 0;
    int *stack = xmalloc(sizeof(int) * (size_t)npnodes), *cstack = xmalloc(sizeof(int) * (size_t)npnodes);
    int *cedge = xmalloc(sizeof(int) * (size_t)npnodes), index = 0, sp = 0, found = -1;
    for (int q = 0; q < nq && found < 0; q++) {
        if (pnodes[queue[q]].index >= 0) continue;
        int cp = 0, w = queue[q];
        for (;;) {
            if (w >= 0) {   /* visit w */
                pnodes[w].index = pnodes[w].low = index++;
                stack[sp++] = w;
                pnodes[w].onstack = 1;
                cstack[cp] = w, cedge[cp++] = 0;
                for (int k = 0; k < pnodes[w].nsucc; k++) {
                    int x = pnodes[w].succ[k];
                    if (pnodes[x].index >= 0 || pem_step(w, k, NULL)) continue;
                    if (nq == qcap) queue = xrealloc(queue, sizeof(int) * (size_t)(qcap *= 2));
                    queue[nq++] = x;
                }
                w = -1;
            }
            if (!cp || found >= 0) break;
            int v = cstack[cp - 1], ns = pnodes[v].nsucc;
            if (cedge[cp - 1] < ns) {
                int k = ns - 1 - cedge[cp - 1]++, x = pnodes[v].succ[k];
                if (!pem_step(v, k, NULL)) continue;
                if (pnodes[x].index < 0) w = x;
                else if (pnodes[x].onstack && pnodes[x].index < pnodes[v].low) pnodes[v].low = pnodes[x].index;
                continue;
            }
            if (--cp > 0 && pnodes[v].low < pnodes[cstack[cp - 1]].low) pnodes[cstack[cp - 1]].low = pnodes[v].low;
            if (pnodes[v].low != pnodes[v].index) continue;
            int start = sp;
            do start--; while (stack[start] != v);
            for (int i = start; i < sp; i++) pnodes[stack[i]].onstack = 0, pem_in[stack[i]] = 1;
            if (accept(stack + start, sp - start)) {
                found = v;
                for (int i = start; i < sp; i++) PUSH(com->v, com->n, stack[i]);
            } else for (int i = start; i < sp; i++) pem_in[stack[i]] = 0;
            sp = start;
        }
    }
    free(queue); free(stack); free(cstack); free(cedge);
    return found;
}

/* The error models of a group the workers search, each to whether a
   component accepts it: 2 one does, 1 none, 0 not known (the search
   failed, printed or drew in the worker). The search goes on in order
   from them, searching again only those not found to be accepted by none. */
static int *pem_job, pem_njob, pem_nroots, *pem_roots;
static Pem *pem_models;
static signed char *pem_found;

/* Each search takes the <>[] conditions of its error model on every edge
   of the product: the workers evaluate them first, on the nodes of the
   states [lo, hi), filling the atom cache. */
static void worker_steps(int lo, int hi) {
    for (int s = lo; s < hi; s++) {
        EvalState saved = eval_save();
        ErrorState er = error_save();
        sigjmp_buf here;
        handler = &here;
        if (!sigsetjmp(here, 0))
            for (int i = 0; i < pnodes_of[s].n * pem_njob; i++) {
                int p = pnodes_of[s].v[i / pem_njob].node;
                pem = &pem_models[pem_job[i % pem_njob]];
                for (int k = 0; k < pnodes[p].nsucc; k++) pem_step(p, k, NULL);
            }
        eval_restore(saved);
        error_restore(&er);
    }
}

static void worker_pems(int lo, int hi) {
    for (int i = lo; i < hi; i++) {
        EvalState saved = eval_save();
        ErrorState er = error_save();
        sigjmp_buf here;
        handler = &here;
        Ints com = {0};
        if (!sigsetjmp(here, 0)) {
            pem = &pem_models[pem_job[i]];
            pem_found[i] = pem_sccs(pem_roots, pem_nroots, &com, pem_accept) >= 0 ? 2 : 1;
        }
        eval_restore(saved);
        error_restore(&er);
        memset(pem_in, 0, (size_t)npnodes + 1);
    }
}

/* What each component of the whole product offers an error model, to
   skip the search of one that none can accept: a component it accepts
   lies in one of them. Bits of the []<>S holding in a node, and of the
   <>[] and []<>A conditions holding on each edge inside; the components
   that fulfil the promises and have an edge inside. */
static TFList conds_s, conds_e;   /* the bits, if 64 or fewer each */
typedef struct { uint64_t states, *edges; int n; } Offer;
static Offer *offers;
static int noffers;

static uint64_t cond_bits(TFList conds, TFList of) {
    uint64_t b = 0;
    for (int i = 0; i < of.n; i++)
        for (int j = 0; j < conds.n; j++) if (conds.v[j] == of.v[i]) b |= 1ull << j;
    return b;
}

/* The components that fulfil the promises, in order: their nodes, each
   node's component (-1 if none), and the evaluations of the bits in them. */
static int *pem_comp;
static Ints comp_nodes, comp_at;   /* component c's nodes from comp_at.v[c] to comp_at.v[c + 1] */
static long npem_evals;

static int pem_number(int *nodes, int n) {
    if (!pem_promised(nodes, n)) return 0;
    PUSH(comp_at.v, comp_at.n, comp_nodes.n);
    for (int j = 0; j < n; j++) {
        int p = nodes[j];
        pem_comp[p] = comp_at.n - 1;
        PUSH(comp_nodes.v, comp_nodes.n, p);
        npem_evals += conds_s.n;
        for (int k = 0; k < pnodes[p].nsucc; k++) npem_evals += pem_in[pnodes[p].succ[k]] ? conds_e.n : 0;
    }
    return 0;
}

static void pem_offer(int *nodes, int n) {
    Offer o = {0};
    for (int j = 0; j < n; j++) {
        int p = nodes[j], s = pnodes[p].state;
        for (int b = 0; b < conds_s.n; b++) if (pem_holds(conds_s.v[b], s, -1, -1)) o.states |= 1ull << b;
        for (int k = 0; k < pnodes[p].nsucc; k++) {
            int w = pnodes[p].succ[k], seen = 0;
            if (pem_comp[w] != pem_comp[p]) continue;
            uint64_t x = 0;
            for (int b = 0; b < conds_e.n; b++)
                if (pem_holds(conds_e.v[b], s, pnodes[p].edge[k], pnodes[w].state)) x |= 1ull << b;
            for (int i = 0; i < o.n && !seen; i++) seen = o.edges[i] == x;
            if (!seen) PUSH(o.edges, o.n, x);
        }
    }
    if (!o.n) return;
    qsort(o.edges, (size_t)o.n, sizeof(uint64_t), cmp_u64);
    for (int i = 0; i < noffers; i++)   /* one of each */
        if (offers[i].states == o.states && offers[i].n == o.n && !memcmp(offers[i].edges, o.edges, sizeof(uint64_t) * (size_t)o.n)) return;
    PUSH(offers, noffers, o);
}

/* With workers, the bits are evaluated first by the workers, on the nodes
   of the states [lo, hi), filling the atom cache, if there are enough of
   them to pay for forking. */
#define OFFER_FORK 100000   /* evaluations; a fork costs a few milliseconds */

static void worker_offers(int lo, int hi) {
    for (int s = lo; s < hi; s++) {
        EvalState saved = eval_save();
        ErrorState er = error_save();
        sigjmp_buf here;
        handler = &here;
        if (!sigsetjmp(here, 0))
            for (int i = 0; i < pnodes_of[s].n; i++) {
                int p = pnodes_of[s].v[i].node;
                if (pem_comp[p] < 0) continue;
                for (int b = 0; b < conds_s.n; b++) pem_holds(conds_s.v[b], s, -1, -1);
                for (int k = 0; k < pnodes[p].nsucc; k++) {
                    int w = pnodes[p].succ[k];
                    if (pem_comp[w] != pem_comp[p]) continue;
                    for (int b = 0; b < conds_e.n; b++) pem_holds(conds_e.v[b], s, pnodes[p].edge[k], pnodes[w].state);
                }
            }
        eval_restore(saved);
        error_restore(&er);
    }
}

static int offer_has(Offer *o, uint64_t need) {
    for (int i = 0; i < o->n; i++) if ((o->edges[i] & need) == need) return 1;
    return 0;
}

static int pem_possible(Pem *m) {
    for (int i = 0; i < noffers; i++) {
        Offer *o = &offers[i];
        int ok = (o->states & m->s_bits) == m->s_bits && offer_has(o, m->ea_bits);
        for (int b = 0; b < 64 && ok; b++)
            if (m->aea_bits >> b & 1) ok = offer_has(o, m->ea_bits | 1ull << b);
        if (ok) return 1;
    }
    return 0;
}

/* TLC's dfsPostFix: from the root, a walk through the component that
   takes the first edge meeting a []<>A not met yet, else, once a []<>S or
   promise is met, the last edge it may take, else the last one to a node not seen
   since the last condition met, backing up where there is none. The walk
   before the node it ends at is in *walk. */
static int pem_walk(int root, Ints *walk) {
    int na = pem->aes.n + pem->aea.n, cnt = na + promises.n, cur = root;
    char *seen = xcalloc((size_t)npnodes, 1), *met = xcalloc((size_t)cnt + 1, 1);
    seen[root] = 1;
    while (cnt > 0) {
        int cnt0 = cnt;
        for (;;) {
            for (int i = 0; i < pem->aes.n; i++)
                if (!met[i] && pem_holds(pem->aes.v[i], pnodes[cur].state, -1, -1)) met[i] = 1, cnt--;
            for (int i = 0; i < promises.n; i++)
                if (!met[na + i] && pem_fulfils(cur, i)) met[na + i] = 1, cnt--;
            if (cnt <= 0) break;
            int next1 = -1, next2 = -1, cnt1 = cnt, moved = 0;
            for (int k = 0; k < pnodes[cur].nsucc && !moved; k++) {
                int w = pnodes[cur].succ[k];
                if (!pem_in[w] || !pem_step(cur, k, NULL)) continue;
                next1 = w;
                for (int i = 0; i < pem->aea.n; i++)
                    if (!met[pem->aes.n + i] && pem_step(cur, k, pem->aea.v[i])) met[pem->aes.n + i] = 1, cnt--;
                if (cnt < cnt1) moved = 1;
                else if (!seen[w]) next2 = w;
            }
            if (moved || (cnt < cnt0 && next1 >= 0)) {
                PUSH(walk->v, walk->n, cur);
                cur = next1;
                memset(seen, 0, (size_t)npnodes);
                break;
            }
            while (next2 < 0 && walk->n > 0) {   /* back up */
                cur = walk->v[--walk->n];
                for (int k = 0; k < pnodes[cur].nsucc && next2 < 0; k++)
                    if (pem_in[pnodes[cur].succ[k]] && !seen[pnodes[cur].succ[k]]) next2 = pnodes[cur].succ[k];
            }
            if (next2 < 0) { cnt = 0; break; }
            PUSH(walk->v, walk->n, cur);
            cur = next2;
            seen[cur] = 1;
        }
    }
    free(seen); free(met);
    return cur;
}

/* TLC's bfsPostFix: the shortest way in the component, by the edges that
   hold the <>[] conditions, from `from` to an edge back to the root, its
   nodes from the last to `from` added to post. */
static void pem_back(int from, int root, Ints *post) {
    int *prev = xmalloc(sizeof(int) * (size_t)npnodes), *queue = xmalloc(sizeof(int) * (size_t)npnodes), qh = 0, qt = 0;
    for (int p = 0; p < npnodes; p++) prev[p] = -2;
    prev[from] = -1;
    queue[qt++] = from;
    while (qh < qt) {
        int v = queue[qh++];
        for (int k = 0; k < pnodes[v].nsucc; k++) {
            int w = pnodes[v].succ[k];
            if (w == v || !pem_step(v, k, NULL)) continue;
            if (w == root) {
                for (int x = v; x >= 0; x = prev[x]) PUSH(post->v, post->n, x);
                free(prev); free(queue);
                return;
            }
            if (pem_in[w] && prev[w] == -2) prev[w] = v, queue[qt++] = w;
        }
    }
    free(prev); free(queue);
}

/* TLC's printTrace: the shortest path to the root, then the cycle of the
   walk and the way back, each state once in a row; the last state, if
   the root's, stutters. */
static void pem_print(int root, int *roots, int nroots) {
    List path = {0}, acts = {0};
    product_path(roots, nroots, root, NULL, 0, &path, &acts);
    Ints walk = {0}, post = {0};
    int cur = pem_walk(root, &walk);
    if (cur != root) pem_back(cur, root, &post);
    for (int i = walk.n - 1; i >= 0; i--)
        if (!post.n || post.v[post.n - 1] != walk.v[i]) PUSH(post.v, post.n, walk.v[i]);
    if (post.n && post.v[post.n - 1] == root) post.n--;
    int n = path.n + post.n, *ls = NEWN(int, n + 1), *la = NEWN(int, n + 1), prev = -1, k = 0, at = 0;
    for (int i = 0; i < n; i++) {
        int p = i < path.n ? (int)path.v[i]->u.i : post.v[post.n - 1 - (i - path.n)];
        int act = !i ? -1 : i < path.n ? (int)acts.v[i]->u.i : edge_act(prev, p);
        prev = p;
        if (k && ls[k - 1] == pnodes[p].state) continue;   /* only its tableau node changes */
        ls[k] = pnodes[p].state;
        la[k++] = act;
        if (i < path.n) at = k - 1;
    }
    if (ls[k - 1] == pnodes[root].state) print_lasso(ls, la, k, -1, la[k - 1], k - 1);
    else print_lasso(ls, la, k, at, edge_act(prev, root), at);
}

/* The error models of the group of pems[i], those sharing its tableau,
   searched on its product with the state graph: 1 if one is accepted, its
   counterexample printed but in a worker, 0 if none is. With workers, and
   not in one, the workers fill what the searches take and search the
   error models first. */
static TFList pem_filled;   /* the <>[] actions evaluated on every edge */

static int pem_group(Pem *pems, int n, int i, int prune) {
    int forks = nworkers > 1 && !in_worker;
    TF *tf = tf_new(TF_TRUE, NULL, NULL);
    for (int j = 0; j < pems[i].tf.n; j++) tf = tf_new(TF_AND, tf, pems[i].tf.v[j]);
    promises = (TFList){0};
    tf_promises(tf);
    ntnodes = npnodes = 0;
    free(pnodes_of);
    pnodes_of = xcalloc((size_t)nstates, sizeof(PRefs));
    int *roots, nroots = live_roots(tf, &roots);
    live_build(tf, 0, NULL);
    free(pem_in);
    pem_in = xcalloc((size_t)npnodes + 1, 1);
    int njob = 0;
    pem_job = NEWN(int, n);
    for (int j = i; j < n; j++)
        if (tfl_same(pems[j].tf.v, pems[j].tf.n, pems[i].tf.v, pems[i].tf.n)) pem_job[njob++] = j;
    int offered = prune && njob > 8;   /* the pass costs a few searches */
    if (offered) {
        Pem all = {0};
        pem = &all;
        pem_comp = NEWN(int, npnodes);
        for (int p = 0; p < npnodes; p++) pem_comp[p] = -1;
        comp_nodes = comp_at = (Ints){0};
        npem_evals = 0;
        pem_sccs(roots, nroots, NULL, pem_number);
        PUSH(comp_at.v, comp_at.n, comp_nodes.n);
        if (forks && npem_evals > OFFER_FORK) {
            stop_workers();   /* to fork with this group's product */
            run_level(0, nstates, BATCH, 0, OFFERS);
        }
        noffers = 0;
        for (int c = 0; c + 1 < comp_at.n; c++) pem_offer(comp_nodes.v + comp_at.v[c], comp_at.v[c + 1] - comp_at.v[c]);
        int k = 0;
        for (int j = 0; j < njob; j++) if (pem_possible(&pems[pem_job[j]])) pem_job[k++] = pem_job[j];
        njob = k;
    }
    int nfilled = pem_filled.n;   /* the workers fill the <>[] actions neither the offers nor a search took */
    for (int k = 0; k < njob && !offered; k++)
        for (int j = 0; j < pems[pem_job[k]].ea.n; j++)
            if (tf_has(pems[pem_job[k]].ea.v[j], 0)) tfl_add(&pem_filled, pems[pem_job[k]].ea.v[j]);
    signed char *found = NULL;
    if (forks && njob > 1) {
        pem_found = found = shared((size_t)njob);
        pem_models = pems, pem_njob = njob, pem_roots = roots, pem_nroots = nroots;
        stop_workers();   /* to fork with this group's product */
        if (pem_filled.n > nfilled) run_level(0, nstates, BATCH, 0, STEPS);
        run_level(0, njob, 1, 0, PEMS);
    }
    int violated = 0;
    for (int k = 0; k < njob && !violated; k++) {
        if (found && found[k] == 1) continue;
        pem = &pems[pem_job[k]];
        Ints com = {0};
        int root = pem_sccs(roots, nroots, &com, pem_accept);
        if (root >= 0) {
            violated = 1;
            if (!in_worker) pem_print(root, roots, nroots);
        }
    }
    if (found) munmap(found, (size_t)njob);
    return violated;
}

/* The groups the workers check, each to whether one of its error models
   is accepted: 2 one is, 1 none, 0 not known; the search goes on in order
   from them, as from pem_found. */
static Pem *group_pems;
static int *group_first, group_npems, group_prune;
static signed char *group_found;

static void worker_groups(int lo, int hi) {
    for (int g = lo; g < hi; g++) {
        EvalState saved = eval_save();
        ErrorState er = error_save();
        sigjmp_buf here;
        handler = &here;
        if (!sigsetjmp(here, 0)) group_found[g] = pem_group(group_pems, group_npems, group_first[g], group_prune) ? 2 : 1;
        eval_restore(saved);
        error_restore(&er);
    }
}

/* 1 if a property is violated, its counterexample printed; 0 if none is;
   -1 if TLC checks them otherwise. The disjuncts sharing a tableau are
   TLC's order of solution: their error models are searched in turn on its
   product with the state graph, a group at a time. */
static int pem_violated(void) {
    if (sim_n || nsymmetry || view_expr || !ntemporal_props) return -1;
    free(decoded);
    decoded = xcalloc((size_t)nstates, sizeof(Value **));
    neventualities = natoms = 0;
    TF *f = NULL, *neg = NULL;
    for (int i = 0; i < nfairness; i++) {
        TF *t = to_tf(fairness[i], root_ctx, 0);
        f = f ? tf_new(TF_AND, f, t) : t;
    }
    for (int p = 0; p < ntemporal_props; p++) {
        TF *t = to_tf(temporal_props[p].expr, temporal_props[p].ctx, 1);
        neg = neg ? tf_new(TF_OR, neg, t) : t;
    }
    f = f ? tf_new(TF_AND, f, neg) : neg;
    if (f->op == TF_FALSE) return 0;
    Dnf d = tf_dnf(f);
    if (d.n < 0) return -1;
    Pem *pems = NEWN(Pem, d.n + 1);
    for (int i = 0; i < d.n; i++) if (!pem_of(d.v[i], &pems[i])) return -1;
    conds_s = conds_e = (TFList){0};
    for (int i = 0; i < d.n; i++) {
        for (int j = 0; j < pems[i].aes.n; j++) tfl_add(&conds_s, pems[i].aes.v[j]);
        for (int j = 0; j < pems[i].ea.n; j++) tfl_add(&conds_e, pems[i].ea.v[j]);
        for (int j = 0; j < pems[i].aea.n; j++) tfl_add(&conds_e, pems[i].aea.v[j]);
    }
    int prune = conds_s.n <= 64 && conds_e.n <= 64;
    for (int i = 0; i < d.n && prune; i++) {
        pems[i].s_bits = cond_bits(conds_s, pems[i].aes);
        pems[i].ea_bits = cond_bits(conds_e, pems[i].ea);
        pems[i].aea_bits = cond_bits(conds_e, pems[i].aea);
    }
    atom_cache_reset();
    live_negated = f;
    pem_filled = (TFList){0};
    int *first = NEWN(int, d.n), ngroups = 0;   /* each group's first error model */
    for (int i = 0; i < d.n; i++) {
        int k = 0;
        while (k < i && !tfl_same(pems[k].tf.v, pems[k].tf.n, pems[i].tf.v, pems[i].tf.n)) k++;
        if (k == i) first[ngroups++] = i;
    }
    signed char *found = NULL;
    if (nworkers > 1 && ngroups > 2) {   /* two keep two workers busy, where each group's search keeps them all */
        group_found = found = shared((size_t)ngroups);
        group_pems = pems, group_first = first, group_npems = d.n, group_prune = prune;
        stop_workers();   /* to fork with the error models */
        run_level(0, ngroups, 1, 0, GROUPS);
    }
    int violated = 0;
    for (int g = 0; g < ngroups && !violated; g++)
        if (!found || found[g] != 1) violated = pem_group(pems, d.n, first[g], prune);
    if (found) munmap(found, (size_t)ngroups);
    return violated;
}

static int live_violated(void) {
    int cut = live_cut_violated();
    if (cut) return cut;
    int pem = pem_violated();
    if (pem >= 0) return pem ? MANYAN_VIOLATION_LIVENESS : 0;
    for (int p = 0; p < ntemporal_props; p++)
        if (check_property(live_setup(p))) return MANYAN_VIOLATION_LIVENESS;
    return 0;
}

/* As TLC does before it checks a model: a property that is no formula it
   can check, such as \EE x : F, is an error. Other errors are left for
   the check. */
/* Whether a formula is FALSE whatever the behavior, its constants alone
   deciding it. */
static int tf_false(TF *t) {
    switch (t->op) {
    case TF_FALSE: return 1;
    case TF_AND: return tf_false(t->a) || tf_false(t->b);
    case TF_OR: return tf_false(t->a) && tf_false(t->b);
    case TF_EVENTUALLY: return tf_false(t->a);   /* TLC does not fold []FALSE */
    default: return 0;
    }
}

/* The tableau of ~e, or NULL if building it fails. */
static TF *negation(Check *p) {
    EvalState s = eval_save();
    sigjmp_buf here;
    handler = &here;
    TF *volatile negated = NULL;
    if (!sigsetjmp(here, 0)) negated = to_tf(p->expr, p->ctx, 1);
    eval_restore(s);
    return negated;
}

/* simulating: TLC finds no tautology then. */
/* Whether a conjunct of the negation, in TLC's disjunctive normal form,
   is neither <>[]A nor []<>A with A no temporal formula, but has an
   action: TLC's tableau cannot take one. */
static int tf_wrong_form(TF *f) {
    if (f->op == TF_AND || f->op == TF_OR) return tf_wrong_form(f->a) || tf_wrong_form(f->b);
    if ((f->op == TF_EVENTUALLY && f->a->op == TF_ALWAYS) || (f->op == TF_ALWAYS && f->a->op == TF_EVENTUALLY))
        if (!tf_has(f->a->a, 1)) return 0;
    return tf_has(f, 0);
}

/* The number of disjuncts of f in TLC's disjunctive normal form, which
   does not reach under temporal operators. */
static double tf_dnf_size(TF *f) {
    if (f->op == TF_OR) return tf_dnf_size(f->a) + tf_dnf_size(f->b);
    if (f->op == TF_AND) return tf_dnf_size(f->a) * tf_dnf_size(f->b);
    return 1;
}

/* TLC's normal form of the fairness, each SF two disjuncts (a WF is one,
   []<>(~ENABLED <<A>>_v \/ <<A>>_v)), and the
   negated properties' disjunction: its size is a Java int. An error in
   the fairness is left for the check. */
static int dnf_too_large(TF **negated) {
    double size = 0;
    for (int p = 0; p < ntemporal_props; p++) size += tf_dnf_size(negated[p]);
    EvalState s = eval_save();
    sigjmp_buf here;
    handler = &here;
    if (!sigsetjmp(here, 0)) collect_fairnesses();
    eval_restore(s);
    for (int i = 0; i < nfairs; i++) size *= 1 + fairs[i].strong;
    nfairs = nfair_rest = 0;
    return size > INT32_MAX;
}

static int check_temporal_forms(int simulating) {
    int temporal = 0, unsatisfiable = 0;
    TF **negated = NEWN(TF *, ntemporal_props + 1);
    for (int p = 0; p < ntemporal_props; p++) {
        negated[p] = negation(&temporal_props[p]);
        if (!negated[p]) {   /* TLC fails building its tableau, evaluating its constants */
            report_exception(0);
            return MANYAN_ERROR;
        }
    }
    if (ntemporal_props && dnf_too_large(negated)) {
        printf("Error: TLC cannot handle the temporal formula because it exceeds the maximum supported size in disjunctive normal form.\n");
        return MANYAN_ERROR;
    }
    for (int p = 0; p < ntemporal_props; p++) {
        if (tf_wrong_form(negated[p])) {
            printf("Error: Temporal formulas containing actions must be of forms <>[]A or []<>A.\n");
            return MANYAN_ERROR;
        }
        if (level_in(temporal_props[p].expr, temporal_props[p].ctx) == 3) {   /* a predicate on the initial states is no tautology */
            temporal++;
            unsatisfiable += tf_false(negated[p]);
        }
    }
    if (temporal && unsatisfiable == temporal && !simulating) {
        printf("Error: Temporal formula is a tautology (its negation is unsatisfiable).\n");
        return MANYAN_FAILURE_LIVENESS_EVAL;
    }
    return 0;
}

/* ---------------------------------------------------------------- driver */

/* The literal TLC fails on first as it processes its constants: the
   definitions of a module, its inner modules, its assumptions, its
   theorems (§11.3). */
static Expr *odd_literal(Module *m) {
    if (m->odd[0]) return m->odd[0];
    for (int i = 0; i < m->nnested; i++) {
        Expr *e = odd_literal(m->nested[i]);
        if (e) return e;
    }
    return m->odd[1] ? m->odd[1] : m->odd[2];
}

/* The training run of a profile-guided build checks no behaviors
   symbolically: what follows takes no profile, and is optimized as if
   built without one, as -fprofile-partial-training has GCC do. */
#ifdef __clang__
#pragma clang attribute push (__attribute__((no_profile_instrument_function)), apply_to = function)
#endif

/* ---------------------------------------------------------------- solver */

/* -symbolic checks behaviors of up to -length steps without enumerating
   states, as Apalache does: it unrolls Init and Next into a formula, one
   step after another, and asks a solver whether a behavior that far
   violates an invariant or cannot go on. The solver is a CDCL SAT solver:
   two watched literals with a blocker each, VSIDS, first-UIP learning,
   learned clauses kept by their glue (the levels they span, as Glucose
   keeps them), Luby restarts, and assumptions, so each question about the
   unrolled formula keeps what the last one learned. A literal is
   2v + negated; variable 0 is true. */
typedef struct { int n, learnt, glue; float act; int lits[]; } Clause;
typedef struct { Clause **c; int n, cap; } Clauses;
typedef struct { Clause *c; int blocker; } Watch;   /* blocker: a literal of c that, true, satisfies it */
typedef struct { Watch *w; int n, cap; } Watches;

#define L_TRUE 0
#define L_FALSE 1

static struct {
    int nvars, cap;
    signed char *val;        /* per literal: 1 true, 0 false, -1 unassigned */
    int *level;
    Clause **reason;
    double *act, var_inc, cla_inc, max_learnts;
    unsigned char *phase, *seen, *model;
    int *trail, ntrail, qhead, *lim, nlim;
    Watches *watch;          /* per literal: the clauses watching it, visited when it becomes false */
    Clauses clauses, learnts;
    int *heap, nheap, *at;   /* unassigned variables by activity; at: a variable's index, -1 if out */
    int *buf, *buf2, capbuf;
    long *stamp, nconflicts;   /* per level: the conflict that last counted it in a glue */
    int glue;                  /* the last learned clause's */
    int ok;
} sat;

static void clauses_push(Clauses *v, Clause *c) {
    if (v->n == v->cap) v->c = xrealloc(v->c, sizeof(Clause *) * (size_t)(v->cap = v->cap ? 2 * v->cap : 4));
    v->c[v->n++] = c;
}

static int heap_before(int a, int b) { return sat.act[a] > sat.act[b]; }
static void heap_put(int i, int v) { sat.heap[i] = v; sat.at[v] = i; }

static void heap_up(int i) {
    int v = sat.heap[i];
    for (; i > 0 && heap_before(v, sat.heap[(i - 1) / 2]); i = (i - 1) / 2) heap_put(i, sat.heap[(i - 1) / 2]);
    heap_put(i, v);
}

static void heap_down(int i) {
    int v = sat.heap[i];
    for (int c; (c = 2 * i + 1) < sat.nheap; i = c) {
        if (c + 1 < sat.nheap && heap_before(sat.heap[c + 1], sat.heap[c])) c++;
        if (!heap_before(sat.heap[c], v)) break;
        heap_put(i, sat.heap[c]);
    }
    heap_put(i, v);
}

static void heap_add(int v) {
    if (sat.at[v] >= 0) return;
    heap_put(sat.nheap++, v);
    heap_up(sat.nheap - 1);
}

static int heap_pop(void) {
    int v = sat.heap[0];
    sat.at[v] = -1;
    if (--sat.nheap) { heap_put(0, sat.heap[sat.nheap]); heap_down(0); }
    return v;
}

static int sat_var(void) {
    int v = sat.nvars++;
    if (v == sat.cap) {
        size_t cap = (size_t)(sat.cap = sat.cap ? 2 * sat.cap : 1 << 12);
        sat.val = xrealloc(sat.val, 2 * cap);
        sat.level = xrealloc(sat.level, sizeof(int) * cap);
        sat.reason = xrealloc(sat.reason, sizeof(Clause *) * cap);
        sat.act = xrealloc(sat.act, sizeof(double) * cap);
        sat.phase = xrealloc(sat.phase, cap);
        sat.seen = xrealloc(sat.seen, cap);
        sat.model = xrealloc(sat.model, cap);
        sat.trail = xrealloc(sat.trail, sizeof(int) * cap);
        sat.lim = xrealloc(sat.lim, sizeof(int) * 2 * cap);   /* a level per variable and per assumption */
        sat.stamp = xrealloc(sat.stamp, sizeof(long) * (2 * cap + 1));
        memset(sat.stamp + 2 * v, 0, sizeof(long) * (2 * cap + 1 - 2 * (size_t)v));
        sat.heap = xrealloc(sat.heap, sizeof(int) * cap);
        sat.at = xrealloc(sat.at, sizeof(int) * cap);
        sat.watch = xrealloc(sat.watch, sizeof(Watches) * 2 * cap);
        memset(sat.watch + 2 * v, 0, sizeof(Watches) * (2 * cap - 2 * (size_t)v));
    }
    sat.val[2 * v] = sat.val[2 * v + 1] = -1;
    sat.level[v] = 0;
    sat.reason[v] = NULL;
    sat.act[v] = 0;
    sat.phase[v] = 1;
    sat.seen[v] = sat.model[v] = 0;
    sat.at[v] = -1;
    heap_add(v);
    return v;
}

static void sat_assign(int l, Clause *why) {
    sat.val[l] = 1;
    sat.val[l ^ 1] = 0;
    sat.level[l >> 1] = sat.nlim;
    sat.reason[l >> 1] = why;
    sat.trail[sat.ntrail++] = l;
}

static void sat_init(void) {
    sat.ok = 1;
    sat.var_inc = sat.cla_inc = 1;
    sat_assign(2 * sat_var(), NULL);
}

static void watch_push(Watches *ws, Clause *c, int blocker) {
    if (ws->n == ws->cap) ws->w = xrealloc(ws->w, sizeof(Watch) * (size_t)(ws->cap = ws->cap ? 2 * ws->cap : 4));
    ws->w[ws->n++] = (Watch){c, blocker};
}

static void sat_watch(Clause *c) {
    watch_push(&sat.watch[c->lits[0]], c, c->lits[1]);
    watch_push(&sat.watch[c->lits[1]], c, c->lits[0]);
}

/* The implied literal of a reason is its first. */
static Clause *sat_propagate(void) {
    while (sat.qhead < sat.ntrail) {
        int f = sat.trail[sat.qhead++] ^ 1;
        Watches *ws = &sat.watch[f];
        Watch *w = ws->w;
        int i = 0, j = 0, n = ws->n;
        while (i < n) {
            if (sat.val[w[i].blocker] == 1) { w[j++] = w[i++]; continue; }
            Clause *c = w[i++].c;
            int *l = c->lits;
            if (l[0] == f) { l[0] = l[1]; l[1] = f; }
            int first = l[0];
            if (sat.val[first] == 1) { w[j++] = (Watch){c, first}; continue; }
            int k = 2;
            while (k < c->n && sat.val[l[k]] == 0) k++;
            if (k < c->n) { l[1] = l[k]; l[k] = f; watch_push(&sat.watch[l[1]], c, first); continue; }
            w[j++] = (Watch){c, first};
            if (sat.val[first] == 0) {
                while (i < n) w[j++] = w[i++];
                ws->n = j;
                sat.qhead = sat.ntrail;
                return c;
            }
            sat_assign(first, c);
        }
        ws->n = j;
    }
    return NULL;
}

static void sat_cancel(int level) {
    if (sat.nlim <= level) return;
    for (int i = sat.ntrail - 1; i >= sat.lim[level]; i--) {
        int l = sat.trail[i];
        sat.val[l] = sat.val[l ^ 1] = -1;
        sat.reason[l >> 1] = NULL;
        sat.phase[l >> 1] = (unsigned char)(l & 1);
        heap_add(l >> 1);
    }
    sat.ntrail = sat.qhead = sat.lim[level];
    sat.nlim = level;
}

static void sat_bump(int v) {
    if ((sat.act[v] += sat.var_inc) > 1e100) {
        for (int i = 0; i < sat.nvars; i++) sat.act[i] *= 1e-100;
        sat.var_inc *= 1e-100;
    }
    if (sat.at[v] >= 0) heap_up(sat.at[v]);
}

static void sat_bump_clause(Clause *c) {
    if ((c->act += (float)sat.cla_inc) > 1e20f) {
        for (int i = 0; i < sat.learnts.n; i++) sat.learnts.c[i]->act *= 1e-20f;
        sat.cla_inc *= 1e-20;
    }
}

static void sat_room(int n) {
    if (sat.capbuf >= n) return;
    sat.capbuf = 2 * n;
    sat.buf = xrealloc(sat.buf, sizeof(int) * (size_t)sat.capbuf);
    sat.buf2 = xrealloc(sat.buf2, sizeof(int) * (size_t)sat.capbuf);
}

/* The first-UIP clause of a conflict in sat.buf, its asserting literal
   first and one of the next level second: returns the level to go back to. */
static int sat_analyze(Clause *c, int *nout) {
    sat_room(sat.nvars + 1);
    int *out = sat.buf, path = 0, p = -1, idx = sat.ntrail - 1, n = 1;
    do {
        if (c->learnt) sat_bump_clause(c);
        for (int k = p < 0 ? 0 : 1; k < c->n; k++) {
            int q = c->lits[k], v = q >> 1;
            if (sat.seen[v] || !sat.level[v]) continue;
            sat_bump(v);
            sat.seen[v] = 1;
            if (sat.level[v] >= sat.nlim) path++;
            else out[n++] = q;
        }
        while (!sat.seen[sat.trail[idx] >> 1]) idx--;
        p = sat.trail[idx--];
        c = sat.reason[p >> 1];
        sat.seen[p >> 1] = 0;
        path--;
    } while (path > 0);
    out[0] = p ^ 1;
    /* Leave out the literals the others imply. */
    memcpy(sat.buf2, out, sizeof(int) * (size_t)n);
    int m = 1;
    for (int i = 1; i < n; i++) {
        Clause *r = sat.reason[out[i] >> 1];
        int keep = !r;
        for (int k = 1; r && k < r->n && !keep; k++) { int u = r->lits[k] >> 1; keep = !sat.seen[u] && sat.level[u] > 0; }
        if (keep) out[m++] = out[i];
    }
    for (int i = 1; i < n; i++) sat.seen[sat.buf2[i] >> 1] = 0;
    sat.glue = 0;
    for (int i = 0; i < m; i++) {
        int lv = sat.level[out[i] >> 1];
        if (sat.stamp[lv] != sat.nconflicts) { sat.stamp[lv] = sat.nconflicts; sat.glue++; }
    }
    int back = 0;
    if (m > 1) {
        int best = 1;
        for (int i = 2; i < m; i++) if (sat.level[out[i] >> 1] > sat.level[out[best] >> 1]) best = i;
        int t = out[1]; out[1] = out[best]; out[best] = t;
        back = sat.level[out[1] >> 1];
    }
    *nout = m;
    return back;
}

static Clause *sat_clause(const int *lits, int n, int learnt) {
    Clause *c = xmalloc(sizeof(Clause) + sizeof(int) * (size_t)n);
    c->n = n;
    c->learnt = learnt;
    c->glue = sat.glue;
    c->act = 0;
    memcpy(c->lits, lits, sizeof(int) * (size_t)n);
    return c;
}

/* The worse first: more glue, then less active. */
static int clause_cmp(const void *x, const void *y) {
    const Clause *a = *(Clause *const *)x, *b = *(Clause *const *)y;
    if (a->glue != b->glue) return b->glue - a->glue;
    return (a->act > b->act) - (a->act < b->act);
}

/* Forgets the worse half of the learned clauses not in use, but those of
   glue 2, which tie two levels. */
static void sat_reduce(void) {
    Clauses *l = &sat.learnts;
    qsort(l->c, (size_t)l->n, sizeof(Clause *), clause_cmp);
    Clause **dead = xmalloc(sizeof(Clause *) * (size_t)(l->n + 1));
    int j = 0, nd = 0;
    for (int i = 0; i < l->n; i++) {
        Clause *c = l->c[i];
        int locked = sat.reason[c->lits[0] >> 1] == c && sat.val[c->lits[0]] == 1;
        if (i < l->n / 2 && c->n > 2 && c->glue > 2 && !locked) dead[nd++] = c;
        else l->c[j++] = c;
    }
    l->n = j;
    for (int i = 0; i < 2 * sat.nvars; i++) sat.watch[i].n = 0;
    for (int i = 0; i < sat.clauses.n; i++) sat_watch(sat.clauses.c[i]);
    for (int i = 0; i < l->n; i++) sat_watch(l->c[i]);
    for (int i = 0; i < nd; i++) free(dead[i]);
    free(dead);
}

static int sat_luby(int x) {
    int size = 1, seq = 0;
    while (size < x + 1) { seq++; size = 2 * size + 1; }
    while (size - 1 != x) { size = (size - 1) >> 1; seq--; x %= size; }
    return 1 << seq;
}

/* 1 satisfiable, 0 not under the assumptions, -1 out of conflicts. */
static int sat_search(long budget, const int *assume, int nassume) {
    for (long conflicts = 0;;) {
        Clause *c = sat_propagate();
        if (c) {
            conflicts++;
            sat.nconflicts++;
            if (!sat.nlim) return sat.ok = 0;
            int n, back = sat_analyze(c, &n);
            sat_cancel(back);
            if (n == 1) sat_assign(sat.buf[0], NULL);
            else {
                Clause *l = sat_clause(sat.buf, n, 1);
                clauses_push(&sat.learnts, l);
                sat_watch(l);
                sat_bump_clause(l);
                sat_assign(l->lits[0], l);
            }
            sat.var_inc /= 0.95;
            sat.cla_inc /= 0.999;
            continue;
        }
        if (conflicts >= budget) { sat_cancel(0); return -1; }
        if (sat.learnts.n - sat.ntrail >= sat.max_learnts) sat_reduce();
        int next = -1;
        while (sat.nlim < nassume && next < 0) {
            int p = assume[sat.nlim];
            if (sat.val[p] == 0) return 0;
            if (sat.val[p] == 1) sat.lim[sat.nlim++] = sat.ntrail;
            else next = p;
        }
        if (next < 0) {
            int v;
            do {
                if (!sat.nheap) {
                    for (int i = 0; i < sat.nvars; i++) sat.model[i] = sat.val[2 * i] == 1;
                    return 1;
                }
                v = heap_pop();
            } while (sat.val[2 * v] >= 0);
            next = 2 * v + sat.phase[v];
        }
        sat.lim[sat.nlim++] = sat.ntrail;
        sat_assign(next, NULL);
    }
}

/* Whether the clauses and the assumptions hold together; if they do, sat.model is a witness. */
static int sat_solve(const int *assume, int nassume) {
    if (!sat.ok) return 0;
    sat.max_learnts = sat.clauses.n / 3.0 + 10000;
    int r = 0, status;
    while ((status = sat_search(100L * sat_luby(r++), assume, nassume)) < 0) sat.max_learnts *= 1.1;
    sat_cancel(0);
    return status;
}

/* Adds a clause, between solves. */
static void sat_add(const int *lits, int n) {
    if (!sat.ok) return;
    sat_room(n + 1);
    int m = 0, satisfied = 0;
    for (int i = 0; i < n && !satisfied; i++) {
        int l = lits[i], v = l >> 1;
        if (sat.val[l] == 1) satisfied = 1;
        else if (sat.val[l] == 0) continue;
        else if (sat.seen[v]) satisfied = sat.seen[v] != 1 + (l & 1);
        else { sat.seen[v] = (unsigned char)(1 + (l & 1)); sat.buf[m++] = l; }
    }
    for (int i = 0; i < m; i++) sat.seen[sat.buf[i] >> 1] = 0;
    if (satisfied) return;
    if (!m) sat.ok = 0;
    else if (m == 1) { sat_assign(sat.buf[0], NULL); if (sat_propagate()) sat.ok = 0; }
    else { Clause *c = sat_clause(sat.buf, m, 0); clauses_push(&sat.clauses, c); sat_watch(c); }
}

static void sat_unit(int a) { sat_add(&a, 1); }
static void sat_add2(int a, int b) { int l[2] = {a, b}; sat_add(l, 2); }
static void sat_add3(int a, int b, int c) { int l[3] = {a, b, c}; sat_add(l, 3); }

static int lit_true(int l) { return l == L_TRUE || (l != L_FALSE && sat.model[l >> 1] ^ (l & 1)); }

/* ---------------------------------------------------------------- gates */

/* The connectives make literals for their results, each defined by its
   clauses once: equal gates are one (structural hashing), and constants
   fold away, so that what a constant decides costs nothing. */
typedef struct { int op, a, b, c, out; } Gate;
static Gate *gates;
static int ngates, capgates;

static uint64_t gate_hash(int op, int a, int b, int c) {
    return fmix(((uint64_t)(unsigned)op << 60) ^ ((uint64_t)(unsigned)a << 40) ^ ((uint64_t)(unsigned)b << 20) ^ (uint64_t)(unsigned)c);
}

static int gate_slot(Gate *t, int cap, int op, int a, int b, int c) {
    int i = (int)(gate_hash(op, a, b, c) & (uint64_t)(cap - 1));
    while (t[i].op && !(t[i].op == op && t[i].a == a && t[i].b == b && t[i].c == c)) i = (i + 1) & (cap - 1);
    return i;
}

/* The output of gate (op a b c); *fresh if it is new and needs its clauses. */
static int gate(int op, int a, int b, int c, int *fresh) {
    if (2 * (ngates + 1) > capgates) {
        int cap = capgates ? 2 * capgates : 1 << 16;
        Gate *t = xcalloc((size_t)cap, sizeof(Gate));
        for (int i = 0; i < capgates; i++)
            if (gates[i].op) t[gate_slot(t, cap, gates[i].op, gates[i].a, gates[i].b, gates[i].c)] = gates[i];
        free(gates);
        gates = t;
        capgates = cap;
    }
    int i = gate_slot(gates, capgates, op, a, b, c);
    *fresh = !gates[i].op;
    if (*fresh) { gates[i] = (Gate){op, a, b, c, 2 * sat_var()}; ngates++; }
    return gates[i].out;
}

static int g_and(int a, int b) {
    if (a > b) { int t = a; a = b; b = t; }
    if (a == L_FALSE || a == (b ^ 1)) return L_FALSE;
    if (a == L_TRUE || a == b) return b;
    int fresh, r = gate(1, a, b, 0, &fresh);
    if (fresh) { sat_add2(r ^ 1, a); sat_add2(r ^ 1, b); sat_add3(r, a ^ 1, b ^ 1); }
    return r;
}

static int g_or(int a, int b) { return g_and(a ^ 1, b ^ 1) ^ 1; }
static int g_implies(int a, int b) { return g_or(a ^ 1, b); }

static int g_xor(int a, int b) {
    int neg = (a ^ b) & 1;
    a &= ~1;
    b &= ~1;
    if (a > b) { int t = a; a = b; b = t; }
    if (a == b) return L_FALSE ^ neg;
    if (a == L_TRUE) return b ^ 1 ^ neg;
    int fresh, r = gate(2, a, b, 0, &fresh);
    if (fresh) { sat_add3(r ^ 1, a, b); sat_add3(r ^ 1, a ^ 1, b ^ 1); sat_add3(r, a ^ 1, b); sat_add3(r, a, b ^ 1); }
    return r ^ neg;
}

static int g_iff(int a, int b) { return g_xor(a, b) ^ 1; }

static int g_ite(int c, int t, int e) {
    if (c == L_TRUE || t == e) return t;
    if (c == L_FALSE) return e;
    if (c & 1) { int x = t; t = e; e = x; c ^= 1; }
    if (t == L_TRUE || t == c) return g_or(c, e);
    if (t == L_FALSE || t == (c ^ 1)) return g_and(c ^ 1, e);
    if (e == L_TRUE || e == (c ^ 1)) return g_or(c ^ 1, t);
    if (e == L_FALSE || e == c) return g_and(c, t);
    if (t == (e ^ 1)) return g_xor(c, e);
    int fresh, r = gate(3, c, t, e, &fresh);
    if (fresh) {
        sat_add3(c ^ 1, t ^ 1, r); sat_add3(c ^ 1, t, r ^ 1); sat_add3(c, e ^ 1, r); sat_add3(c, e, r ^ 1);
        sat_add3(t ^ 1, e ^ 1, r); sat_add3(t, e, r ^ 1);
    }
    return r;
}

/* n literals of which exactly one is true, as chosen by fresh ones. */
static int *one_hot(int n) {
    int *pick = NEWN(int, n > 0 ? n : 1), seen = L_FALSE;
    for (int i = 0; i + 1 < n; i++) {
        int s = 2 * sat_var();
        pick[i] = g_and(s, seen ^ 1);
        seen = g_or(seen, s);
    }
    if (n) pick[n - 1] = seen ^ 1;
    return pick;
}

/* ---------------------------------------------------------------- words */

/* An integer is a 64-bit two's complement word of literals, least
   significant first. Arithmetic asserts that it does not overflow: the
   behaviors whose integers leave 64 bits are not explored. */
#define BW 64

static int *bv_const(int64_t k) {
    int *b = NEWN(int, BW);
    for (int i = 0; i < BW; i++) b[i] = ((uint64_t)k >> i) & 1 ? L_TRUE : L_FALSE;
    return b;
}

static int bv_value(const int *b, int64_t *k) {
    uint64_t u = 0;
    for (int i = 0; i < BW; i++) {
        if (b[i] > L_FALSE) return 0;
        if (b[i] == L_TRUE) u |= (uint64_t)1 << i;
    }
    *k = (int64_t)u;
    return 1;
}

static int *bv_fresh(void) {
    int *b = NEWN(int, BW);
    for (int i = 0; i < BW; i++) b[i] = 2 * sat_var();
    return b;
}

static int *bv_ite(int c, const int *a, const int *b) {
    if (c == L_TRUE) return (int *)a;
    if (c == L_FALSE) return (int *)b;
    int *r = NEWN(int, BW);
    for (int i = 0; i < BW; i++) r[i] = g_ite(c, a[i], b[i]);
    return r;
}

static int bv_eq(const int *a, const int *b) {
    int r = L_TRUE;
    for (int i = 0; i < BW && r != L_FALSE; i++) r = g_and(r, g_iff(a[i], b[i]));
    return r;
}

/* a < b, signed: the highest bit that differs decides, the sign bit the other way. */
static int bv_lt(const int *a, const int *b) {
    int lt = L_FALSE;
    for (int i = 0; i < BW - 1; i++) lt = g_ite(g_xor(a[i], b[i]), b[i], lt);
    return g_ite(g_xor(a[BW - 1], b[BW - 1]), a[BW - 1], lt);
}

static int bv_le(const int *a, const int *b) { return bv_lt(b, a) ^ 1; }

static void no_overflow(int ovf) {
    if (ovf == L_TRUE) fail("Symbolic checking cannot represent an integer of more than %d bits.", BW);
    if (ovf != L_FALSE) sat_unit(ovf ^ 1);
}

static int *bv_add_carry(const int *a, const int *b, int carry, int *ovf) {
    int *s = NEWN(int, BW);
    for (int i = 0; i < BW; i++) {
        int x = g_xor(a[i], b[i]), out = g_or(g_and(a[i], b[i]), g_and(carry, x));
        s[i] = g_xor(x, carry);
        if (i == BW - 1) *ovf = g_xor(carry, out);
        carry = out;
    }
    return s;
}

static int *bv_not(const int *a) {
    int *r = NEWN(int, BW);
    for (int i = 0; i < BW; i++) r[i] = a[i] ^ 1;
    return r;
}

static int *bv_add(const int *a, const int *b) { int o, *s = bv_add_carry(a, b, L_FALSE, &o); no_overflow(o); return s; }
static int *bv_sub(const int *a, const int *b) { int o, *s = bv_add_carry(a, bv_not(b), L_TRUE, &o); no_overflow(o); return s; }
static int *bv_neg(const int *a) { return bv_sub(bv_const(0), a); }

/* The product, in twice the width: it overflows unless the high half
   repeats the sign. Shift and add, over the bits of b that may be set. */
static int *bv_mul(const int *a, const int *b) {
    int64_t k;
    if (bv_value(a, &k)) { const int *t = a; a = b; b = t; }
    if (bv_value(b, &k) && k < 0 && k != INT64_MIN) return bv_neg(bv_mul(a, bv_const(-k)));
    int w = 2 * BW, *acc = NEWN(int, w);
    for (int i = 0; i < w; i++) acc[i] = L_FALSE;
    for (int i = 0; i < w; i++) {
        int bi = b[i < BW ? i : BW - 1];
        if (bi == L_FALSE) continue;
        int carry = L_FALSE;
        for (int j = i; j < w; j++) {
            int p = g_and(a[j - i < BW ? j - i : BW - 1], bi), x = g_xor(acc[j], p);
            int out = g_or(g_and(acc[j], p), g_and(carry, x));
            acc[j] = g_xor(x, carry);
            carry = out;
        }
    }
    for (int i = BW; i < w; i++) no_overflow(g_xor(acc[i], acc[BW - 1]));
    return acc;
}

/* a \div b and a % b for b > 0: a = q * b + r and 0 <= r < b. For other
   b, as Apalache's solver leaves them, any. */
static void bv_divmod(const int *a, const int *b, int **q, int **r) {
    int64_t k;
    if (bv_value(b, &k) && k > 0 && !(k & (k - 1))) {   /* a shift: floor, as an arithmetic one */
        int s = 0;
        while ((int64_t)1 << s < k) s++;
        *q = NEWN(int, BW);
        *r = NEWN(int, BW);
        for (int i = 0; i < BW; i++) { (*q)[i] = i + s < BW ? a[i + s] : a[BW - 1]; (*r)[i] = i < s ? a[i] : L_FALSE; }
        return;
    }
    *q = bv_fresh();
    *r = bv_fresh();
    int *zero = bv_const(0), o1, o2;
    int w = 2 * BW, *m = NEWN(int, w);
    /* q * b without asserting it fits: only for b > 0 must it */
    for (int i = 0; i < w; i++) m[i] = L_FALSE;
    for (int i = 0; i < w; i++) {
        int bi = b[i < BW ? i : BW - 1], carry = L_FALSE;
        if (bi == L_FALSE) continue;
        for (int j = i; j < w; j++) {
            int p = g_and((*q)[j - i < BW ? j - i : BW - 1], bi), x = g_xor(m[j], p);
            int out = g_or(g_and(m[j], p), g_and(carry, x));
            m[j] = g_xor(x, carry);
            carry = out;
        }
    }
    o1 = L_FALSE;
    for (int i = BW; i < w; i++) o1 = g_or(o1, g_xor(m[i], m[BW - 1]));
    int *sum = bv_add_carry(m, *r, L_FALSE, &o2);
    int ok = g_and(g_and(bv_eq(sum, a), g_and(o1 ^ 1, o2 ^ 1)), g_and(bv_lt(*r, b), bv_lt(*r, zero) ^ 1));
    sat_add2(bv_lt(zero, b) ^ 1, ok);
}

/* ---------------------------------------------------------------- symbolic values */

/* A symbolic value is a concrete value, or a structure of literals: a
   boolean, an integer or atom (a string or model value, as a code), a
   finite set of guarded elements (an element is in the set when its guard
   is true), a function of guarded pairs (its domain the keys whose guard
   is true), or a set kept by its definition, such as Nat or [S -> T].
   The value of an expression that went wrong is undefined: it carries the
   error, and which one it is matters only if it is the value of a state. */
enum { SV_CONST, SV_BOOL, SV_INT, SV_ATOM, SV_SET, SV_FCN, SV_INF, SV_UNDEF };
enum { INF_INT, INF_NAT, INF_STRING, INF_SUBSET, INF_FCNSET, INF_RCDSET, INF_TIMES, INF_SEQ, INF_RANGE, INF_MINUS, INF_FILTER };
enum { C_BOOL, C_INT, C_ATOM, C_SET, C_FCN, C_NONE };

typedef struct SEnv SEnv;
typedef struct { Ctx c; SEnv *s; } SCtx;
struct Filter { Expr *e; SCtx sc; };   /* INF_FILTER: {x \in S : P}, where it is */

typedef struct SVal SVal;
struct SVal {
    unsigned char kind, inf, rec, known;   /* rec: a record; known: whether value was looked for */
    int n;
    Value *value;    /* SV_CONST's, and another's once known to be concrete */
    union {
        int lit;
        int *bits;
        struct { SVal **elems; int *guards; } set;
        struct { SVal **keys, **vals; int *guards; } fcn;
        struct { SVal **parts; int *names; struct Filter *filter; } inf;   /* RCDSET: field names */
        char *err;
    } u;
};

static SVal *sv_new(int kind) { SVal *s = NEW(SVal); s->kind = (unsigned char)kind; return s; }
static SVal *sv_const(Value *v) { SVal *s = sv_new(SV_CONST); s->value = v; return s; }
static SVal *sv_bool(int lit) { SVal *s = sv_new(SV_BOOL); s->u.lit = lit; return s; }
static SVal *sv_bits(int kind, int *bits) { SVal *s = sv_new(kind); s->u.bits = bits; return s; }

static SVal *sv_set(int n) {
    SVal *s = sv_new(SV_SET);
    s->u.set.elems = NEWN(SVal *, n > 0 ? n : 1);
    s->u.set.guards = NEWN(int, n > 0 ? n : 1);
    return s;
}

static void set_add(SVal *s, SVal *e, int g) {
    if (g == L_FALSE) return;
    s->u.set.elems[s->n] = e;
    s->u.set.guards[s->n++] = g;
}

static int sv_same(SVal *a, SVal *b);

/* Adds e to s under g, or, if s has it, under its guard or g. */
static void set_join(SVal *s, SVal *e, int g) {
    for (int i = 0; i < s->n; i++)
        if (sv_same(s->u.set.elems[i], e)) { s->u.set.guards[i] = g_or(s->u.set.guards[i], g); return; }
    set_add(s, e, g);
}

static SVal *sv_fcn(int n, int rec) {
    SVal *s = sv_new(SV_FCN);
    s->rec = (unsigned char)rec;
    s->u.fcn.keys = NEWN(SVal *, n > 0 ? n : 1);
    s->u.fcn.vals = NEWN(SVal *, n > 0 ? n : 1);
    s->u.fcn.guards = NEWN(int, n > 0 ? n : 1);
    return s;
}

static void fcn_add(SVal *f, SVal *k, SVal *v, int g) {
    if (g == L_FALSE) return;
    f->u.fcn.keys[f->n] = k;
    f->u.fcn.vals[f->n] = v;
    f->u.fcn.guards[f->n++] = g;
}

static SVal *sv_inf(int inf, int n) {
    SVal *s = sv_new(SV_INF);
    s->inf = (unsigned char)inf;
    s->n = n;
    s->u.inf.parts = NEWN(SVal *, n > 0 ? n : 1);
    s->u.inf.names = NEWN(int, n > 0 ? n : 1);
    return s;
}

static SVal *sv_undef(void) {
    SVal *s = sv_new(SV_UNDEF);
    s->u.err = strdup(error_message.s ? error_message.s : "an undefined value");
    return s;
}

static SVal *sv_int_const(int64_t i) { return sv_const(mk_int(i)); }

static int64_t atom_code(Value *v) { return 2 * v->u.i + (v->kind == V_MODEL); }
static Value *atom_value(int64_t code) { return code & 1 ? mk_model((int)(code >> 1)) : mk_str((int)(code >> 1)); }

static int sv_class(SVal *s) {
    switch (s->kind) {
    case SV_CONST:
        switch (s->value->kind) {
        case V_BOOL: return C_BOOL;
        case V_INT: return C_INT;
        case V_STR: case V_MODEL: return C_ATOM;
        case V_TUPLE: case V_FCN: case V_LAMBDA: return C_FCN;
        case V_OPER: return C_NONE;
        default: return C_SET;
        }
    case SV_BOOL: return C_BOOL;
    case SV_INT: return C_INT;
    case SV_ATOM: return C_ATOM;
    case SV_SET: case SV_INF: return C_SET;
    case SV_FCN: return C_FCN;
    default: return C_NONE;
    }
}

static const char *class_name(int c) {
    static const char *names[] = {"a boolean", "an integer", "a string or model value", "a set", "a function", "an operator"};
    return names[c];
}

/* s as a structure, one level down: a concrete value's parts stay concrete. */
static SVal *sv_open(SVal *s) {
    if (s->kind != SV_CONST) return s;
    Value *v = realize(s->value);
    SVal *o;
    switch (v->kind) {
    case V_BOOL: return sv_bool(v->u.i ? L_TRUE : L_FALSE);
    case V_INT: return sv_bits(SV_INT, bv_const(v->u.i));
    case V_STR: case V_MODEL: return sv_bits(SV_ATOM, bv_const(atom_code(v)));
    case V_TUPLE: case V_FCN:
        o = sv_fcn(v->n, v->kind == V_FCN && v->made == MADE_RECORD);
        for (int i = 0; i < v->n; i++) fcn_add(o, sv_const(fcn_key(v, i)), sv_const(v->u.fcn.vals[i]), L_TRUE);
        return o;
    case V_SET:
        o = sv_set(v->n);
        for (int i = 0; i < v->n; i++) set_add(o, sv_const(v->u.set.elems[i]), L_TRUE);
        return o;
    case V_INTERVAL: {   /* a large one as a range, which sv_enum lists only where its elements are needed */
        int n = interval_size(v);
        if (n > 4096) {
            o = sv_inf(INF_RANGE, 2);
            o->u.inf.parts[0] = sv_int_const(v->u.range.lo);
            o->u.inf.parts[1] = sv_int_const(v->u.range.hi);
            return o;
        }
        o = sv_set(n);
        for (int i = 0; i < n; i++) set_add(o, sv_int_const(v->u.range.lo + i), L_TRUE);
        return o;
    }
    case V_LAZY:
        switch (v->lazy) {
        case L_INT: return sv_inf(INF_INT, 0);
        case L_NAT: return sv_inf(INF_NAT, 0);
        case L_STRING: return sv_inf(INF_STRING, 0);
        case L_SUBSET: o = sv_inf(INF_SUBSET, 1); o->u.inf.parts[0] = sv_const(v->u.l.a); return o;
        case L_SEQ: o = sv_inf(INF_SEQ, 1); o->u.inf.parts[0] = sv_const(v->u.l.a); return o;
        case L_FCNSET:
            o = sv_inf(INF_FCNSET, 2);
            o->u.inf.parts[0] = sv_const(v->u.l.a);
            o->u.inf.parts[1] = sv_const(v->u.l.b);
            return o;
        case L_RCDSET: case L_TIMES:
            o = sv_inf(v->lazy == L_RCDSET ? INF_RCDSET : INF_TIMES, v->n);
            for (int i = 0; i < v->n; i++) {
                if (v->lazy == L_RCDSET) o->u.inf.names[i] = (int)v->u.l.names[i]->u.i;
                o->u.inf.parts[i] = sv_const(v->u.l.names[v->n + i]);
            }
            return o;
        case L_FILTER: {
            Expr *e = v->u.l.expr;
            if (enumerable(v->u.l.a) || e->bounds[0].n != 1 || e->bounds[0].tuple) return sv_open(sv_const(enumerate(v)));
            o = sv_inf(INF_FILTER, 1);
            o->u.inf.parts[0] = sv_const(v->u.l.a);
            o->u.inf.filter = NEW(struct Filter);
            *o->u.inf.filter = (struct Filter){e, {{v->u.l.env, v->u.l.inst}, NULL}};
            return o;
        }
        case L_DIFF:
            if (enumerable(v->u.l.a)) return sv_open(sv_const(enumerate(v)));
            o = sv_inf(INF_MINUS, 2);
            o->u.inf.parts[0] = sv_const(v->u.l.a);
            o->u.inf.parts[1] = sv_const(v->u.l.b);
            return o;
        default:
            return sv_open(sv_const(enumerate(v)));
        }
    default:
        fail("Symbolic checking cannot use %s as a value.", pretty(v));
    }
}

static Value *values_set(Value **vs, int n) { return manyan_set((size_t)n, vs); }

/* A function of pairs as TLC has it: a record, a tuple, or another. */
static Value *values_fcn(Value **keys, Value **vals, int n, int rec) {
    int tuple = !rec;
    for (int i = 0; i < n && tuple; i++) tuple = keys[i]->kind == V_INT;
    if (tuple) {
        Value **at = NEWN(Value *, n > 0 ? n : 1);
        for (int i = 0; i < n && tuple; i++) {
            int64_t k = keys[i]->u.i;
            tuple = k >= 1 && k <= n && !at[k - 1];
            if (tuple) at[k - 1] = vals[i];
        }
        if (tuple) return manyan_tuple((size_t)n, at);
    }
    return rec ? manyan_record((size_t)n, keys, vals) : manyan_function((size_t)n, keys, vals);
}

/* The concrete value s is, if its literals are all constant; else NULL. */
static Value *sv_known(SVal *s) {
    if (s->kind == SV_CONST || s->known) return s->value;
    s->known = 1;
    Value *v = NULL, **ks, **vs;
    int64_t k;
    int m = 0;
    switch (s->kind) {
    case SV_BOOL: if (s->u.lit <= L_FALSE) v = BOOLV(s->u.lit == L_TRUE); break;
    case SV_INT: if (bv_value(s->u.bits, &k)) v = mk_int(k); break;
    case SV_ATOM: if (bv_value(s->u.bits, &k)) v = atom_value(k); break;
    case SV_SET:
        vs = NEWN(Value *, s->n > 0 ? s->n : 1);
        for (int i = 0; i < s->n; i++) {
            if (s->u.set.guards[i] == L_FALSE) continue;
            if (s->u.set.guards[i] != L_TRUE || !(vs[m++] = sv_known(s->u.set.elems[i]))) return NULL;
        }
        v = values_set(vs, m);
        break;
    case SV_FCN:
        ks = NEWN(Value *, s->n > 0 ? s->n : 1);
        vs = NEWN(Value *, s->n > 0 ? s->n : 1);
        for (int i = 0; i < s->n; i++) {
            if (s->u.fcn.guards[i] == L_FALSE) continue;
            if (s->u.fcn.guards[i] != L_TRUE || !(ks[m] = sv_known(s->u.fcn.keys[i])) || !(vs[m] = sv_known(s->u.fcn.vals[i]))) return NULL;
            m++;
        }
        v = values_fcn(ks, vs, m, s->rec);
        break;
    default: break;
    }
    return s->value = v;
}

/* Whether a and b are the same structure of the same literals. */
static int sv_same(SVal *a, SVal *b) {
    if (a == b) return 1;
    Value *x = sv_known(a), *y = sv_known(b);
    if (x || y) {
        if (!x || !y || sv_class(a) != sv_class(b)) return 0;
        if (x->kind == V_LAZY || y->kind == V_LAZY) return x == y;
        return veq(x, y);
    }
    if (a->kind != b->kind || a->n != b->n) return 0;
    switch (a->kind) {
    case SV_BOOL: return a->u.lit == b->u.lit;
    case SV_INT: case SV_ATOM: return !memcmp(a->u.bits, b->u.bits, sizeof(int) * BW);
    case SV_SET:
        for (int i = 0; i < a->n; i++)
            if (a->u.set.guards[i] != b->u.set.guards[i] || !sv_same(a->u.set.elems[i], b->u.set.elems[i])) return 0;
        return 1;
    case SV_FCN:
        if (a->rec != b->rec) return 0;
        for (int i = 0; i < a->n; i++)
            if (a->u.fcn.guards[i] != b->u.fcn.guards[i] || !sv_same(a->u.fcn.keys[i], b->u.fcn.keys[i])
                || !sv_same(a->u.fcn.vals[i], b->u.fcn.vals[i])) return 0;
        return 1;
    case SV_INF:
        if (a->inf != b->inf || a->u.inf.filter != b->u.inf.filter) return 0;
        for (int i = 0; i < a->n; i++)
            if (a->u.inf.names[i] != b->u.inf.names[i] || !sv_same(a->u.inf.parts[i], b->u.inf.parts[i])) return 0;
        return 1;
    default: return 0;
    }
}

static _Noreturn void kinds_mismatch(SVal *a, SVal *b) {
    fail("Symbolic checking cannot combine %s and %s in one value: Apalache would reject the spec's types.",
         class_name(sv_class(a)), class_name(sv_class(b)));
}

static SVal *sv_ite(int c, SVal *a, SVal *b);

/* The elements or pairs of a and b, those of a under c and those of b
   under not c; the same element or key once. */
static SVal *merge_parts(int c, SVal *a, SVal *b) {
    int fcn = a->kind == SV_FCN;
    SVal *r = fcn ? sv_fcn(a->n + b->n, a->rec | b->rec) : sv_set(a->n + b->n);
    char *used = NEWN(char, b->n > 0 ? b->n : 1);
    SVal **ak = fcn ? a->u.fcn.keys : a->u.set.elems, **bk = fcn ? b->u.fcn.keys : b->u.set.elems;
    int *ag = fcn ? a->u.fcn.guards : a->u.set.guards, *bg = fcn ? b->u.fcn.guards : b->u.set.guards;
    for (int i = 0; i < a->n; i++) {
        int j = 0;
        while (j < b->n && (used[j] || !sv_same(ak[i], bk[j]))) j++;
        int g = j < b->n ? g_ite(c, ag[i], bg[j]) : g_and(c, ag[i]);
        if (j < b->n) used[j] = 1;
        if (!fcn) set_add(r, ak[i], g);
        else fcn_add(r, ak[i], j < b->n ? sv_ite(c, a->u.fcn.vals[i], b->u.fcn.vals[j]) : a->u.fcn.vals[i], g);
    }
    for (int j = 0; j < b->n; j++) {
        if (used[j]) continue;
        if (!fcn) set_add(r, bk[j], g_and(c ^ 1, bg[j]));
        else fcn_add(r, bk[j], b->u.fcn.vals[j], g_and(c ^ 1, bg[j]));
    }
    return r;
}

/* IF c THEN a ELSE b. */
static SVal *sv_ite(int c, SVal *a, SVal *b) {
    if (c == L_TRUE || b->kind == SV_UNDEF) return a;
    if (c == L_FALSE || a->kind == SV_UNDEF) return b;
    if (sv_same(a, b)) return a;
    if (sv_class(a) != sv_class(b)) kinds_mismatch(a, b);
    a = sv_open(a);
    b = sv_open(b);
    switch (a->kind) {
    case SV_BOOL: return sv_bool(g_ite(c, a->u.lit, b->u.lit));
    case SV_INT: case SV_ATOM: return sv_bits(a->kind, bv_ite(c, a->u.bits, b->u.bits));
    case SV_SET: case SV_FCN:
        if (a->kind != b->kind) break;
        return merge_parts(c, a, b);
    default: break;
    }
    fail("Symbolic checking cannot choose between two infinite sets by a condition.");
}

/* An undefined value used as a Boolean or an integer becomes an arbitrary
   one, the same wherever it is shared, as Apalache leaves it. */
static int sv_lit(SVal *s, Expr *where) {
    if (s->kind == SV_UNDEF) { s->kind = SV_BOOL; s->u.lit = 2 * sat_var(); }
    if (sv_class(s) != C_BOOL) fail_at(where, "A non-boolean expression (%s) was used as a condition.", class_name(sv_class(s)));
    return sv_open(s)->u.lit;
}

static int *sv_word(SVal *s, Expr *where) {
    if (s->kind == SV_UNDEF) { s->kind = SV_INT; s->u.bits = bv_fresh(); }
    if (sv_class(s) != C_INT) fail_at(where, "Symbolic checking expected an integer, but has %s.", class_name(sv_class(s)));
    return sv_open(s)->u.bits;
}

static int sv_eq(SVal *a, SVal *b);
static int sv_in(SVal *x, SVal *s);
static int filter_holds(SVal *s, SVal *x);
static SVal *sv_enum(SVal *s);

static int sv_subseteq(SVal *a, SVal *b) {
    a = sv_open(a);
    if (a->kind == SV_INF) {
        b = sv_open(b);
        if (b->kind == SV_INF && (b->inf == INF_INT ? a->inf == INF_INT || a->inf == INF_NAT : a->inf == b->inf && sv_same(a, b)))
            return L_TRUE;
        a = sv_enum(a);
    }
    int r = L_TRUE;
    for (int i = 0; i < a->n && r != L_FALSE; i++) r = g_and(r, g_implies(a->u.set.guards[i], sv_in(a->u.set.elems[i], b)));
    return r;
}

static int fcn_eq(SVal *a, SVal *b) {
    int aligned = a->n == b->n, r = L_TRUE;
    for (int i = 0; i < a->n && aligned; i++) aligned = sv_same(a->u.fcn.keys[i], b->u.fcn.keys[i]);
    if (aligned) {
        for (int i = 0; i < a->n && r != L_FALSE; i++)
            r = g_and(r, g_and(g_iff(a->u.fcn.guards[i], b->u.fcn.guards[i]),
                               g_implies(a->u.fcn.guards[i], sv_eq(a->u.fcn.vals[i], b->u.fcn.vals[i]))));
        return r;
    }
    for (int i = 0; i < a->n && r != L_FALSE; i++) {
        int match = L_FALSE;
        for (int j = 0; j < b->n; j++) {
            int k = g_and(b->u.fcn.guards[j], sv_eq(a->u.fcn.keys[i], b->u.fcn.keys[j]));
            if (k != L_FALSE) match = g_or(match, g_and(k, sv_eq(a->u.fcn.vals[i], b->u.fcn.vals[j])));
        }
        r = g_and(r, g_implies(a->u.fcn.guards[i], match));
    }
    for (int j = 0; j < b->n && r != L_FALSE; j++) {
        int has = L_FALSE;
        for (int i = 0; i < a->n && has != L_TRUE; i++) has = g_or(has, g_and(a->u.fcn.guards[i], sv_eq(b->u.fcn.keys[j], a->u.fcn.keys[i])));
        r = g_and(r, g_implies(b->u.fcn.guards[j], has));
    }
    return r;
}

static int sv_eq(SVal *a, SVal *b) {
    if (a->kind == SV_UNDEF || b->kind == SV_UNDEF) return 2 * sat_var();
    int ca = sv_class(a);
    if (ca != sv_class(b)) return L_FALSE;
    Value *x = sv_known(a), *y = sv_known(b);
    if (x && y) return veq(x, y) ? L_TRUE : L_FALSE;
    if (sv_same(a, b)) return L_TRUE;
    a = sv_open(a);
    b = sv_open(b);
    switch (ca) {
    case C_BOOL: return g_iff(a->u.lit, b->u.lit);
    case C_INT: case C_ATOM: return bv_eq(a->u.bits, b->u.bits);
    case C_SET:
        if (a->kind == SV_INF && b->kind == SV_INF && a->inf == b->inf && a->n == b->n) {
            int r = L_TRUE;
            for (int i = 0; i < a->n; i++) {
                if (a->u.inf.names[i] != b->u.inf.names[i]) return L_FALSE;
                r = g_and(r, sv_eq(a->u.inf.parts[i], b->u.inf.parts[i]));
            }
            return r;
        }
        return g_and(sv_subseteq(a, b), sv_subseteq(b, a));
    default: return fcn_eq(a, b);
    }
}

static SVal *sv_domain(SVal *f) {
    f = sv_open(f);
    if (f->kind == SV_UNDEF) return f;
    if (f->kind != SV_FCN) fail("Symbolic checking cannot take the domain of %s.", class_name(sv_class(f)));
    SVal *d = sv_set(f->n);
    for (int i = 0; i < f->n; i++) set_add(d, f->u.fcn.keys[i], f->u.fcn.guards[i]);
    return d;
}

static SVal *names_set(SVal *s) {
    Value **vs = NEWN(Value *, s->n > 0 ? s->n : 1);
    for (int i = 0; i < s->n; i++) vs[i] = s->inf == INF_RCDSET ? mk_str(s->u.inf.names[i]) : mk_int(i + 1);
    return sv_const(values_set(vs, s->n));
}

static SVal *sv_apply(SVal *f, SVal *x);

static int values_in(SVal *f, SVal *s) {
    f = sv_open(f);
    int r = L_TRUE;
    for (int i = 0; i < f->n && r != L_FALSE; i++) r = g_and(r, g_implies(f->u.fcn.guards[i], sv_in(f->u.fcn.vals[i], s)));
    return r;
}

static int sv_in(SVal *x, SVal *s) {
    if (s->kind == SV_UNDEF) return 2 * sat_var();
    Value *xv = sv_known(x), *sv = sv_known(s);
    if (xv && sv && sv->kind != V_LAZY) return set_member(xv, sv) ? L_TRUE : L_FALSE;
    s = sv_open(s);
    if (s->kind == SV_SET) {   /* an undefined x is equal to each element or not, and in no empty set */
        int r = L_FALSE;
        for (int i = 0; i < s->n && r != L_TRUE; i++) r = g_or(r, g_and(s->u.set.guards[i], sv_eq(x, s->u.set.elems[i])));
        return r;
    }
    if (s->kind != SV_INF) fail("Symbolic checking found \\in applied to %s, not a set.", class_name(sv_class(s)));
    if (x->kind == SV_UNDEF) return 2 * sat_var();
    int cx = sv_class(x);
    switch (s->inf) {
    case INF_INT: return cx == C_INT ? L_TRUE : L_FALSE;
    case INF_NAT: return cx == C_INT ? sv_open(x)->u.bits[BW - 1] ^ 1 : L_FALSE;
    case INF_STRING: return cx == C_ATOM ? sv_open(x)->u.bits[0] ^ 1 : L_FALSE;
    case INF_RANGE: {
        if (cx != C_INT) return L_FALSE;
        int *b = sv_open(x)->u.bits;
        return g_and(bv_le(sv_open(s->u.inf.parts[0])->u.bits, b), bv_le(b, sv_open(s->u.inf.parts[1])->u.bits));
    }
    case INF_SUBSET: return cx == C_SET ? sv_subseteq(x, s->u.inf.parts[0]) : L_FALSE;
    case INF_MINUS: return g_and(sv_in(x, s->u.inf.parts[0]), sv_in(x, s->u.inf.parts[1]) ^ 1);
    case INF_FILTER: return g_and(sv_in(x, s->u.inf.parts[0]), filter_holds(s, x));
    case INF_FCNSET:
        if (cx != C_FCN) return L_FALSE;
        return g_and(sv_eq(sv_domain(x), s->u.inf.parts[0]), values_in(x, s->u.inf.parts[1]));
    case INF_SEQ: {
        if (cx != C_FCN) return L_FALSE;
        x = sv_open(x);
        int r = values_in(x, s->u.inf.parts[0]);
        for (int i = 0; i < x->n && r != L_FALSE; i++) {   /* the keys are 1..n */
            int k = x->u.fcn.guards[i];
            r = g_and(r, g_implies(k, sv_in(x->u.fcn.keys[i], sv_inf(INF_NAT, 0))));
            r = g_and(r, g_implies(k, sv_eq(x->u.fcn.keys[i], sv_int_const(0)) ^ 1));
        }
        return r;
    }
    default: {   /* INF_RCDSET, INF_TIMES */
        if (cx != C_FCN) return L_FALSE;
        int r = sv_eq(sv_domain(x), names_set(s));
        for (int i = 0; i < s->n && r != L_FALSE; i++) {
            SVal *k = s->inf == INF_RCDSET ? sv_const(mk_str(s->u.inf.names[i])) : sv_int_const(i + 1);
            r = g_and(r, sv_in(sv_apply(x, k), s->u.inf.parts[i]));
        }
        return r;
    }
    }
}

/* The largest value a word can have, from its constant high bits; -1 if unknown. */
static int64_t bv_bound(const int *b) {
    if (b[BW - 1] != L_FALSE) return -1;
    int top = BW - 2;
    while (top >= 0 && b[top] == L_FALSE) top--;
    if (top > 20) return -1;
    return ((int64_t)1 << (top + 1)) - 1;
}

/* s as a finite set of guarded elements. */
static SVal *sv_enum(SVal *s) {
    s = sv_open(s);
    if (s->kind == SV_SET) return s;
    if (s->kind != SV_INF) fail("Symbolic checking expected a set, but has %s.", class_name(sv_class(s)));
    SVal *r, **parts = NULL;
    int64_t total = 1;
    switch (s->inf) {
    case INF_RANGE: {
        int *lo = sv_open(s->u.inf.parts[0])->u.bits, *hi = sv_open(s->u.inf.parts[1])->u.bits;
        int64_t l, h = bv_bound(hi);
        if (!bv_value(lo, &l) || h < 0) break;
        r = sv_set(h >= l ? (int)(h - l + 1) : 0);
        for (int64_t i = l; i <= h; i++) {
            int *w = bv_const(i);
            set_add(r, sv_int_const(i), g_and(bv_le(lo, w), bv_le(w, hi)));
        }
        return r;
    }
    case INF_SUBSET: {
        SVal *b = sv_enum(s->u.inf.parts[0]);
        if (b->n > 16) break;
        r = sv_set(1 << b->n);
        for (int m = 0; m < 1 << b->n; m++) {
            SVal *t = sv_set(b->n);
            for (int i = 0; i < b->n; i++) if (m >> i & 1) set_add(t, b->u.set.elems[i], b->u.set.guards[i]);
            set_add(r, t, L_TRUE);
        }
        return r;
    }
    case INF_FCNSET: {
        SVal *d = sv_enum(s->u.inf.parts[0]), *rng = sv_enum(s->u.inf.parts[1]);
        for (int i = 0; i < d->n && total <= 4096; i++) total *= rng->n;
        if (total > 4096) break;
        r = sv_set((int)total);
        for (int64_t m = 0; m < total; m++) {
            SVal *f = sv_fcn(d->n, 0);
            int g = L_TRUE;
            for (int64_t i = 0, k = m; i < d->n; i++, k /= rng->n) {
                int j = (int)(k % rng->n);
                fcn_add(f, d->u.set.elems[i], rng->u.set.elems[j], d->u.set.guards[i]);
                g = g_and(g, g_implies(d->u.set.guards[i], rng->u.set.guards[j]));
            }
            set_add(r, f, g);
        }
        return r;
    }
    case INF_RCDSET: case INF_TIMES:
        parts = NEWN(SVal *, s->n > 0 ? s->n : 1);
        for (int i = 0; i < s->n && total <= 4096; i++) total *= (parts[i] = sv_enum(s->u.inf.parts[i]))->n;
        if (total > 4096) break;
        r = sv_set((int)total);
        for (int64_t m = 0; m < total; m++) {
            SVal *f = sv_fcn(s->n, s->inf == INF_RCDSET);
            int g = L_TRUE;
            for (int64_t i = 0, k = m; i < s->n; k /= parts[i]->n, i++) {
                int j = (int)(k % parts[i]->n);
                fcn_add(f, s->inf == INF_RCDSET ? sv_const(mk_str(s->u.inf.names[i])) : sv_int_const(i + 1), parts[i]->u.set.elems[j], L_TRUE);
                g = g_and(g, parts[i]->u.set.guards[j]);
            }
            set_add(r, f, g);
        }
        return r;
    default: break;
    }
    fail("Symbolic checking cannot enumerate this set: it is infinite or too large.");
}

/* f[x]: the value of the pair whose key x is, or of the last pair if none
   is, which Apalache leaves unspecified. */
static SVal *sv_apply(SVal *f, SVal *x) {
    if (f->kind == SV_UNDEF) return f;
    if (x->kind == SV_UNDEF) return x;
    f = sv_open(f);
    if (f->kind != SV_FCN) fail("Symbolic checking found %s applied as a function.", class_name(sv_class(f)));
    Value *xv = sv_known(x);
    for (int i = 0; xv && i < f->n; i++) {
        Value *k = sv_known(f->u.fcn.keys[i]);
        if (k && sv_class(f->u.fcn.keys[i]) == sv_class(x) && veq(k, xv) && f->u.fcn.guards[i] == L_TRUE) return f->u.fcn.vals[i];
    }
    if (!f->n) { error_reset(); buf_puts(&error_message, "A function with an empty domain was applied."); return sv_undef(); }
    SVal *r = f->u.fcn.vals[f->n - 1];
    for (int i = f->n - 2; i >= 0; i--) r = sv_ite(g_and(f->u.fcn.guards[i], sv_eq(f->u.fcn.keys[i], x)), f->u.fcn.vals[i], r);
    return r;
}

/* [f EXCEPT ![k] = v]. */
static SVal *sv_update(SVal *f, SVal *k, SVal *v) {
    if (f->kind == SV_UNDEF) return f;
    f = sv_open(f);
    if (f->kind != SV_FCN) fail("Symbolic checking found EXCEPT applied to %s.", class_name(sv_class(f)));
    SVal *g = sv_fcn(f->n, f->rec);
    for (int i = 0; i < f->n; i++)
        fcn_add(g, f->u.fcn.keys[i], sv_ite(sv_eq(f->u.fcn.keys[i], k), v, f->u.fcn.vals[i]), f->u.fcn.guards[i]);
    return g;
}

/* Some element of s, with *g whether it is one: s's guard of it. */
static SVal *sv_pick(SVal *s, int *g) {
    if (s->kind == SV_UNDEF) { *g = L_FALSE; return s; }
    s = sv_open(s);
    SVal *r;
    if (s->kind == SV_SET) {
        if (!s->n) { *g = L_FALSE; error_reset(); buf_puts(&error_message, "No element of an empty set."); return sv_undef(); }
        int *pick = one_hot(s->n);
        r = s->u.set.elems[s->n - 1];
        *g = L_FALSE;
        for (int i = s->n - 1; i >= 0; i--) {
            if (i < s->n - 1) r = sv_ite(pick[i], s->u.set.elems[i], r);
            *g = g_or(*g, g_and(pick[i], s->u.set.guards[i]));
        }
        return r;
    }
    if (s->kind != SV_INF) fail("Symbolic checking expected a set, but has %s.", class_name(sv_class(s)));
    int *w;
    switch (s->inf) {
    case INF_INT: *g = L_TRUE; return sv_bits(SV_INT, bv_fresh());
    case INF_NAT: w = bv_fresh(); *g = w[BW - 1] ^ 1; return sv_bits(SV_INT, w);
    case INF_RANGE:
        w = bv_fresh();
        *g = g_and(bv_le(sv_open(s->u.inf.parts[0])->u.bits, w), bv_le(w, sv_open(s->u.inf.parts[1])->u.bits));
        return sv_bits(SV_INT, w);
    case INF_SUBSET: {
        SVal *b = sv_enum(s->u.inf.parts[0]);
        r = sv_set(b->n);
        for (int i = 0; i < b->n; i++) set_add(r, b->u.set.elems[i], g_and(2 * sat_var(), b->u.set.guards[i]));
        *g = L_TRUE;
        return r;
    }
    case INF_FCNSET: {
        SVal *d = sv_enum(s->u.inf.parts[0]);
        r = sv_fcn(d->n, 0);
        *g = L_TRUE;
        for (int i = 0; i < d->n; i++) {
            int h;
            SVal *v = sv_pick(s->u.inf.parts[1], &h);
            fcn_add(r, d->u.set.elems[i], v, d->u.set.guards[i]);
            *g = g_and(*g, g_implies(d->u.set.guards[i], h));
        }
        return r;
    }
    case INF_RCDSET: case INF_TIMES:
        r = sv_fcn(s->n, s->inf == INF_RCDSET);
        *g = L_TRUE;
        for (int i = 0; i < s->n; i++) {
            int h;
            SVal *v = sv_pick(s->u.inf.parts[i], &h);
            fcn_add(r, s->inf == INF_RCDSET ? sv_const(mk_str(s->u.inf.names[i])) : sv_int_const(i + 1), v, L_TRUE);
            *g = g_and(*g, h);
        }
        return r;
    case INF_MINUS:
        r = sv_pick(s->u.inf.parts[0], g);
        *g = g_and(*g, sv_in(r, s->u.inf.parts[1]) ^ 1);
        return r;
    case INF_FILTER:
        r = sv_pick(s->u.inf.parts[0], g);
        *g = g_and(*g, filter_holds(s, r));
        return r;
    default: break;
    }
    fail("Symbolic checking cannot choose an element of this set.");
}

/* The number of distinct elements of s: an element counts unless one
   before it is the same. */
static SVal *sv_card(SVal *s) {
    s = sv_enum(s);
    int *sum = bv_const(0);
    for (int i = 0; i < s->n; i++) {
        int c = s->u.set.guards[i];
        for (int j = 0; j < i && c != L_FALSE; j++)
            c = g_and(c, g_and(s->u.set.guards[j], sv_eq(s->u.set.elems[j], s->u.set.elems[i])) ^ 1);
        int *one = bv_const(0);
        one[0] = c;
        sum = bv_add(sum, one);
    }
    return sv_bits(SV_INT, sum);
}

/* The concrete value of s in the solver's model. */
static Value *sv_model(SVal *s) {
    Value **ks, **vs;
    int m = 0;
    int64_t u = 0;
    switch (s->kind) {
    case SV_CONST: return s->value;
    case SV_BOOL: return BOOLV(lit_true(s->u.lit));
    case SV_INT: case SV_ATOM:
        for (int i = 0; i < BW; i++) if (lit_true(s->u.bits[i])) u |= (int64_t)((uint64_t)1 << i);
        return s->kind == SV_INT ? mk_int(u) : atom_value(u);
    case SV_SET:
        vs = NEWN(Value *, s->n > 0 ? s->n : 1);
        for (int i = 0; i < s->n; i++) if (lit_true(s->u.set.guards[i])) vs[m++] = sv_model(s->u.set.elems[i]);
        return values_set(vs, m);
    case SV_FCN:
        ks = NEWN(Value *, s->n > 0 ? s->n : 1);
        vs = NEWN(Value *, s->n > 0 ? s->n : 1);
        for (int i = 0; i < s->n; i++) {
            if (!lit_true(s->u.fcn.guards[i])) continue;
            Value *k = sv_model(s->u.fcn.keys[i]);
            int dup = 0;
            for (int j = 0; j < m && !dup; j++) dup = veq(ks[j], k);
            if (!dup) { ks[m] = k; vs[m++] = sv_model(s->u.fcn.vals[i]); }
        }
        return values_fcn(ks, vs, m, s->rec);
    case SV_INF:
        if (s->inf == INF_INT) return mk_lazy(L_INT);
        if (s->inf == INF_NAT) return mk_lazy(L_NAT);
        return sv_model(sv_enum(s));
    default:
        fail("%s", s->u.err);
    }
}

/* ---------------------------------------------------------------- symbolic evaluation */

/* Evaluation follows the evaluator: a context binds names to concrete
   values, in an environment the evaluator reads, or to symbolic ones and
   unevaluated arguments, in a symbolic environment. An expression that
   reads no state and names nothing symbolic is evaluated by the
   evaluator. */
struct SEnv {
    Def *def;
    SVal *v;     /* its value, once known */
    Expr *e;     /* else the argument or definition body e in ctx */
    SCtx ctx;
    SEnv *next;
};

/* A call of a polymorphic operator a Gen depends on: a mark in the
   context of its body, back to the caller's (sym_typed). */
static SEnv *sym_typed(Expr *call, SCtx caller, SEnv *s);

static SVal **sym_cur;     /* the state being read */
static SVal **sym_next;    /* the next state as far as assigned */
static int sym_primed;     /* reading the next state */
static int sym_init;       /* an initial predicate: assigning unprimed variables */
static int sym_gen_step;   /* what makes the values of Gen: 0 Init, N the Nth step, -1 another */
static struct { Expr *e; int step; SVal *v; } *sym_gens;   /* those values, for the evaluator to replay */
static int nsym_gens;
static SVal *sym_at;       /* @ in an EXCEPT */
static Def **sym_consts;   /* the constants -cinit chooses */
static SVal **sym_const_vals;
static int nsym_consts;
static int sym_cinit;      /* the constant initializer: assigning constants */

static int sym_const_index(Def *d) {
    for (int i = 0; i < nsym_consts; i++) if (sym_consts[i] == d) return i;
    return -1;
}

enum { P_POS = 1, P_NEG = 2, P_BOTH = 3 };   /* where a formula is: under no negation, one, or either */

static SEnv *senv_find(SEnv *s, Def *d) {
    for (; s; s = s->next) if (s->def == d) return s;
    return NULL;
}

static SEnv *senv_bind(Def *d, SVal *v, Expr *e, SCtx ctx, SEnv *next) {
    SEnv *b = NEW(SEnv);
    b->def = d; b->v = v; b->e = e; b->ctx = ctx; b->next = next;
    return b;
}

/* What an expression names that a context may bind symbolically, and its
   level, found once. */
static Def at_mark;
typedef struct { Expr *e; int level, n; Def **defs; } ExprInfo;
static ExprInfo *infos;
static int ninfos, capinfos;

static void collect_names(Expr *e, Def ***defs, int *n, int *cap) {
    if (!e) return;
    Def *d = e->kind == K_BOUND || e->kind == K_PARAMCALL || (e->kind == K_CALL && e->def->local == 2) || (e->kind == K_DECL && e->def->kind == D_CONST) ? e->def
           : e->kind == X_AT ? &at_mark : NULL;
    if (d) {
        int i = 0;
        while (i < *n && (*defs)[i] != d) i++;
        if (i == *n) {
            if (*n == *cap) *defs = xrealloc(*defs, sizeof(Def *) * (size_t)(*cap = *cap ? 2 * *cap : 8));
            (*defs)[(*n)++] = d;
        }
    }
    for (int i = 0; i < e->n; i++) collect_names(e->args[i], defs, n, cap);
    for (int i = 0; i < e->nb; i++) collect_names(e->bounds[i].set, defs, n, cap);
    if (e->kind == X_EXCEPT)
        for (int i = 0; i < e->n - 1; i++)
            for (int k = 0; k < e->paths[i].n; k++) if (e->paths[i].fields[k] < 0) collect_names(e->paths[i].keys[k], defs, n, cap);
    if (e->kind == X_LET) for (int i = 0; i < e->ndefs; i++) collect_names(e->defs[i]->body, defs, n, cap);
    if (e->kind == X_LAMBDA) collect_names(e->def->body, defs, n, cap);
    for (int i = 0; i < e->nseg; i++)
        for (int k = 0; k < e->segs[i].n; k++) collect_names(e->segs[i].args[k], defs, n, cap);
}

static ExprInfo *expr_info(Expr *e);

/* Whether e reads no state (0), the state (1), or the next state too (2),
   3 for a temporal formula: from what it is made of, a native operator
   from its arguments only, as its definition is TLC's stub. */
/* A native whose value is not a function of its arguments: TLC's
   registers and the random choices. */
static int sym_impure(Native f) {
    return f == n_tlcget || f == n_tlcset || f == n_randomelement || f == n_randomsubset || f == n_randomsetofsubsets || f == n_javatime;
}

static int max_sym_level(Expr **es, int n);
static int def_sym_level(Def *d) {
    static Def *busy[256];
    static int nbusy;
    if (d->replacement) d = d->replacement;
    if (d->kind == D_VAR || (d->native && sym_impure(d->native)) || is_gen(d)) return 1;
    if (d->kind == D_INST) {
        int l = 0;
        for (int i = 0; i < d->nsubst; i++) if (d->subst_expr[i]->kind != X_OPREF) { int b = expr_info(d->subst_expr[i])->level; if (b > l) l = b; }
        return l;
    }
    if (d->kind == D_CONST) return sym_const_index(d) >= 0;   /* -cinit chooses it, as Init a variable */
    if (d->native || !d->body || d->kind == D_PARAM || d->kind == D_BOUND) return 0;
    for (int i = 0; i < nbusy; i++) if (busy[i] == d) return 0;
    if (nbusy == 256) return expr_level(d->body);
    busy[nbusy++] = d;
    int l = expr_info(d->body)->level;
    for (int i = 0; i < d->nb; i++) if (d->bounds[i].set) { int b = expr_info(d->bounds[i].set)->level; if (b > l) l = b; }
    nbusy--;
    return l;
}

static int max_sym_level(Expr **es, int n) {
    int l = 0;
    for (int i = 0; i < n; i++) if (es[i]) { int a = expr_info(es[i])->level; if (a > l) l = a; }
    return l;
}

static int sym_level(Expr *e) {
    int l = max_sym_level(e->args, e->n);
    for (int i = 0; i < e->nb; i++) if (e->bounds[i].set) { int b = expr_info(e->bounds[i].set)->level; if (b > l) l = b; }
    if (e->kind == X_EXCEPT)
        for (int i = 0; i < e->n - 1; i++)
            for (int k = 0; k < e->paths[i].n; k++) if (e->paths[i].fields[k] < 0) { int b = expr_info(e->paths[i].keys[k])->level; if (b > l) l = b; }
    for (int i = 0; i < e->nseg; i++) { int b = max_sym_level(e->segs[i].args, e->segs[i].n); if (b > l) l = b; }
    int own = 0;
    switch (e->kind) {
    case K_DECL: own = e->def->kind == D_VAR || (e->def->kind == D_CONST && sym_const_index(e->def) >= 0); break;
    case K_PRIME: case K_UNCHANGED: case X_SQACT: case X_ANGLEACT: case K_CDOT: own = 2; break;
    case K_ENABLED: return 1;
    case K_ALWAYS: case K_EVENTUALLY: case K_LEADSTO: case X_WF: case X_SF: case K_WHILE: case X_TFORALL: case X_TEXISTS: own = 3; break;
    case K_CALL: own = def_sym_level(e->def); break;
    case K_INSTCALL:
        own = def_sym_level(e->def);
        for (int i = 0; i < e->ndefs; i++) { int d = def_sym_level(e->defs[i]); if (d > own) own = d; }
        break;
    case X_LET: for (int i = 0; i < e->ndefs; i++) { int d = def_sym_level(e->defs[i]); if (d > own) own = d; } break;
    case X_LAMBDA: own = expr_info(e->def->body)->level; break;
    case X_OPREF: own = def_sym_level(e->def); break;
    default: break;
    }
    return own > l ? own : l;
}

static ExprInfo *info_slot(Expr *e) {
    int j = (int)(fmix((uint64_t)(uintptr_t)e) & (uint64_t)(capinfos - 1));
    while (infos[j].e && infos[j].e != e) j = (j + 1) & (capinfos - 1);
    return &infos[j];
}

static ExprInfo *expr_info(Expr *e) {
    if (capinfos) { ExprInfo *in = info_slot(e); if (in->e) return in; }
    /* Computed before it is stored: computing it stores others. */
    int cap = 0;
    ExprInfo in = {e, sym_level(e), 0, NULL};
    collect_names(e, &in.defs, &in.n, &cap);
    if (2 * (ninfos + 1) > capinfos) {
        int size = capinfos ? 2 * capinfos : 1 << 12;
        ExprInfo *old = infos;
        int oldcap = capinfos;
        infos = xcalloc((size_t)size, sizeof(ExprInfo));
        capinfos = size;
        for (int i = 0; i < oldcap; i++) if (old[i].e) *info_slot(old[i].e) = old[i];
        free(old);
    }
    ExprInfo *slot = info_slot(e);
    if (!slot->e) { *slot = in; ninfos++; }
    return slot;
}

/* Whether the evaluator can evaluate e in sc: e reads no state and
   names nothing sc binds symbolically. */
static int sym_plain(Expr *e, SCtx sc) {
    ExprInfo *in = expr_info(e);
    if (in->level) return 0;
    for (int i = 0; i < in->n; i++) {
        Def *d = in->defs[i];
        if (d == &at_mark) { if (!sym_at || !sv_known(sym_at)) return 0; }
        else if (d->kind == D_CONST) {   /* an instance's, substituted */
            Ctx c = sc.c;
            Expr *x = sc.c.inst ? substitute(d, &c) : NULL;
            if (x && x->kind != X_OPREF && !sym_plain(x, (SCtx){c, NULL})) return 0;
        }
        else if (sc.s && senv_find(sc.s, d)) return 0;
    }
    return 1;
}

/* Runs the evaluator on e: an error makes an undefined value. */
static SVal *sym_plain_eval(Expr *e, Ctx c) {
    EvalState es = eval_save();
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) { eval_restore(es); return sv_undef(); }
    cur_state = next_state = NULL;
    primed = gen_init = 0;
    if (sym_at) at_value = sv_known(sym_at);
    Value *v = eval(e, c);
    eval_restore(es);
    return sv_const(v);
}

static SVal *sym(Expr *e, SCtx sc, int pol);
static SVal *sym_enabled(Expr *e, SCtx sc);
static int sym_bool(Expr *e, SCtx sc, int pol) { return sv_lit(sym(e, sc, pol), e); }

static SVal *senv_force(SEnv *b) {
    if (b->v) return b->v;
    int keep = !sym_primed && !sym_init && expr_info(b->e)->level < 2;
    SVal *v = sym(b->e, b->ctx, P_BOTH);
    if (keep) b->v = v;
    return v;
}

static SCtx sym_bind(SCtx sc, Def *d, SVal *v) {
    Value *k = sv_known(v);
    if (k && k->kind != V_LAZY) sc.c.env = mk_binding(d, k, sc.c.env);
    else sc.s = senv_bind(d, v, NULL, sc, sc.s);
    return sc;
}

/* Binds d's parameters to args, written in caller, into inner. */
/* Whether x satisfies the predicate of the filter s. */
static int filter_holds(SVal *s, SVal *x) {
    struct Filter *f = s->u.inf.filter;
    return sym_bool(f->e->args[0], sym_bind(f->sc, f->e->bounds[0].defs[0], x), P_BOTH);
}

static SCtx sym_bind_args(Def *d, Expr **args, int n, SCtx caller, SCtx inner) {
    for (int i = 0; i < n && i < d->nparams; i++) {
        Def *p = d->params[i];
        if (sym_plain(args[i], caller))
            inner.c.env = p->arity ? mk_binding(p, eval_operator_arg(args[i], caller.c), inner.c.env)
                                   : mk_arg(p, args[i], caller.c, inner.c.env);
        else inner.s = senv_bind(p, NULL, args[i], caller, inner.s);
    }
    return inner;
}

static SVal *sym_native(Def *d, Expr **args, int n, SCtx sc, Expr *call);
static SVal *sym_fcndef(Def *d, SCtx sc);

static SVal *sym_oper(Value *v, Expr **args, int n, SCtx sc, Expr *call, int pol);

/* The operator argument d, bound in at, applied to args written in sc. */
static SVal *sym_call(Def *d, Expr **args, int n, SCtx sc, SCtx at, Expr *call, int pol);
static SVal *sym_param_call(Def *d, Expr **args, int n, SCtx sc, SCtx at, Expr *call, int pol) {
    SEnv *b = senv_find(at.s, d);
    if (b) {
        Expr *op = b->e;
        if (op && (op->kind == X_LAMBDA || ((op->kind == K_CALL || op->kind == K_PARAMCALL) && op->n == 0)))
            return sym_call(op->def, args, n, sc, b->ctx, call, pol);
        fail_at(call, "Symbolic checking cannot apply this operator argument.");
    }
    Env *cb = env_find(at.c.env, d);
    if (!cb) fail_at(call, "Unbound operator parameter %s.", S(d->name));
    return sym_oper(force(cb), args, n, sc, call, pol);
}

/* The operator value v applied to args written in sc. */
static SVal *sym_oper(Value *v, Expr **args, int n, SCtx sc, Expr *call, int pol) {
    if (v->kind != V_OPER || v->u.op.table) fail_at(call, "Symbolic checking cannot apply this operator.");
    Def *od = v->u.op.def->replacement ? v->u.op.def->replacement : v->u.op.def;
    SCtx oc = {{v->u.op.env, v->u.op.inst}, NULL};
    if (od->local == 2 && !od->native) { Env *lb = env_find(oc.c.env, od); if (lb) oc.c.env = lb->ctx_env; }
    return sym_call(od, args, n, sc, oc, call, pol);
}

/* The operator argument op, written in sc, applied to the n values xs. */
static SVal *sym_apply_op(Expr *op, SCtx sc, SVal **xs, int n, Expr *call) {
    Expr **args = NEWN(Expr *, n);
    SCtx at = sc;
    for (int i = 0; i < n; i++) {
        Def *d = NEW(Def);
        d->kind = D_BOUND;
        args[i] = NEW(Expr);
        args[i]->kind = K_BOUND;
        args[i]->def = d;
        at.s = senv_bind(d, xs[i], NULL, sc, at.s);
    }
    if (op->kind == X_LAMBDA) return sym_call(op->def, args, n, at, sc, call, P_BOTH);
    if (!sym_plain(op, sc)) fail_at(call, "Symbolic checking cannot apply this operator argument.");
    return sym_oper(eval_operator_arg(op, sc.c), args, n, at, call, P_BOTH);
}

/* Apalache's ApaFoldSet(Op, v, S) on a set not yet known: Op folds in
   each element present and not the same as one present before it. */
static SVal *sym_fold_set(Expr **args, SCtx sc, Expr *call) {
    SVal *acc = sym(args[1], sc, P_BOTH), *s = sv_enum(sym(args[2], sc, P_BOTH));
    for (int i = 0; i < s->n; i++) {
        int c = s->u.set.guards[i];
        for (int j = 0; j < i && c != L_FALSE; j++)
            c = g_and(c, g_and(s->u.set.guards[j], sv_eq(s->u.set.elems[j], s->u.set.elems[i])) ^ 1);
        if (c == L_FALSE) continue;
        SVal *xs[2] = {acc, s->u.set.elems[i]};
        acc = sv_ite(c, sym_apply_op(args[0], sc, xs, 2, call), acc);
    }
    return acc;
}

/* The context a definition's body is evaluated in, before its parameters:
   a LET definition's closure; *forced its value, for one without them. */
static SCtx def_ctx(Def *d, SCtx sc, Expr *call, SVal **forced, int pol) {
    SCtx inner = {{NULL, sc.c.inst}, NULL};
    *forced = NULL;
    if (d->local != 2) return inner;
    SEnv *b = senv_find(sc.s, d);
    Env *cb = b ? NULL : env_find(sc.c.env, d);
    if (!b && !cb) fail_at(call, "Unbound LET definition %s.", S(d->name));
    inner = b ? b->ctx : (SCtx){{cb->ctx_env, cb->ctx_inst}, NULL};
    if (!d->nparams && d->kind != D_FCN) *forced = b ? senv_force(b) : sym(d->body, inner, pol);
    return inner;
}

/* d, named in at, applied to args written in sc. */
static SVal *sym_call(Def *d, Expr **args, int n, SCtx sc, SCtx at, Expr *call, int pol) {
    if (d->replacement) d = d->replacement;
    if (d->native) return sym_native(d, args, n, sc, call);
    if (d->kind == D_PARAM) return sym_param_call(d, args, n, sc, at, call, pol);
    if (is_fold_set(d) && !sym_plain(args[2], sc)) return sym_fold_set(args, sc, call);
    SVal *forced;
    SCtx inner = def_ctx(d, at, call, &forced, pol);
    if (forced) return forced;
    if (d->kind == D_FCN) return sym_fcndef(d, inner);
    if (d->kind != D_OP && d->kind != D_RECURSIVE) fail_at(call, "Symbolic checking cannot evaluate %s.", S(d->name));
    inner.s = sym_typed(call, sc, inner.s);
    inner = sym_bind_args(d, args, n, sc, inner);
    deeper();
    SVal *v = sym(d->body, inner, pol);
    eval_depth--;
    return v;
}

/* A bound name's or binding's value in sc. */
static SVal *sym_bound(Def *d, SCtx sc, Expr *where) {
    SEnv *b = senv_find(sc.s, d);
    if (b) return senv_force(b);
    SVal *v = sym_plain_eval(where, sc.c);
    Env *arg = v->kind == SV_UNDEF ? env_find(sc.c.env, d) : NULL;
    if (arg && arg->e) return sym(arg->e, (SCtx){{arg->ctx_env, arg->ctx_inst}, NULL}, P_BOTH);   /* the argument, by its parts */
    return v;
}

/* A constant's or variable's value in sc, through the substitutions of
   the instances sc is in. */
static SVal *sym_decl(Def *d, SCtx sc, Expr *where) {
    int k = d->kind == D_CONST ? sym_const_index(d) : -1;
    if (k >= 0) {
        SVal *v = sym_cinit ? sym_next[k] : sym_const_vals[k];
        if (!v) fail_at(where, "In evaluation, the identifier %s is either undefined or not an operator.", S(d->name));
        return v;
    }
    if (d->kind == D_VAR && d->var_index >= 0) {
        SVal *v = sym_primed ? sym_next[d->var_index] : sym_cur[d->var_index];
        if (!v) fail_at(where, "In evaluation, the identifier %s is either undefined or not an operator.", S(d->name));
        return v;
    }
    Ctx c = sc.c;
    Expr *x = substitute(d, &c);
    if (x && x->kind == X_OPREF && x->def->kind == D_CONST) return sym_decl(x->def, (SCtx){c, NULL}, where);
    if (!x || x->kind == X_OPREF) return sym_plain_eval(where, sc.c);
    return sym(x, (SCtx){c, NULL}, P_BOTH);
}

/* The instances an instance call goes through. */
static Inst *sym_instance(Expr *e, SCtx sc) {
    for (int i = 0; i < e->nseg; i++)
        for (int k = 0; k < e->segs[i].n; k++)
            if (!sym_plain(e->segs[i].args[k], sc)) fail_at(e, "Symbolic checking cannot instantiate a module with arguments of the state.");
    return instance_chain(e, sc.c);
}

/* Calls fn for each binding of the bounds, in sc; key is the element
   bound, a tuple of them for several. */
typedef void (*SBindFn)(SCtx inner, int guard, SVal *key, void *data);

static void sym_bindings(Bound *bs, int nb, SVal **given, SCtx sc, SBindFn fn, void *data, Expr *where) {
    int nslots = 0;
    for (int i = 0; i < nb; i++) nslots += bs[i].tuple ? 1 : bs[i].n;
    SVal **sets = NEWN(SVal *, nslots);
    Bound **of = NEWN(Bound *, nslots);
    int *name = NEWN(int, nslots), *at = NEWN(int, nslots);
    for (int i = 0, k = 0; i < nb; i++) {
        if (!bs[i].set) fail_at(where, "Symbolic checking cannot handle an unbounded quantifier.");
        SVal *s = sv_enum(given ? given[i] : sym(bs[i].set, sc, P_BOTH));
        for (int j = 0; j < (bs[i].tuple ? 1 : bs[i].n); j++, k++) { sets[k] = s; of[k] = &bs[i]; name[k] = j; }
    }
    for (int k = 0; k < nslots; k++) if (!sets[k]->n) return;
    for (;;) {
        SCtx inner = sc;
        int g = L_TRUE;
        SVal *key = nslots == 1 ? sets[0]->u.set.elems[at[0]] : sv_fcn(nslots, 0);
        for (int k = 0; k < nslots; k++) {
            SVal *e = sets[k]->u.set.elems[at[k]];
            g = g_and(g, sets[k]->u.set.guards[at[k]]);
            if (nslots > 1) fcn_add(key, sv_int_const(k + 1), e, L_TRUE);
            if (!of[k]->tuple) { inner = sym_bind(inner, of[k]->defs[name[k]], e); continue; }
            for (int m = 0; m < of[k]->n; m++) inner = sym_bind(inner, of[k]->defs[m], sv_apply(e, sv_int_const(m + 1)));
        }
        if (g != L_FALSE) fn(inner, g, key, data);
        int k = nslots - 1;
        while (k >= 0 && ++at[k] == sets[k]->n) at[k--] = 0;
        if (k < 0) return;
    }
}

typedef struct { Expr *body; int pol, exists, value; SVal *out; } SQuant;

static void sym_quant_fn(SCtx inner, int g, SVal *key, void *data) {
    (void)key;
    SQuant *q = data;
    if (q->value == (q->exists ? L_TRUE : L_FALSE)) return;
    int b = sym_bool(q->body, inner, q->pol);
    q->value = q->exists ? g_or(q->value, g_and(g, b)) : g_and(q->value, g_implies(g, b));
}

static void sym_filter_fn(SCtx inner, int g, SVal *key, void *data) {
    SQuant *q = data;
    set_add(q->out, key, g_and(g, sym_bool(q->body, inner, P_BOTH)));
}

static void sym_map_fn(SCtx inner, int g, SVal *key, void *data) {
    (void)key;
    SQuant *q = data;
    set_add(q->out, sym(q->body, inner, P_BOTH), g);
}

static void sym_fcn_fn(SCtx inner, int g, SVal *key, void *data) {
    SQuant *q = data;
    fcn_add(q->out, key, sym(q->body, inner, P_BOTH), g);
}

/* The number of bindings the bounds have, -1 if a set is not finite. */
static int64_t bindings_count(Bound *bs, int nb, SCtx sc, SVal **sets) {
    int64_t total = 1;
    for (int i = 0; i < nb; i++) {
        if (!bs[i].set) return -1;
        SVal *s = sv_open(sets[i] = sym(bs[i].set, sc, P_BOTH));
        if (s->kind != SV_SET) return -1;
        for (int j = 0; j < (bs[i].tuple ? 1 : bs[i].n); j++) if ((total *= s->n) > 1 << 20) return -1;
    }
    return total;
}

/* The elements chosen for each \E, for the evaluator to replay it with. */
static struct { Expr *e; int step; SVal **vals; } *sym_witnesses;
static int nsym_witnesses;

/* Binds each name of q's bounds to a fresh element of its set: *g whether
   they are. */
static SCtx sym_skolem(Expr *q, SCtx sc, SVal **sets, int *g) {
    Bound *bs = q->bounds;
    int nb = q->nb;
    SVal **w = NULL;
    *g = L_TRUE;
    if (q->kind == X_EXISTS) {
        sym_witnesses = xrealloc(sym_witnesses, sizeof *sym_witnesses * (size_t)(nsym_witnesses + 1));
        sym_witnesses[nsym_witnesses].e = q;
        sym_witnesses[nsym_witnesses].step = sym_gen_step;
        sym_witnesses[nsym_witnesses++].vals = w = NEWN(SVal *, bounds_total(bs, nb));
    }
    for (int i = 0; i < nb; i++)
        for (int j = 0; j < (bs[i].tuple ? 1 : bs[i].n); j++) {
            int h;
            SVal *e = sv_pick(sets[i], &h);
            if (w) *w++ = e;
            *g = g_and(*g, h);
            if (!bs[i].tuple) { sc = sym_bind(sc, bs[i].defs[j], e); continue; }
            for (int m = 0; m < bs[i].n; m++) sc = sym_bind(sc, bs[i].defs[m], sv_apply(e, sv_int_const(m + 1)));
        }
    return sc;
}

static SVal *sym_quant(Expr *e, SCtx sc, int pol) {
    int exists = e->kind == X_EXISTS;
    SVal **sets = NEWN(SVal *, e->nb);
    int64_t n = bindings_count(e->bounds, e->nb, sc, sets);
    if ((n < 0 || n > 64) && pol == (exists ? P_POS : P_NEG)) {   /* \E as a witness, as Apalache skolemizes */
        int g;
        for (int i = 0; i < e->nb; i++) if (!e->bounds[i].set) fail_at(e, "Symbolic checking cannot handle an unbounded quantifier.");
        SCtx inner = sym_skolem(e, sc, sets, &g);
        int b = sym_bool(e->args[0], inner, pol);
        return sv_bool(exists ? g_and(g, b) : g_implies(g, b));
    }
    SQuant q = {e->args[0], pol, exists, exists ? L_FALSE : L_TRUE, NULL};
    sym_bindings(e->bounds, e->nb, sets, sc, sym_quant_fn, &q, e);
    return sv_bool(q.value);
}

/* CHOOSE x \in S : P, an element that satisfies P if one does. */
static SVal *sym_choose(Expr *e, SCtx sc) {
    Bound *b = &e->bounds[0];
    if (!b->set) fail_at(e, "Symbolic checking cannot handle an unbounded CHOOSE.");
    SVal *set = sym(b->set, sc, P_BOTH);
    int g;
    SVal *x = sv_pick(set, &g);
    SCtx inner = sc;
    if (!b->tuple) inner = sym_bind(inner, b->defs[0], x);
    else for (int m = 0; m < b->n; m++) inner = sym_bind(inner, b->defs[m], sv_apply(x, sv_int_const(m + 1)));
    int holds = g_and(g, sym_bool(e->args[0], inner, P_BOTH));
    SQuant q = {e->args[0], P_BOTH, 1, L_FALSE, NULL};
    sym_bindings(b, 1, &set, sc, sym_quant_fn, &q, e);
    sat_add2(q.value ^ 1, holds);
    return x;
}

static SVal *sym_set_op(Expr *e, SVal *a, SVal *b) {
    if (a->kind == SV_UNDEF) return a;
    if (b->kind == SV_UNDEF) return b;
    if (e->kind == K_SUBSETEQ) return sv_bool(sv_subseteq(a, b));
    if (sv_open(a)->kind == SV_INF && e->kind != K_CUP) {   /* infinite, or too large to list */
        if (e->kind == K_CAP && sv_open(b)->kind == SV_SET) return sym_set_op(e, b, a);
        if (e->kind == K_SETMINUS) {
            SVal *r = sv_inf(INF_MINUS, 2);
            r->u.inf.parts[0] = a;
            r->u.inf.parts[1] = b;
            return r;
        }
    }
    a = sv_enum(a);
    SVal *r;
    if (e->kind == K_CUP) {
        b = sv_enum(b);
        r = sv_set(a->n + b->n);
        for (int i = 0; i < a->n; i++) set_add(r, a->u.set.elems[i], a->u.set.guards[i]);
        for (int i = 0; i < b->n; i++) set_join(r, b->u.set.elems[i], b->u.set.guards[i]);
        return r;
    }
    r = sv_set(a->n);
    for (int i = 0; i < a->n; i++)
        set_add(r, a->u.set.elems[i], g_and(a->u.set.guards[i], sv_in(a->u.set.elems[i], b) ^ (e->kind == K_SETMINUS)));
    return r;
}

static SVal *sym_union(SVal *s) {
    s = sv_enum(s);
    int n = 0;
    SVal **parts = NEWN(SVal *, s->n > 0 ? s->n : 1);
    for (int i = 0; i < s->n; i++) n += (parts[i] = sv_enum(s->u.set.elems[i]))->n;
    SVal *r = sv_set(n);
    for (int i = 0; i < s->n; i++)
        for (int j = 0; j < parts[i]->n; j++) set_join(r, parts[i]->u.set.elems[j], g_and(s->u.set.guards[i], parts[i]->u.set.guards[j]));
    return r;
}

static SVal *sym_except_path(SVal *f, Path *p, int k, Expr *val, SCtx sc) {
    SVal *key = p->fields[k] >= 0 ? sv_const(mk_str(p->fields[k])) : sym(p->keys[k], sc, P_BOTH);
    SVal *old = sv_apply(f, key), *nv;
    if (k + 1 < p->n) nv = sym_except_path(old, p, k + 1, val, sc);
    else {
        SVal *saved = sym_at;
        sym_at = old;
        nv = sym(val, sc, P_BOTH);
        sym_at = saved;
    }
    return sv_update(f, key, nv);
}

static SVal *sym_fcndef(Def *d, SCtx sc) {
    if (d->self) fail("Symbolic checking cannot evaluate the recursive function %s on symbolic values.", S(d->name));
    SVal **sets = NEWN(SVal *, d->nb);
    int64_t n = bindings_count(d->bounds, d->nb, sc, sets);
    if (n < 0) fail("Symbolic checking cannot make the function %s over an infinite domain.", S(d->name));
    SQuant q = {d->body, P_BOTH, 0, 0, sv_fcn((int)n, 0)};
    sym_bindings(d->bounds, d->nb, sets, sc, sym_fcn_fn, &q, d->where);
    return q.out;
}

static SCtx let_ctx(Expr *e, SCtx sc) {
    /* A definition is bound for the evaluator unless it names what is
       bound symbolically, or another definition that does. */
    char *symbolic = NEWN(char, e->ndefs);
    for (int changed = 1; changed;) {
        changed = 0;
        for (int i = 0; i < e->ndefs; i++) {
            if (symbolic[i]) continue;
            ExprInfo *in = expr_info(e->defs[i]->body);
            for (int k = 0; k < in->n && !symbolic[i]; k++) {
                Def *x = in->defs[k];
                if (x == &at_mark) symbolic[i] = sym_at != NULL;
                else if (sc.s && senv_find(sc.s, x)) symbolic[i] = 1;
                for (int j = 0; j < e->ndefs && !symbolic[i]; j++) symbolic[i] = symbolic[j] && e->defs[j] == x;
            }
            changed |= symbolic[i];
        }
    }
    SCtx inner = sc;
    for (int i = 0; i < e->ndefs; i++)
        if (symbolic[i]) inner.s = senv_bind(e->defs[i], NULL, e->defs[i]->body, sc, inner.s);
        else inner.c.env = mk_thunk(e->defs[i], e->defs[i]->body, sc.c, inner.c.env);
    for (Env *b = inner.c.env; b != sc.c.env; b = b->next) b->ctx_env = inner.c.env;
    for (SEnv *b = inner.s; b != sc.s; b = b->next) b->ctx = inner;
    return inner;
}

static SVal *seq_len(SVal *s);

static SVal *sym_parts(Expr *e, SCtx sc, int pol);
static SVal *sym_gen(Expr *e, SCtx sc);

/* Where the evaluator fails on e, only the part of e that fails is
   undefined, as Apalache has it, and e has one meaning in its context
   however often it is met: the first. */
static SVal *sym(Expr *e, SCtx sc, int pol) {
    static struct { Expr *e; Ctx c; SVal *v; } *failed;
    static int nfailed;
    if (!sym_plain(e, sc)) return sym_parts(e, sc, pol);
    SVal *v = sym_plain_eval(e, sc.c);
    if (v->kind != SV_UNDEF) return v;
    for (int i = 0; i < nfailed; i++)
        if (failed[i].e == e && failed[i].c.env == sc.c.env && failed[i].c.inst == sc.c.inst) return failed[i].v;
    v = sym_parts(e, sc, pol);
    failed = xrealloc(failed, sizeof *failed * (size_t)(nfailed + 1));
    failed[nfailed].e = e, failed[nfailed].c = sc.c, failed[nfailed++].v = v;
    return v;
}

static SVal *sym_parts(Expr *e, SCtx sc, int pol) {
    SVal *a, *b, *r;
    int l;
    switch (e->kind) {
    case K_BOUND: return sym_bound(e->def, sc, e);
    case K_DECL: return sym_decl(e->def, sc, e);
    case K_CALL: case K_PARAMCALL:
        if (e->def->kind == D_VAR) return sym_decl(e->def, sc, e);
        if (is_gen(e->def)) return sym_gen(e, sc);
        return sym_call(e->def, e->args, e->n, sc, sc, e, pol);
    case K_INSTCALL: {
        Def *d = e->def;
        if (is_gen(d)) return sym_gen(e, sc);
        if (d->replacement) return sym_call(d, e->args, e->n, sc, sc, e, pol);
        SCtx at = {{NULL, sym_instance(e, sc)}, NULL};
        if (d->kind == D_CONST || d->kind == D_VAR) return sym_decl(d, at, e);
        return sym_call(d, e->args, e->n, sc, at, e, pol);
    }
    case K_AND: case K_OR: {
        int and = e->kind == K_AND;
        l = and ? L_TRUE : L_FALSE;
        for (int i = 0; i < e->n && l != (and ? L_FALSE : L_TRUE); i++)
            l = and ? g_and(l, sym_bool(e->args[i], sc, pol)) : g_or(l, sym_bool(e->args[i], sc, pol));
        return sv_bool(l);
    }
    case K_NOT: return sv_bool(sym_bool(e->args[0], sc, pol ^ (pol == P_BOTH ? 0 : 3)) ^ 1);
    case K_IMPLIES:
        l = sym_bool(e->args[0], sc, pol ^ (pol == P_BOTH ? 0 : 3));
        return sv_bool(l == L_FALSE ? L_TRUE : g_implies(l, sym_bool(e->args[1], sc, pol)));
    case K_EQUIV: return sv_bool(g_iff(sym_bool(e->args[0], sc, P_BOTH), sym_bool(e->args[1], sc, P_BOTH)));
    case K_EQ: case K_NEQ:
        l = sv_eq(sym(e->args[0], sc, P_BOTH), sym(e->args[1], sc, P_BOTH));
        return sv_bool(e->kind == K_EQ ? l : l ^ 1);
    case K_IN: case K_NOTIN:
        l = sv_in(sym(e->args[0], sc, P_BOTH), sym(e->args[1], sc, P_BOTH));
        return sv_bool(e->kind == K_IN ? l : l ^ 1);
    case K_CUP: case K_CAP: case K_SETMINUS: case K_SUBSETEQ:
        return sym_set_op(e, sym(e->args[0], sc, P_BOTH), sym(e->args[1], sc, P_BOTH));
    case K_SUBSET: r = sv_inf(INF_SUBSET, 1); r->u.inf.parts[0] = sym(e->args[0], sc, P_BOTH); return r;
    case K_UNION: return sym_union(sym(e->args[0], sc, P_BOTH));
    case K_DOMAIN: return sv_domain(sym(e->args[0], sc, P_BOTH));
    case K_PRIME: {
        int saved = sym_primed;   /* in the initial predicate, as Apalache, x' is x */
        sym_primed = 1;
        r = sym(e->args[0], sc, pol);
        sym_primed = saved;
        return r;
    }
    case K_UNCHANGED: {
        a = sym(e->args[0], sc, P_BOTH);
        int saved = sym_primed;
        sym_primed = 1;
        b = sym(e->args[0], sc, P_BOTH);
        sym_primed = saved;
        return sv_bool(sv_eq(a, b));
    }
    case X_SQACT: case X_ANGLEACT: {
        int sq = e->kind == X_SQACT;
        l = sym_bool(e->args[0], sc, pol);
        a = sym(e->args[1], sc, P_BOTH);
        int saved = sym_primed;
        sym_primed = 1;
        b = sym(e->args[1], sc, P_BOTH);
        sym_primed = saved;
        int same = sv_eq(a, b);
        return sv_bool(sq ? g_or(l, same) : g_and(l, same ^ 1));
    }
    case K_TIMES:
        r = sv_inf(INF_TIMES, e->n);
        for (int i = 0; i < e->n; i++) r->u.inf.parts[i] = sym(e->args[i], sc, P_BOTH);
        return r;
    case X_SETENUM:
        r = sv_set(e->n);
        for (int i = 0; i < e->n; i++) set_add(r, sym(e->args[i], sc, P_BOTH), L_TRUE);
        return r;
    case X_TUPLE:
        r = sv_fcn(e->n, 0);
        for (int i = 0; i < e->n; i++) fcn_add(r, sv_int_const(i + 1), sym(e->args[i], sc, P_BOTH), L_TRUE);
        return r;
    case X_RECORD:
        r = sv_fcn(e->n, 1);
        for (int i = 0; i < e->n; i++) fcn_add(r, sv_const(mk_str(e->segs[i].name)), sym(e->args[i], sc, P_BOTH), L_TRUE);
        return r;
    case X_RCDSET:
        r = sv_inf(INF_RCDSET, e->n);
        for (int i = 0; i < e->n; i++) { r->u.inf.names[i] = e->segs[i].name; r->u.inf.parts[i] = sym(e->args[i], sc, P_BOTH); }
        return r;
    case X_FCNSET:
        r = sv_inf(INF_FCNSET, 2);
        r->u.inf.parts[0] = sym(e->args[0], sc, P_BOTH);
        r->u.inf.parts[1] = sym(e->args[1], sc, P_BOTH);
        return r;
    case X_FCN: {
        SVal **sets = NEWN(SVal *, e->nb);
        int64_t n = bindings_count(e->bounds, e->nb, sc, sets);
        if (n < 0) fail_at(e, "Symbolic checking cannot make a function over an infinite domain.");
        SQuant q = {e->args[0], P_BOTH, 0, 0, sv_fcn((int)n, 0)};
        sym_bindings(e->bounds, e->nb, sets, sc, sym_fcn_fn, &q, e);
        return q.out;
    }
    case X_APPLY:
        a = sym(e->args[0], sc, P_BOTH);
        if (e->n == 2) b = sym(e->args[1], sc, P_BOTH);
        else {
            b = sv_fcn(e->n - 1, 0);
            for (int i = 1; i < e->n; i++) fcn_add(b, sv_int_const(i), sym(e->args[i], sc, P_BOTH), L_TRUE);
        }
        return sv_apply(a, b);
    case X_DOT: return sv_apply(sym(e->args[0], sc, P_BOTH), sv_const(mk_str(e->op)));
    case X_EXCEPT:
        r = sym(e->args[0], sc, P_BOTH);
        for (int i = 0; i < e->n - 1; i++) r = sym_except_path(r, &e->paths[i], 0, e->args[i + 1], sc);
        return r;
    case X_AT:
        if (!sym_at) fail_at(e, "@ outside an EXCEPT.");
        return sym_at;
    case X_FILTER: case X_MAP: {
        SVal **sets = NEWN(SVal *, e->nb);
        int64_t n = bindings_count(e->bounds, e->nb, sc, sets);
        if (n < 0 && e->kind == X_FILTER && e->nb == 1 && e->bounds[0].n == 1 && !e->bounds[0].tuple) {   /* of an infinite set: as it is */
            r = sv_inf(INF_FILTER, 1);
            r->u.inf.parts[0] = sets[0];
            r->u.inf.filter = NEW(struct Filter);
            *r->u.inf.filter = (struct Filter){e, sc};
            return r;
        }
        if (n < 0) fail_at(e, "Symbolic checking cannot make a set from an infinite one.");
        SQuant q = {e->args[0], P_BOTH, 0, 0, sv_set((int)n)};
        sym_bindings(e->bounds, e->nb, sets, sc, e->kind == X_FILTER ? sym_filter_fn : sym_map_fn, &q, e);
        return q.out;
    }
    case X_FORALL: case X_EXISTS: return sym_quant(e, sc, pol);
    case X_CHOOSE: return sym_choose(e, sc);
    case X_IF:
        l = sym_bool(e->args[0], sc, P_BOTH);
        if (l == L_TRUE) return sym(e->args[1], sc, pol);
        if (l == L_FALSE) return sym(e->args[2], sc, pol);
        return sv_ite(l, sym(e->args[1], sc, pol), sym(e->args[2], sc, pol));
    case X_CASE: {
        int last = e->n - 2;
        r = NULL;
        if (!e->args[last]) { r = sym(e->args[last + 1], sc, pol); last -= 2; }
        for (int i = last; i >= 0; i -= 2) {
            SVal *v = sym(e->args[i + 1], sc, pol);
            r = r ? sv_ite(sym_bool(e->args[i], sc, P_BOTH), v, r) : v;
        }
        return r;
    }
    case X_LET: return sym(e->args[0], let_ctx(e, sc), pol);
    case K_ENABLED: return sym_enabled(e, sc);
    default: break;
    }
    if (expr_info(e)->level >= 3) fail_at(e, "Symbolic checking does not check temporal formulas.");
    fail_at(e, "Symbolic checking does not support this expression.");
}

/* ---------------------------------------------------------------- symbolic operators */

/* The words of a sequence's positions 1..n, with their guards; fails
   unless its keys are integers known. */
static SVal *seq_open(SVal *s, SVal ***vals, int **guards, int *n, Expr *where) {
    s = sv_open(s);
    if (s->kind != SV_FCN) fail_at(where, "Symbolic checking expected a sequence, but has %s.", class_name(sv_class(s)));
    int64_t max = 0, k;
    for (int i = 0; i < s->n; i++) {
        Value *key = sv_known(s->u.fcn.keys[i]);
        if (!key || key->kind != V_INT || (k = key->u.i) < 1) fail_at(where, "Symbolic checking cannot use a function as a sequence unless its domain is 1..n.");
        if (k > max) max = k;
    }
    *n = (int)max;
    *vals = NEWN(SVal *, max > 0 ? max : 1);
    *guards = NEWN(int, max > 0 ? max : 1);
    for (int i = 0; i < max; i++) (*guards)[i] = L_FALSE;
    for (int i = 0; i < s->n; i++) {
        int at = (int)sv_known(s->u.fcn.keys[i])->u.i - 1;
        (*vals)[at] = s->u.fcn.vals[i];
        (*guards)[at] = s->u.fcn.guards[i];
    }
    for (int i = 0; i < max; i++) if (!(*vals)[i]) (*vals)[i] = s->n ? s->u.fcn.vals[0] : NULL;
    return s;
}

static SVal *seq_len(SVal *s) {
    SVal **v;
    int *g, n;
    seq_open(s, &v, &g, &n, NULL);
    int *sum = bv_const(0);
    for (int i = 0; i < n; i++) { int *one = bv_const(0); one[0] = g[i]; sum = bv_add(sum, one); }
    return sv_bits(SV_INT, sum);
}

static SVal *seq_make(SVal **v, int *g, int n) {
    SVal *r = sv_fcn(n, 0);
    for (int i = 0; i < n; i++) fcn_add(r, sv_int_const(i + 1), v[i], g[i]);
    return r;
}

/* The elements of s that test, an operator argument, keeps: the one at j
   is the element i kept with j kept before it. */
static SVal *seq_select(SVal *s, Expr *test, SCtx sc, Expr *call) {
    SVal **v;
    int *g, m;
    seq_open(s, &v, &g, &m, call);
    int *keep = NEWN(int, m + 1), **before = NEWN(int *, m + 1);
    before[0] = bv_const(0);
    for (int i = 0; i < m; i++) {
        keep[i] = g_and(g[i], sv_lit(sym_apply_op(test, sc, &v[i], 1, call), call));
        int *one = bv_const(0);
        one[0] = keep[i];
        before[i + 1] = bv_add(before[i], one);
    }
    SVal **nv = NEWN(SVal *, m + 1);
    int *ng = NEWN(int, m + 1);
    for (int j = 0; j < m; j++) {
        nv[j] = v[m - 1];
        for (int i = m - 2; i >= j; i--) nv[j] = sv_ite(g_and(keep[i], bv_eq(before[i], bv_const(j))), v[i], nv[j]);
        ng[j] = bv_lt(bv_const(j), before[m]);
    }
    return seq_make(nv, ng, m);
}

static SVal *sym_native(Def *d, Expr **args, int n, SCtx sc, Expr *call) {
    if (d->native == n_selectseq) return seq_select(sym(args[0], sc, P_BOTH), args[1], sc, call);
    if (d->lazy || n > 3 || sym_impure(d->native)) fail_at(call, "Symbolic checking does not support %s.", S(d->name));
    SVal *a[3];
    Value *vals[3];
    int known = 1;
    Native f = d->native;
    int arith = f == n_plus || f == n_minus || f == n_times || f == n_lt || f == n_gt || f == n_leq || f == n_geq
        || f == n_mod || f == n_div || f == n_range || f == n_pow;
    for (int i = 0; i < n; i++) {
        if (d->params[i]->arity) fail_at(call, "Symbolic checking does not support %s.", S(d->name));
        a[i] = sym(args[i], sc, P_BOTH);
        if (a[i]->kind == SV_UNDEF && !arith) return a[i];   /* sv_word makes it an integer */
        known &= (vals[i] = sv_known(a[i])) != NULL;
    }
    if (f == n_print) return a[1];
    if (f == n_printt || f == n_assert) return sv_const(TRUEV);
    SVal *undef = NULL;   /* the operator's error on known arguments: what it means symbolically, if it has a meaning there */
    if (known) {   /* the operator itself */
        EvalState es = eval_save();
        sigjmp_buf here;
        handler = &here;
        if (sigsetjmp(here, 0)) { eval_restore(es); undef = sv_undef(); }
        else {
            Value *v = call_native(d, call, vals, sc.c);
            eval_restore(es);
            return sv_const(v);
        }
    }
    int *x = NULL, *y = NULL, *q, *r;
    if (arith) {
        x = sv_word(a[0], args[0]);
        y = sv_word(a[1], args[1]);
    }
    if (f == n_plus) return sv_bits(SV_INT, bv_add(x, y));
    if (f == n_minus) return sv_bits(SV_INT, bv_sub(x, y));
    if (f == n_times) return sv_bits(SV_INT, bv_mul(x, y));
    if (f == n_lt) return sv_bool(bv_lt(x, y));
    if (f == n_gt) return sv_bool(bv_lt(y, x));
    if (f == n_leq) return sv_bool(bv_le(x, y));
    if (f == n_geq) return sv_bool(bv_le(y, x));
    if (f == n_mod || f == n_div) { bv_divmod(x, y, &q, &r); return sv_bits(SV_INT, f == n_div ? q : r); }
    if (f == n_pow) {
        int64_t k;
        if (!bv_value(y, &k) || k < 0) fail_at(call, "Symbolic checking supports a ^ b only for a constant b >= 0.");
        int *p = bv_const(1);
        while (k-- > 0) p = bv_mul(p, x);
        return sv_bits(SV_INT, p);
    }
    if (f == n_range) {
        SVal *s = sv_inf(INF_RANGE, 2);
        s->u.inf.parts[0] = a[0];
        s->u.inf.parts[1] = a[1];
        return s;
    }
    if (f == n_cardinality) return sv_card(a[0]);
    if (f == n_isfinite) {
        SVal *s = sv_open(a[0]);
        return sv_const(BOOLV(s->kind != SV_INF || (s->inf != INF_INT && s->inf != INF_NAT && s->inf != INF_STRING && s->inf != INF_SEQ)));
    }
    if (f == n_seq) { SVal *s = sv_inf(INF_SEQ, 1); s->u.inf.parts[0] = a[0]; return s; }
    if (f == n_singleton) { SVal *s = sv_fcn(1, 0); fcn_add(s, a[0], a[1], L_TRUE); return s; }
    if (f == n_merge) {
        SVal *g = sv_open(a[0]), *h = sv_open(a[1]);
        if (g->kind != SV_FCN || h->kind != SV_FCN) fail_at(call, "Symbolic checking expected functions for @@.");
        SVal *s = sv_fcn(g->n + h->n, 0), *dom = sv_domain(g);
        for (int i = 0; i < g->n; i++) fcn_add(s, g->u.fcn.keys[i], g->u.fcn.vals[i], g->u.fcn.guards[i]);
        for (int i = 0; i < h->n; i++) fcn_add(s, h->u.fcn.keys[i], h->u.fcn.vals[i], g_and(h->u.fcn.guards[i], sv_in(h->u.fcn.keys[i], dom) ^ 1));
        return s;
    }
    SVal **v, **w;
    int *g, *h, m, k;
    if (f == n_len) return seq_len(a[0]);
    if (f == n_head) return sv_apply(a[0], sv_int_const(1));
    if (f == n_tail) {
        seq_open(a[0], &v, &g, &m, call);
        return m ? seq_make(v + 1, g + 1, m - 1) : a[0];
    }
    if (f == n_append) {
        seq_open(a[0], &v, &g, &m, call);
        int *len = sv_open(seq_len(a[0]))->u.bits;
        SVal **nv = NEWN(SVal *, m + 1);
        int *ng = NEWN(int, m + 1);
        for (int i = 0; i <= m; i++) {
            int here = bv_eq(len, bv_const(i));
            nv[i] = i < m ? sv_ite(here, a[1], v[i]) : a[1];
            ng[i] = i < m ? g_or(g[i], here) : here;
        }
        return seq_make(nv, ng, m + 1);
    }
    if (f == n_concat) {
        seq_open(a[0], &v, &g, &m, call);
        seq_open(a[1], &w, &h, &k, call);
        int *ls = sv_open(seq_len(a[0]))->u.bits, *lt = sv_open(seq_len(a[1]))->u.bits, *total = bv_add(ls, lt);
        SVal **nv = NEWN(SVal *, m + k + 1);
        int *ng = NEWN(int, m + k + 1);
        for (int i = 0; i < m + k; i++) {
            int *pos = bv_const(i + 1);
            SVal *from_t = k ? sv_apply(a[1], sv_bits(SV_INT, bv_sub(pos, ls))) : NULL;
            nv[i] = i < m ? (from_t ? sv_ite(bv_le(pos, ls), v[i], from_t) : v[i]) : from_t;
            ng[i] = bv_le(pos, total);
        }
        return seq_make(nv, ng, m + k);
    }
    if (f == n_subseq) {
        seq_open(a[0], &v, &g, &m, call);
        int *lo = sv_word(a[1], args[1]), *hi = sv_word(a[2], args[2]), *len = bv_add(bv_sub(hi, lo), bv_const(1));
        SVal **nv = NEWN(SVal *, m + 1);
        int *ng = NEWN(int, m + 1);
        for (int i = 0; i < m; i++) {
            nv[i] = sv_apply(a[0], sv_bits(SV_INT, bv_add(lo, bv_const(i))));
            ng[i] = bv_le(bv_const(i + 1), len);
        }
        return seq_make(nv, ng, m);
    }
    if (undef) return undef;
    fail_at(call, "Symbolic checking does not support %s.", S(d->name));
}

/* ---------------------------------------------------------------- symbolic actions */

/* An action is evaluated as the generator evaluates it, but once for all
   states: a branch is a guard and the next state as far as it assigns
   it. A disjunction, an \E and an IF split the branch; the branches that
   assign the same variables then merge again into one, each variable the
   value of the branch that fresh literals choose, so that a step is one
   branch whatever the number of the action's cases. */
typedef struct { int guard; SVal **next; } Branch;
typedef struct { Branch *v; int n, cap; } Branches;

static void branches_add(Branches *bs, Branch b) {
    if (b.guard == L_FALSE) return;
    if (bs->n == bs->cap) {
        Branch *g = NEWN(Branch, bs->cap = bs->cap ? 2 * bs->cap : 4);
        if (bs->n) memcpy(g, bs->v, sizeof(Branch) * (size_t)bs->n);
        bs->v = g;
    }
    bs->v[bs->n++] = b;
}

static Branch branch_and(Branch b, int g) { b.guard = g_and(b.guard, g); return b; }

static Branch branch_set(Branch b, int var, SVal *v) {
    if (v->kind == SV_UNDEF) fail("%s", v->u.err);
    SVal **next = NEWN(SVal *, nvars);
    memcpy(next, b.next, sizeof(SVal *) * (size_t)nvars);
    next[var] = v;
    b.next = next;
    return b;
}

static int same_assigned(Branch *a, Branch *b) {
    for (int i = 0; i < nvars; i++) if (!a->next[i] != !b->next[i]) return 0;
    return 1;
}

/* One branch for bs: the first of pick whose branch is taken. */
static Branch merge_branches(Branch *bs, int n, int *pick) {
    Branch m = {L_FALSE, NEWN(SVal *, nvars)};
    for (int i = 0; i < n; i++) m.guard = g_or(m.guard, g_and(pick[i], bs[i].guard));
    for (int v = 0; v < nvars; v++) {
        if (!bs[0].next[v]) continue;
        SVal *x = bs[n - 1].next[v];
        for (int i = n - 2; i >= 0; i--) x = sv_ite(pick[i], bs[i].next[v], x);
        m.next[v] = x;
    }
    return m;
}

/* The branches of in, those that assign the same variables merged; an
   exclusive set's guards choose, as no two hold together. */
static void merge_into(Branches *in, Branches *out, int exclusive) {
    char *done = NEWN(char, in->n > 0 ? in->n : 1);
    Branch *group = NEWN(Branch, in->n > 0 ? in->n : 1);
    for (int i = 0; i < in->n; i++) {
        if (done[i]) continue;
        int n = 0;
        for (int j = i; j < in->n; j++)
            if (!done[j] && same_assigned(&in->v[i], &in->v[j])) { done[j] = 1; group[n++] = in->v[j]; }
        if (n == 1) { branches_add(out, group[0]); continue; }
        int *pick = exclusive ? NEWN(int, n) : one_hot(n);
        for (int k = 0; exclusive && k < n; k++) pick[k] = group[k].guard;
        branches_add(out, merge_branches(group, n, pick));
    }
}

static void act(Expr *e, SCtx sc, Branch in, Branches *out);

typedef struct { Expr *body; Branch in; Branches *out; } SAct;

static void sym_act_fn(SCtx inner, int g, SVal *key, void *data) {
    (void)key;
    SAct *a = data;
    act(a->body, inner, branch_and(a->in, g), a->out);
}

/* What e stands for, in its context, as far as parameters, definitions
   without them and the substitutions of instances for variables go. */
static Expr *sym_arg(Expr *e, SCtx *sc) {
    for (;;) {
        SEnv *b;
        Ctx c = sc->c;
        Expr *x;
        Def *d = e->def;
        if (e->kind == K_BOUND && (b = senv_find(sc->s, d)) && b->e) e = b->e, *sc = b->ctx;
        else if (e->kind == K_DECL && d->kind == D_VAR && d->var_index < 0 && (x = substitute(d, &c))) e = x, *sc = (SCtx){c, NULL};
        else if ((e->kind == K_CALL || e->kind == K_INSTCALL) && !e->n && d->kind == D_OP && !d->native && !d->replacement && d->local != 2)
            *sc = (SCtx){{NULL, e->kind == K_INSTCALL ? sym_instance(e, *sc) : sc->c.inst}, NULL}, e = d->body;
        else return e;
    }
}

/* The level of e where its parameters stand for their arguments. */
static int act_level(Expr *e, SCtx sc) {
    ExprInfo *in = expr_info(e);
    int l = in->level;
    for (int i = 0; i < in->n && l < 2; i++) {
        SEnv *b = in->defs[i] == &at_mark ? NULL : senv_find(sc.s, in->defs[i]);
        if (b && b->e) { int a = act_level(b->e, b->ctx); if (a > l) l = a; }
    }
    return l;
}

/* The variable that `lhs = e` or `lhs \in S` assigns, -1 if none. */
static int assign_target(Expr *lhs, SCtx sc) {
    lhs = sym_arg(lhs, &sc);
    if (lhs->kind == K_PRIME) lhs = sym_arg(lhs->args[0], &sc);   /* in the initial predicate, x' is x */
    else if (!sym_init) return -1;
    if (lhs->kind != K_DECL) return -1;
    if (sym_cinit) return lhs->def->kind == D_CONST ? sym_const_index(lhs->def) : -1;
    if (lhs->def->kind != D_VAR || lhs->def->var_index < 0) return -1;
    return lhs->def->var_index;
}

static Branch act_unchanged(Expr *e, SCtx sc, Branch b) {
    e = sym_arg(e, &sc);
    if (e->kind == X_TUPLE) {
        for (int i = 0; i < e->n; i++) b = act_unchanged(e->args[i], sc, b);
        return b;
    }
    if (e->kind == K_DECL && e->def->kind == D_VAR && e->def->var_index >= 0) {
        int v = e->def->var_index;
        return b.next[v] ? branch_and(b, sv_eq(b.next[v], sym_cur[v])) : branch_set(b, v, sym_cur[v]);
    }
    sym_next = b.next;
    SVal *now = sym(e, sc, P_BOTH);
    sym_primed = 1;
    SVal *then = sym(e, sc, P_BOTH);
    sym_primed = 0;
    return branch_and(b, sv_eq(now, then));
}

static void act(Expr *e, SCtx sc, Branch in, Branches *out) {
    if (in.guard == L_FALSE) return;
    sym_next = in.next;
    if (act_level(e, sc) < (sym_init ? 1 : 2)) { branches_add(out, branch_and(in, sym_bool(e, sc, P_POS))); return; }
    Branches tmp = {0};
    switch (e->kind) {
    case K_AND: {
        Branches cur = {0};
        branches_add(&cur, in);
        for (int i = 0; i < e->n && cur.n; i++) {
            Branches next = {0};
            for (int k = 0; k < cur.n; k++) act(e->args[i], sc, cur.v[k], &next);
            cur = (Branches){0};
            merge_into(&next, &cur, 0);
        }
        for (int k = 0; k < cur.n; k++) branches_add(out, cur.v[k]);
        return;
    }
    case K_OR:
        for (int i = 0; i < e->n; i++) act(e->args[i], sc, in, &tmp);
        merge_into(&tmp, out, 0);
        return;
    case X_EXISTS: {
        SVal **sets = NEWN(SVal *, e->nb);
        int64_t n = bindings_count(e->bounds, e->nb, sc, sets);
        if (n < 0 || n > 64) {
            int g;
            SCtx inner = sym_skolem(e, sc, sets, &g);
            act(e->args[0], inner, branch_and(in, g), out);
            return;
        }
        SAct a = {e->args[0], in, &tmp};
        sym_bindings(e->bounds, e->nb, sets, sc, sym_act_fn, &a, e);
        merge_into(&tmp, out, 0);
        return;
    }
    case X_IF: {
        int c = sym_bool(e->args[0], sc, P_BOTH);
        act(e->args[1], sc, branch_and(in, c), &tmp);
        act(e->args[2], sc, branch_and(in, c ^ 1), &tmp);
        merge_into(&tmp, out, 1);
        return;
    }
    case X_CASE: {
        int none = L_TRUE;
        for (int i = 0; i + 1 < e->n; i += 2) {
            sym_next = in.next;
            int c = e->args[i] ? sym_bool(e->args[i], sc, P_BOTH) : L_TRUE;
            act(e->args[i + 1], sc, branch_and(in, g_and(none, c)), &tmp);
            none = g_and(none, c ^ 1);
        }
        merge_into(&tmp, out, 1);
        return;
    }
    case X_LET: act(e->args[0], let_ctx(e, sc), in, out); return;
    case K_CALL: case K_PARAMCALL: case K_INSTCALL: {
        Def *d = e->def->replacement ? e->def->replacement : e->def;
        SCtx at = sc;   /* where d is defined */
        while (d->kind == D_PARAM) {   /* an operator argument: the operator it stands for */
            SEnv *b = senv_find(at.s, d);
            Expr *op = b ? b->e : NULL;
            if (!op || !(op->kind == X_LAMBDA || ((op->kind == K_CALL || op->kind == K_PARAMCALL) && !op->n))) break;
            d = op->def, at = b->ctx;
        }
        if (d->kind != D_OP || d->native) break;
        SCtx inner = {{NULL, e->kind == K_INSTCALL && d == e->def ? sym_instance(e, sc) : at.c.inst}, NULL};
        if (d->local == 2) {
            SEnv *b = senv_find(at.s, d);
            Env *cb = b ? NULL : env_find(at.c.env, d);
            if (!b && !cb) break;
            inner = b ? b->ctx : (SCtx){{cb->ctx_env, cb->ctx_inst}, NULL};
        }
        inner.s = sym_typed(e, sc, inner.s);
        inner = sym_bind_args(d, e->args, e->n, sc, inner);
        deeper();
        act(d->body, inner, in, out);
        eval_depth--;
        return;
    }
    case K_EQ: case K_IN: case K_SUBSETEQ: {
        int v = assign_target(e->args[0], sc);
        if (v < 0 || in.next[v]) break;
        int saved = sym_primed;
        sym_primed = sym_init;
        SVal *x = sym(e->args[1], sc, P_BOTH);
        sym_primed = saved;
        if (e->kind == K_EQ) { branches_add(out, branch_set(in, v, x)); return; }
        if (e->kind == K_SUBSETEQ) { SVal *all = sv_inf(INF_SUBSET, 1); all->u.inf.parts[0] = x; x = all; }
        int g;
        SVal *pick = sv_pick(x, &g);
        if (g == L_FALSE) return;
        branches_add(out, branch_set(branch_and(in, g), v, pick));
        return;
    }
    case K_UNCHANGED:
        if (sym_init) break;
        branches_add(out, act_unchanged(e->args[0], sc, in));
        return;
    case X_SQACT: {
        act(e->args[0], sc, in, &tmp);
        if (!sym_init) branches_add(&tmp, act_unchanged(e->args[1], sc, in));
        merge_into(&tmp, out, 0);
        return;
    }
    case X_ANGLEACT: {
        if (sym_init) break;
        Branches done = {0};
        act(e->args[0], sc, in, &done);
        for (int k = 0; k < done.n; k++) {
            sym_next = done.v[k].next;
            SVal *now = sym(e->args[1], sc, P_BOTH);
            sym_primed = 1;
            SVal *then = sym(e->args[1], sc, P_BOTH);
            sym_primed = 0;
            branches_add(&tmp, branch_and(done.v[k], sv_eq(now, then) ^ 1));
        }
        merge_into(&tmp, out, 0);
        return;
    }
    default: break;
    }
    sym_next = in.next;
    branches_add(out, branch_and(in, sym_bool(e, sc, P_POS)));
}

/* Which variables e assigns, as Apalache finds its assignments: by the
   syntax alone, with operators inlined, refusing a disjunct, or an arm of
   IF or CASE, that assigns other variables than its siblings. What it
   cannot follow, an instance's variables or a LAMBDA, leaves the rule
   unchecked. asg_env holds the arguments of the operators being inlined. */
static int asg_unknown, asg_depth;
typedef struct { Def *param; Expr *arg; } AsgArg;
static AsgArg *asg_env;
static int nasg_env, asg_env_cap;
static void asg(Expr *e, char *done);

/* What e stands for: an argument for a parameter, a definition's body for
   a name without arguments. */
static Expr *asg_resolve(Expr *e) {
    for (int depth = 0; depth < 100; depth++) {
        int i = nasg_env - 1;
        if (e->kind == K_BOUND || (e->kind == K_PARAMCALL && !e->n)) while (i >= 0 && asg_env[i].param != e->def) i--;
        if (i >= 0 && (e->kind == K_BOUND || e->kind == K_PARAMCALL)) e = asg_env[i].arg;
        else if (e->kind == K_CALL && !e->n && e->def->kind == D_OP && !e->def->native && !e->def->arity) e = e->def->body;
        else return e;
    }
    return e;
}

static void asg_call(Def *d, Expr **args, int n, char *done) {
    if (d->replacement) d = d->replacement;
    if (d->kind != D_OP || d->native) return;
    if (d->recursive || d->nparams != n || asg_depth > 100) { asg_unknown = 1; return; }
    if (nasg_env + n > asg_env_cap) {
        AsgArg *grown = NEWN(AsgArg, asg_env_cap = 2 * (nasg_env + n));
        if (nasg_env) memcpy(grown, asg_env, sizeof *asg_env * (size_t)nasg_env);
        asg_env = grown;
    }
    for (int i = 0; i < n; i++) asg_env[nasg_env + i].param = d->params[i], asg_env[nasg_env + i].arg = args[i];
    nasg_env += n, asg_depth++;
    asg(d->body, done);
    nasg_env -= n, asg_depth--;
}

static void asg_target(Expr *lhs, char *done) {
    lhs = asg_resolve(lhs);
    int primed = lhs->kind == K_PRIME;
    if (primed) lhs = asg_resolve(lhs->args[0]);
    if (lhs->kind == K_INSTCALL || (primed && lhs->kind != K_DECL))
        asg_unknown = 1;
    else if ((primed || sym_init) && lhs->kind == K_DECL && lhs->def->kind == D_VAR) {   /* in the initial predicate, x' is x */
        if (lhs->def->var_index < 0) asg_unknown = 1;
        else done[lhs->def->var_index] = 1;
    }
}

static void asg_unchanged(Expr *x, char *done) {
    x = asg_resolve(x);
    if (x->kind == X_TUPLE) for (int i = 0; i < x->n; i++) asg_unchanged(x->args[i], done);
    else if (x->kind == K_DECL) asg_target(&(Expr){.kind = K_PRIME, .n = 1, .args = &x}, done);
    else asg_unknown = 1;
}

/* The variables of want, all if NULL, that done does not assign; NULL if none. */
static char *asg_missing(char *want, char *done) {
    Buf b = {0};
    for (int v = 0; v < nvars; v++) if ((!want || want[v]) && !done[v]) buf_printf(&b, "%s%s", b.s ? ", " : "", S(vars[v]->name));
    return b.s;
}

static void asg_arms(Expr **arms, int n, char *done) {
    char **sets = NEWN(char *, n), *any = NEWN(char, nvars);
    for (int i = 0; i < n; i++) {
        memcpy(sets[i] = NEWN(char, nvars), done, (size_t)nvars);
        asg(arms[i], sets[i]);
        if (asg_unknown) return;
        for (int v = 0; v < nvars; v++) any[v] |= sets[i][v];
    }
    for (int i = 0; i < n; i++) {
        char *missing = asg_missing(any, sets[i]);
        if (missing) fail_at(arms[i], "Missing assignments to: %s", missing);
    }
    memcpy(done, any, (size_t)nvars);
}

static void asg(Expr *e, char *done) {
    if (asg_unknown) return;
    switch (e->kind) {
    case K_AND: case X_ANGLEACT:
        for (int i = 0; i < (e->kind == K_AND ? e->n : 1); i++) asg(e->args[i], done);
        return;
    case K_OR: asg_arms(e->args, e->n, done); return;
    case X_IF: asg_arms(e->args + 1, 2, done); return;
    case X_CASE: {
        Expr **arms = NEWN(Expr *, e->n / 2);
        for (int i = 0; i < e->n / 2; i++) arms[i] = e->args[2 * i + 1];
        asg_arms(arms, e->n / 2, done);
        return;
    }
    case X_SQACT: {
        Expr unchanged = *e;   /* located at [A]_v */
        unchanged.kind = K_UNCHANGED, unchanged.n = 1, unchanged.args = e->args + 1;
        asg_arms((Expr *[]){e->args[0], &unchanged}, 2, done);
        return;
    }
    case X_EXISTS: case X_LET: asg(e->args[0], done); return;
    case K_EQ: case K_IN: asg_target(e->args[0], done); return;
    case K_UNCHANGED: asg_unchanged(e->args[0], done); return;
    case K_CALL: asg_call(e->def, e->args, e->n, done); return;
    case K_PARAMCALL: {
        Expr *op = asg_resolve(&(Expr){.kind = K_PARAMCALL, .def = e->def});
        if (op->kind == X_OPREF || ((op->kind == K_CALL || op->kind == K_PARAMCALL) && !op->n)) asg_call(op->def, e->args, e->n, done);
        else asg_unknown = 1;
        return;
    }
    case K_BOUND: { Expr *x = asg_resolve(e); if (x != e) asg(x, done); return; }
    case K_INSTCALL: case K_SUBSETEQ: asg_unknown = 1; return;
    default: return;
    }
}

/* That e, the initial predicate or the next-state relation, assigns
   every variable as Apalache finds assignments. */
static void asg_check(Expr *e, int init) {
    char *done = NEWN(char, nvars), *missing;
    sym_init = init;
    asg_unknown = nasg_env = asg_depth = 0;
    asg(e, done);
    sym_init = 0;
    if (!asg_unknown && (missing = asg_missing(NULL, done))) fail("No assignments found for: %s", missing);
}

/* The single branch of an action that assigns every variable, as one
   step needs; NULL if it is never enabled. */
static Branch *act_step(Expr *e, Ctx c, const char *what) {
    Branches out = {0};
    Branch in = {L_TRUE, NEWN(SVal *, nvars)};
    act(e, (SCtx){c, NULL}, in, &out);
    if (!out.n) return NULL;
    for (int k = 0; k < out.n; k++)
        for (int v = 0; v < nvars; v++)
            if (!out.v[k].next[v])
                fail_at(e, "%s does not assign the variable %s on every branch, as symbolic checking requires.", what, S(vars[v]->name));
    Branches one = {0};
    merge_into(&out, &one, 0);
    Branch *b = NEW(Branch);
    *b = one.v[0];
    return b;
}

/* ENABLED A, as TLC checks it, where Apalache has none: a literal of its
   own, true only where some branch of A is, at the state read. That it
   is false where A is enabled is ruled out as the models show it, by
   sym_enabled_refine. One made for a query (an invariant, a property, a
   deadlock) is refined for it; one of a step, for every query after. */
typedef struct { int lit, query; Expr *a; SCtx sc; SVal **at; Branches out; } SymEnabled;
static SymEnabled *sym_enableds;
static int nsym_enableds, sym_enabled_query;

static int sym_enabled_lit(Expr *a, SCtx sc) {
    SVal **next = sym_next;
    Branches out = {0};
    act(a, sc, (Branch){L_TRUE, NEWN(SVal *, nvars)}, &out);
    sym_next = next;
    int some = L_FALSE;
    for (int k = 0; k < out.n; k++) some = g_or(some, out.v[k].guard);
    if (some == L_FALSE) return L_FALSE;
    int l = 2 * sat_var();
    sat_add2(l ^ 1, some);
    if (!(nsym_enableds & (nsym_enableds + 1))) {
        SymEnabled *grown = NEWN(SymEnabled, 2 * (nsym_enableds + 1));
        if (nsym_enableds) memcpy(grown, sym_enableds, sizeof *grown * (size_t)nsym_enableds);
        sym_enableds = grown;
    }
    sym_enableds[nsym_enableds++] = (SymEnabled){l, sym_enabled_query, a, sc, sym_cur, out};
    return l;
}

static SVal *sym_enabled(Expr *e, SCtx sc) {
    return sv_bool(sym_enabled_lit(e->args[0], sc));
}

/* That st[depth], in the model, has no successor: a deadlock as TLC finds
   it, in any behavior. */
static int sym_dead(SVal ***st, int depth, int kept) {
    sym_cur = st[depth];
    int some = L_FALSE;
    sym_enabled_query = 1;
    for (int k = 0; k < nactions; k++) some = g_or(some, sym_enabled_lit(actions[k].e, (SCtx){actions[k].c, NULL}));
    sym_enabled_query = 0;
    return g_and(kept, some ^ 1);
}

/* Whether each ENABLED of a step, or of the query made since the from'th,
   that the model has false is: where the solver finds a
   step of A from the model's state, with its bindings and constants,
   ENABLED A is tied to every state that step leaves from, and 0 is
   returned. The model is kept. */
static int sym_enabled_refine(int from) {
    int n = 0, m = nsym_enableds, *pins = NEWN(int, m + 1);   /* -1 where the model has it true */
    for (int i = 0; i < m; i++) {
        SymEnabled *x = &sym_enableds[i];
        pins[i] = -1;
        if ((i < from && x->query) || lit_true(x->lit)) continue;
        int pin = L_TRUE;
        for (int v = 0; v < nvars; v++) pin = g_and(pin, sv_eq(x->at[v], sv_const(sv_model(x->at[v]))));
        for (SEnv *b = x->sc.s; b; b = b->next) if (b->v) pin = g_and(pin, sv_eq(b->v, sv_const(sv_model(b->v))));
        for (int c = 0; c < nsym_consts; c++) pin = g_and(pin, sv_eq(sym_const_vals[c], sv_const(sv_model(sym_const_vals[c]))));
        pins[i] = pin, n++;
    }
    if (!n) return 1;
    int kept = sat.nvars, fine = 1;
    unsigned char *model = NEWN(unsigned char, kept + 1);
    memcpy(model, sat.model, (size_t)kept);
    for (int i = 0; i < m; i++) {
        SymEnabled *x = &sym_enableds[i];
        if (pins[i] < 0) continue;
        for (int k = 0; k < x->out.n; k++) {
            int q[2] = {pins[i], x->out.v[k].guard};
            if (!sat_solve(q, 2)) continue;
            SVal **t = NEWN(SVal *, nvars);
            for (int v = 0; v < nvars; v++) t[v] = sv_const(sv_model(x->out.v[k].next[v] ? x->out.v[k].next[v] : x->at[v]));
            sym_cur = x->at, sym_next = t;
            sat_add2(x->lit, sym_bool(x->a, x->sc, P_BOTH) ^ 1);
            sym_next = NULL;
            fine = 0;
            break;
        }
    }
    memcpy(sat.model, model, (size_t)kept);
    return fine;
}

/* Whether the clauses and the assumptions hold together, as sat_solve,
   with each ENABLED as it is. */
static int sym_solve(int *assume, int n) {
    while (sat_solve(assume, n)) if (sym_enabled_refine(nsym_enableds)) return 1;
    return 0;
}

/* ---------------------------------------------------------------- symbolic checking */

static long sym_length = 10;
static long sym_max_error = 1;   /* -max-error */
static const char *sym_run_dir;   /* -run-dir */

static void sym_print(Value ***s, int *act_of, int n) {
    printf("Error: The behavior up to this point is:\n");
    for (int i = 0; i < n; i++) print_numbered(i + 1, act_of[i], s[i], i ? s[i - 1] : NULL, s[i + (i + 1 < n)]);
}

static void itf_write(Value ***s, int n, int loop, int index);

/* The parameter of a trace invariant, which Apalache checks of the
   behavior so far; NULL for another invariant. */
static Def *trace_param(Check *c) { return c->def && c->def->nparams == 1 && c->expr == c->def->body ? c->def->params[0] : NULL; }

/* The behavior up to depth as a trace invariant takes it: a sequence of
   records, a field for each variable. */
static SVal *sym_history(SVal ***st, int depth) {
    SVal *h = sv_fcn(depth + 1, 0);
    for (int i = 0; i <= depth; i++) {
        SVal *r = sv_fcn(nvars, 1);
        for (int v = 0; v < nvars; v++) fcn_add(r, sv_const(mk_str(vars[v]->name)), st[i][v], L_TRUE);
        fcn_add(h, sv_int_const(i + 1), r, L_TRUE);
    }
    return h;
}

/* The negation of each temporal property, in negation normal form. */
static TF **sym_negated;

/* Each state of the behavior the model gives, checked by the evaluator:
   it satisfies Init, each step its action and, for a violation, the last
   state does not satisfy invariant bad, or the behavior is a lasso, back
   to state *loop, or stuttering at its last, that violates property prop
   and is fair. A behavior that does not
   replay is a fault of the symbolic encoding, reported as such. */
static int sym_behavior(SVal ***st, int **picks, int *nenabled, int **enabled, int n, int bad, int prop, int stutter, int *loop, Value ****out, int **acts) {
    for (int i = 0; i < nsym_consts; i++) sym_consts[i]->value = sv_model(sym_const_vals[i]);
    Value ***s = NEWN(Value **, n);
    int *act_of = NEWN(int, n);
    for (int i = 0; i < n; i++) {
        s[i] = NEWN(Value *, nvars);
        for (int v = 0; v < nvars; v++) s[i][v] = sv_model(st[i][v]);
        act_of[i] = -1;
        if (i) for (int k = 0; k < nenabled[i - 1]; k++) if (lit_true(picks[i - 1][k])) act_of[i] = enabled[i - 1][k];
    }
    witnesses = NEWN(Witness, nsym_witnesses);
    for (int i = 0; i < nsym_witnesses; i++) {   /* but those of an empty set, undefined */
        Expr *e = sym_witnesses[i].e;
        int n = bounds_total(e->bounds, e->nb), k = 0;
        while (k < n && sym_witnesses[i].vals[k]->kind != SV_UNDEF) k++;
        if (k < n) continue;
        Witness *w = &witnesses[nwitnesses++];
        w->e = e;
        w->step = sym_witnesses[i].step;
        w->vals = NEWN(Value *, n);
        while (k--) w->vals[k] = sv_model(sym_witnesses[i].vals[k]);
    }
    gen_values = NEWN(GenValue, nsym_gens + 1);
    for (int i = 0; i < nsym_gens; i++) gen_values[i] = (GenValue){sym_gens[i].e, sym_gens[i].step, 0, sv_model(sym_gens[i].v)};
    ngen_values = nsym_gens;
    EvalState es = eval_save();
    sigjmp_buf here;
    handler = &here;
    const char *wrong = NULL;
    if (sigsetjmp(here, 0)) { eval_restore(es); wrong = error_message.s ? error_message.s : "an error"; }
    else {
        cur_state = next_state = s[0];   /* x' is x in the initial predicate */
        gen_step = 0;
        if (!eval_bool(init_expr, root_ctx)) wrong = "the initial state does not satisfy the initial predicate";
        for (int i = 1; i < n && !wrong; i++) {
            gen_step = i;
            cur_state = s[i - 1];
            next_state = s[i];
            Action *a = &actions[act_of[i]];
            if (!eval_bool(a->e, a->c)) wrong = "a step is not one of its action";
        }
        if (!wrong && bad >= 0) {
            Check *c = &invariants[bad];
            Def *p = trace_param(c);
            int action = expr_level(c->expr) == 2;
            Ctx at = c->ctx;
            if (p) at.env = mk_binding(p, sv_model(sym_history(st, n - 1)), at.env);
            cur_state = s[n - 1 - action];
            next_state = action ? s[n - 1] : NULL;
            if (eval_bool(c->expr, at)) wrong = "the last state satisfies the invariant";
        }
        if (!wrong && prop >= 0) {
            int l = 0, m = n - !stutter;   /* the lasso's states */
            for (int v; l < n - 1 && !stutter; l++) {
                for (v = 0; v < nvars && veq(s[l][v], s[n - 1][v]); v++) {}
                if (v == nvars) break;
            }
            *loop = l;
            if (l == m) wrong = "the last state is none before it";
            else if (!holds_on_lasso(sym_negated[prop], s, m, l, 0)) wrong = "the lasso satisfies the property";
            else if (!fair_on_lasso(s, m, l)) wrong = "the lasso is not fair";
        }
        eval_restore(es);
    }
    nwitnesses = ngen_values = 0;
    if (wrong) {
        printf("Error: The behavior symbolic checking found does not replay: %s.\nThis is a bug in manyan.\n", wrong);
        sym_print(s, act_of, n);
        return 0;
    }
    *out = s;
    *acts = act_of;
    return 1;
}


/* The constants the configuration leaves, as -cinit's operator chooses
   them, as the initial predicate chooses the variables: its branch. */
static Branch *sym_constants(void) {
    Sym *s = root_sym(intern(sym_cinit_name));
    if (!s || s->def->kind != D_OP || s->def->nparams) fail("The constant initializer %s is not an operator without parameters of the specification.", sym_cinit_name);
    int n;
    Def **c = tlc_constants(&n);
    sym_consts = NEWN(Def *, n + 1);
    for (int i = 0; i < n; i++) if (!c[i]->value && !c[i]->replacement && !c[i]->arity) sym_consts[nsym_consts++] = c[i];
    int saved = nvars;
    Def **saved_vars = vars;
    nvars = nsym_consts, vars = sym_consts, sym_cinit = 1;
    Branch *b = act_step(s->def->body, root_ctx, "The constant initializer");
    nvars = saved, vars = saved_vars, sym_cinit = 0;
    if (b) sym_const_vals = b->next;
    return b;
}

/* The literal that invariant i is violated at depth: of the state there,
   of the step to it for an action invariant, or of the behavior to it for
   a trace invariant. */
static int sym_violated(int i, SVal ***st, int depth) {
    Check *c = &invariants[i];
    Def *p = trace_param(c);
    int action = expr_level(c->expr) == 2;
    if (action && !depth) return L_FALSE;
    sym_cur = st[depth - action];
    sym_next = action ? st[depth] : NULL;
    SCtx sc = {c->ctx, NULL};
    if (p) sc = sym_bind(sc, p, sym_history(st, depth));
    sym_enabled_query = 1;
    int l = sym_bool(c->expr, sc, P_NEG) ^ 1;
    sym_enabled_query = 0;
    return l;
}

/* Temporal properties, as Apalache checks them: on a lasso, a behavior
   of k steps whose last state is one before it, as the bounded encoding
   of Biere et al. (2006) has it. A behavior with no such loop is no
   counterexample. Each lasso Apalache finds is one, but where its
   tableau's own variables differ, it may find only a longer one.

   Apalache has no fairness. With fairness, the counterexample is TLC's:
   a fair lasso, which may also stutter forever at its last state. */

typedef struct { SVal ***st; int k, *back; } Lasso;   /* st[0..k]: back[j], whether the loop goes back to j or before */

static int states_eq(SVal **a, SVal **b) {
    int l = L_TRUE;
    for (int v = 0; v < nvars && l != L_FALSE; v++) l = g_and(l, sv_eq(a[v], b[v]));
    return l;
}

typedef struct { TF *t; int at, lit; } LassoMemo;

/* Whether t holds from position i of the lasso st[0..k]: back[j] whether
   the loop goes back to j or before, so that from any position on it, j
   comes again. */
static int sym_lasso(TF *t, SVal ***st, int k, int *back, int i, LassoMemo **memo, int *nmemo) {
    for (int m = 0; m < *nmemo; m++) if ((*memo)[m].t == t && (*memo)[m].at == i) return (*memo)[m].lit;
    int l;
    switch (t->op) {
    case TF_TRUE: return L_TRUE;
    case TF_FALSE: return L_FALSE;
    case TF_AND: l = g_and(sym_lasso(t->a, st, k, back, i, memo, nmemo), sym_lasso(t->b, st, k, back, i, memo, nmemo)); break;
    case TF_OR: l = g_or(sym_lasso(t->a, st, k, back, i, memo, nmemo), sym_lasso(t->b, st, k, back, i, memo, nmemo)); break;
    case TF_ATOM:
        sym_cur = st[i];
        sym_next = t->action ? st[i + 1] : NULL;
        l = sym_bool(t->atom, (SCtx){t->c, NULL}, P_BOTH) ^ t->neg;
        break;
    default: {   /* at every position, or at some, that comes from i on */
        int always = t->op == TF_ALWAYS;
        l = always ? L_TRUE : L_FALSE;
        for (int j = 0; j < k; j++) {
            int comes = j >= i ? L_TRUE : back[j], h = sym_lasso(t->a, st, k, back, j, memo, nmemo);
            l = always ? g_and(l, g_implies(comes, h)) : g_or(l, g_and(comes, h));
        }
    }
    }
    *memo = xrealloc(*memo, sizeof **memo * (size_t)(*nmemo + 1));
    (*memo)[(*nmemo)++] = (LassoMemo){t, i, l};
    return l;
}

/* The behavior st[0..k] as a lasso, its last state one before it. */
static Lasso sym_loop(SVal ***st, int k) {
    int *back = NEWN(int, k + 1);
    for (int j = 0; j < k; j++) back[j] = g_or(j ? back[j - 1] : L_FALSE, states_eq(st[j], st[k]));
    return (Lasso){st, k, back};
}

/* The behavior st[0..k] stuttering forever at st[k]. */
static Lasso sym_stutter(SVal ***st, int k) {
    SVal ***s = NEWN(SVal **, k + 2);
    memcpy(s, st, sizeof *s * (size_t)(k + 1));
    s[k + 1] = st[k];
    int *back = NEWN(int, k + 1);
    for (int j = 0; j < k; j++) back[j] = L_FALSE;
    back[k] = L_TRUE;
    return (Lasso){s, k + 1, back};
}

/* Whether fairness f's action is disabled at st[i]: a literal of its own,
   which only sym_refine ties to the action. */
static int **sym_disabled;

static int sym_disabled_at(int f, int i) {
    if (!sym_disabled[f][i]) sym_disabled[f][i] = 2 * sat_var();
    return sym_disabled[f][i];
}

/* That the lasso is fair: for each WF_v(A), some step on its loop is an
   <<A>>_v step or A is disabled at some state on it; for SF_v(A), at all. */
static int sym_fair(Lasso ls) {
    int fair = L_TRUE;
    for (int f = 0; f < nfairs; f++) {
        int strong = fairs[f].strong, took = L_FALSE, off = strong ? L_TRUE : L_FALSE;
        for (int i = 0; i < ls.k; i++) {
            int on = ls.back[i], d = sym_disabled_at(f, i);
            sym_cur = ls.st[i], sym_next = ls.st[i + 1];
            took = g_or(took, g_and(on, sym_bool(fairs[f].step, (SCtx){fairs[f].c, NULL}, P_BOTH)));
            off = strong ? g_and(off, g_implies(on, d)) : g_or(off, g_and(on, d));
        }
        fair = g_and(fair, g_or(took, off));
    }
    return fair;
}

/* Whether the model's lasso is fair, as the evaluator finds it: where the
   model has an action disabled that the evaluator finds enabled, the
   successor it finds is no step of the action from any state disabled
   so, for every model, and 0 is returned. */
static int sym_refine(Lasso ls) {
    for (int i = 0; i < nsym_consts; i++) sym_consts[i]->value = sv_model(sym_const_vals[i]);
    int fair = 1;
    for (int f = 0; f < nfairs; f++)
        for (int i = 0; i < ls.k; i++) {
            int d = sym_disabled[f][i];
            if (!lit_true(ls.back[i]) || !lit_true(d)) continue;
            Value **s = NEWN(Value *, nvars), **t = NEWN(Value *, nvars);
            for (int v = 0; v < nvars; v++) s[v] = sv_model(ls.st[i][v]);
            cur_state = s, next_state = NULL, enabled_seen = t;
            int on = eval_bool(fairs[f].enabled, fairs[f].c);
            enabled_seen = NULL;
            if (!on) continue;
            SVal **next = NEWN(SVal *, nvars);
            for (int v = 0; v < nvars; v++) next[v] = sv_const(t[v] ? t[v] : s[v]);
            sym_cur = ls.st[i], sym_next = next;
            sat_add2(d ^ 1, sym_bool(fairs[f].step, (SCtx){fairs[f].c, NULL}, P_BOTH) ^ 1);
            fair = 0;
        }
    return fair;
}

/* Whether a model has the lasso violate property p, fairly; it is left
   as the solver's model. */
static int sym_lasso_violated(int p, Lasso ls, int kept) {
    if (!ls.k) return 0;
    LassoMemo *memo = NULL;
    sym_enabled_query = 1;
    int from = nsym_enableds, n = 0, l = g_and(g_and(kept, ls.back[ls.k - 1]), sym_lasso(sym_negated[p], ls.st, ls.k, ls.back, 0, &memo, &n));
    sym_enabled_query = 0;
    free(memo);
    if (nfairness) l = g_and(l, sym_fair(ls));
    while (sat_solve(&l, 1)) if (sym_refine(ls) && sym_enabled_refine(from)) return 1;
    return 0;
}

static int sym_types(void);
static int lib_module(Module *m);

/* A recursive operator or function of the specification's modules, which
   Apalache refuses; those of the modules it builds in or rewires are not. */
static Def *recursive_in(Module *m) {
    if (lib_module(m)) return NULL;
    for (int k = 0; k < m->nunits; k++) {
        Unit *u = &m->units[k];
        if (u->kind == 0 && ((u->def->kind == D_OP && u->def->recursive) || (u->def->kind == D_FCN && u->def->self))) return u->def;
    }
    for (int i = 0; i < m->nnested; i++) { Def *d = recursive_in(m->nested[i]); if (d) return d; }
    return NULL;
}

static Def *sym_recursive(void) {
    for (int i = 0; i < nmodules; i++) { Def *d = recursive_in(modules[i]); if (d) return d; }
    return NULL;
}

/* Prints the behavior the solver finds to st[depth] that violates
   invariant bad, the index-th violation, or deadlocks (bad < 0); 0 if it
   does not replay. */
static int sym_report(SVal ***st, int **picks, int *nenabled, int **enabled, int depth, int bad, int violated, int from, int index) {
    while (sat_solve(&violated, 1) && !sym_enabled_refine(from)) {}
    Value ***states;
    int *act_of, loop;
    if (!sym_behavior(st, picks, nenabled, enabled, depth + 1, bad, -1, 0, &loop, &states, &act_of)) return 0;
    if (bad >= 0 && !depth) {   /* as TLC reports it */
        printf("Error: Invariant %s is violated by the initial state:\n", S(invariants[bad].name));
        print_trace_state(states[0], states[0], 1);
        printf("\n");
    } else {
        if (bad >= 0) printf("Error: Invariant %s is violated.\n", S(invariants[bad].name));
        else printf("Error: Deadlock reached.\n");
        sym_print(states, act_of, depth + 1);
    }
    itf_write(states, depth + 1, -1, bad >= 0 ? index : 0);
    return 1;
}

/* That st[depth] is in the model, as TLC keeps a state to go on from: it
   satisfies the constraints, and the step into it the action constraints.
   TLC checks the invariants of a state outside it, and finds its steps
   for deadlock, but takes none of them. */
static int sym_kept(SVal ***st, int depth) {
    int l = L_TRUE;
    for (int i = 0; i < nconstraints; i++) {
        sym_cur = st[depth], sym_next = NULL;
        l = g_and(l, sym_bool(constraints[i].expr, (SCtx){constraints[i].ctx, NULL}, P_BOTH));
    }
    for (int i = 0; depth && i < naction_constraints; i++) {
        sym_cur = st[depth - 1], sym_next = st[depth];
        l = g_and(l, sym_bool(action_constraints[i].expr, (SCtx){action_constraints[i].ctx, NULL}, P_BOTH));
    }
    return l;
}

/* That a behavior to st[depth] differs in its views from the one the
   solver found, as Apalache goes on past a violation: the views of each
   state, views[k], made before it was found. */
static int sym_other_views(SVal **views, int depth) {
    int same = L_TRUE;
    for (int k = 0; k <= depth; k++) same = g_and(same, sv_eq(views[k], sv_const(sv_model(views[k]))));
    return same ^ 1;
}

static int symbolic(void) {
    int typed = sym_types();   /* Apalache checks the types first */
    if (typed) return typed;
    Def *rec = sym_recursive();
    if (rec) {
        printf("Error: Symbolic checking does not support recursive operators and functions, as Apalache does not: %s, %s.\n",
               S(rec->name), loc_str(rec->where));
        return MANYAN_ERROR;
    }
    if (sym_max_error > 1 && (!view_expr || sym_cinit_name)) {
        printf("Error: Symbolic checking finds more than one violation only of a configuration with a VIEW, which tells them apart, and without -cinit.\n");
        return MANYAN_ERROR;
    }
    sat_init();
    SVal ***st = NEWN(SVal **, sym_length + 1);
    int **picks = NEWN(int *, sym_length + 1), **enabled = NEWN(int *, sym_length + 1), *nenabled = NEWN(int, sym_length + 1);
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {
        handler = NULL;
        printf("Error: ");
        print_error_text();
        return MANYAN_ERROR;
    }
    asg_check(init_expr, 1);
    if (next_expr) asg_check(next_expr, 0);
    sym_init = sym_primed = 1;
    Branch *init = sym_cinit_name ? sym_constants() : &(Branch){L_TRUE, NULL};
    if (init) sat_unit(init->guard);
    sym_init = sym_primed = 0;
    for (int i = 0; init && i < nsym_assumes; i++) {   /* of the constants chosen, as Apalache assumes them */
        Unit *u = sym_assumes[i];
        SVal *v = sym(u->expr, (SCtx){root_ctx, NULL}, P_POS);
        if (v->kind == SV_UNDEF) { printf("Error: Evaluating assumption %s failed.\n%s\n", loc_str(u->expr), v->u.err); return MANYAN_VIOLATION_ASSUMPTION; }
        int l = sv_lit(v, u->expr);
        if (l == L_FALSE) { printf("Error: Assumption %s is false.\n", loc_str(u->expr)); return MANYAN_VIOLATION_ASSUMPTION; }
        sat_unit(l);
    }
    sym_init = sym_primed = 1;
    if (init) init = act_step(init_expr, root_ctx, "The initial predicate");
    sym_init = sym_primed = 0;
    sym_gen_step = -1;
    if (init) {
        sat_unit(init->guard);
        st[0] = init->next;
    }
    /* stuck: no behavior goes on, which is a deadlock if they are checked */
    if (ntemporal_props) collect_fairnesses();
    sym_disabled = NEWN(int *, nfairs + 1);
    for (int f = 0; f < nfairs; f++) sym_disabled[f] = NEWN(int, sym_length + 2);
    sym_negated = NEWN(TF *, ntemporal_props + 1);
    for (int p = 0; p < ntemporal_props; p++) {   /* and the fairness that is no WF or SF, as TLC checks it */
        sym_negated[p] = to_tf(temporal_props[p].expr, temporal_props[p].ctx, 1);
        for (int i = nfair_rest - 1; i >= 0; i--) sym_negated[p] = tf_new(TF_AND, to_tf(fair_rest[i], fair_rest_c[i], 0), sym_negated[p]);
    }
    int depth = 0, bad = -1, prop = -1, stutter = 0, stuck = !init || !sym_solve(NULL, 0), none = stuck, outside = 0;
    int found = 0;   /* the violations reported, before the last one */
    int as_tlc = (nfairness && ntemporal_props) || nconstraints || naction_constraints;   /* TLC's verdict, where Apalache has none */
    int dead = -1, violated = L_FALSE, from = 0;   /* the depth of a deadlock, as TLC finds it; the last violation's literal, and its first ENABLED */
    Value ***states = NULL;   /* the lasso violating prop, at lasso_depth */
    int *act_of = NULL, loop = 0, lasso_depth = 0;
    SVal **views = NEWN(SVal *, sym_length + 1);
    for (; !stuck; depth++) {
        if (sym_max_error > 1) {
            sym_cur = st[depth], sym_next = NULL;
            views[depth] = sym(view_expr, (SCtx){root_ctx, NULL}, P_BOTH);
        }
        for (int i = 0; i < ninvariants && bad < 0; i++) {
            from = nsym_enableds;
            violated = sym_violated(i, st, depth);
            while (bad < 0 && sat_solve(&violated, 1)) {
                if (!sym_enabled_refine(from)) continue;
                if (found + 1 == sym_max_error) { bad = i; break; }
                int ok = sym_report(st, picks, nenabled, enabled, depth, i, violated, from, found + 1);
                handler = &here;
                if (!ok) return MANYAN_ERROR;
                found++;
                sat_unit(sym_other_views(views, depth));
            }
        }
        int kept = sym_kept(st, depth);
        if (as_tlc && check_deadlock && bad < 0 && nactions) {   /* TLC checks every state for deadlock, before any property */
            from = nsym_enableds;
            violated = sym_dead(st, depth, kept);
            while (sat_solve(&violated, 1)) if (sym_enabled_refine(from)) { dead = depth; break; }
        }
        for (int p = 0; p < ntemporal_props && bad < 0 && dead < 0 && prop < 0; p++) {
            if (sym_lasso_violated(p, sym_loop(st, depth), kept)) prop = p;
            else if (as_tlc && sym_lasso_violated(p, sym_stutter(st, depth), kept)) prop = p, stutter = 1;
            if (prop < 0) continue;
            if (!sym_behavior(st, picks, nenabled, enabled, depth + 1, -1, prop, stutter, &loop, &states, &act_of)) return MANYAN_ERROR;
            handler = &here;
            lasso_depth = depth;
        }
        if (bad >= 0 || dead >= 0 || (prop >= 0 && !(as_tlc && (ninvariants || check_deadlock))) || depth == sym_length || !nactions) break;
        if (kept != L_TRUE && !sym_solve(&kept, 1)) { stuck = outside = 1; break; }   /* no behavior goes on in the model */
        sat_unit(kept);
        Branch **steps = NEWN(Branch *, nactions), *by = NEWN(Branch, nactions);
        enabled[depth] = NEWN(int, nactions);
        sym_gen_step = depth + 1;
        for (int k = 0; k < nactions; k++) {
            sym_cur = st[depth];
            steps[k] = act_step(actions[k].e, actions[k].c, "The action");
            if (steps[k]) { by[nenabled[depth]] = *steps[k]; enabled[depth][nenabled[depth]++] = k; }
        }
        sym_gen_step = -1;
        picks[depth] = one_hot(nenabled[depth]);
        Branch step = nenabled[depth] ? merge_branches(by, nenabled[depth], picks[depth]) : (Branch){L_FALSE, NULL};
        if (!sym_solve(&step.guard, 1)) { stuck = 1; break; }
        sat_unit(step.guard);
        st[depth + 1] = step.next;
    }
    if (bad >= 0 || dead >= 0) {
        int ok = sym_report(st, picks, nenabled, enabled, depth, bad, violated, from, found + 1);
        handler = NULL;
        return !ok ? MANYAN_ERROR : bad >= 0 ? MANYAN_VIOLATION_SAFETY : MANYAN_VIOLATION_DEADLOCK;
    }
    if (prop < 0 && found) {   /* the views of the violations left no more */
        handler = NULL;
        return MANYAN_VIOLATION_SAFETY;
    }
    if (prop < 0 && !(stuck && check_deadlock && !outside && !as_tlc)) {
        handler = NULL;
        printf("Model checking completed. No error has been found");
        if (none) printf(". No state satisfies the initial predicate.\n");
        else if (stuck && !outside) printf(". No behavior has more than %d steps.\n", depth);
        else printf(" in behaviors of up to %ld steps.\n", outside ? depth : sym_length);   /* the model's every behavior */
        return MANYAN_OK;
    }
    if (none) {
        handler = NULL;
        printf("Error: Deadlock reached.\nError: No state satisfies the initial predicate.\n");
        return MANYAN_VIOLATION_DEADLOCK;
    }
    if (prop < 0) {
        int ok = sym_report(st, picks, nenabled, enabled, depth, -1, L_TRUE, nsym_enableds, found + 1);
        handler = NULL;
        return ok ? MANYAN_VIOLATION_DEADLOCK : MANYAN_ERROR;
    }
    handler = NULL;
    int n = lasso_depth + stutter;
    print_violated(states, n, loop);   /* as TLC prints a lasso */
    itf_write(states, n, loop, 1);
    printf("Error: The following behavior constitutes a counter-example:\n\n");
    for (int i = 0; i < n; i++) print_numbered(i + 1, act_of[i], states[i], i ? states[i - 1] : NULL, states[i + (i < lasso_depth)]);
    if (stutter) {
        printf("State %d: Stuttering\n", n + 1);
        return MANYAN_VIOLATION_LIVENESS;
    }
    printf("Back to state %d: ", loop + 1);
    action_label(act_of[lasso_depth]);
    printf("\n\n");
    return MANYAN_VIOLATION_LIVENESS;
}

#ifdef __clang__
#pragma clang attribute pop
#endif

/* ---------------------------------------------------------------- types */

/* -typecheck: Apalache's type checker, Snowcat (Apalache 0.63.0, Type
   System 1.2 with rows). Each definition is typed from @type annotations
   in the comments before it and from its body: its type is the most
   general one constraints on it allow, solved by unification, and an
   operator is polymorphic in the variables its use leaves free.
   Constraints are solved as Apalache's ConstraintSolver solves them: an
   equation at once, a choice of overloaded signatures once only one of
   them fits; a definition whose constraints have no solution is a type
   error. */

enum { TY_VAR, TY_INT, TY_BOOL, TY_STR, TY_REAL, TY_CONST, TY_SET, TY_SEQ, TY_FUN, TY_OPER, TY_TUP, TY_SPARSE,
       TY_ROW, TY_REC, TY_VARIANT, TY_OLDREC };

typedef struct Type Type;
struct Type {
    int kind;
    int n;          /* TY_OPER: parameters; TY_TUP, TY_SPARSE, TY_ROW, TY_OLDREC: elements */
    int var;        /* TY_VAR: its number; TY_CONST: its name */
    int *keys;      /* TY_SPARSE: indices, ascending; TY_ROW, TY_OLDREC: field names, in order */
    Type **args;    /* TY_SET, TY_SEQ: the element; TY_FUN: argument, result; TY_OPER: parameters, result;
                       TY_REC, TY_VARIANT: the row; others: elements */
    Type *tail;     /* TY_ROW: its variable, or NULL for a closed row */
};

static Type ty_int = {.kind = TY_INT}, ty_bool = {.kind = TY_BOOL}, ty_str = {.kind = TY_STR}, ty_real = {.kind = TY_REAL};

static Type *ty_new(int kind, int n) {
    Type *t = NEW(Type);
    t->kind = kind;
    t->n = n;
    if (n) t->args = NEWN(Type *, n + (kind == TY_OPER));
    if (n && (kind == TY_SPARSE || kind == TY_ROW || kind == TY_OLDREC)) t->keys = NEWN(int, n);
    return t;
}

static Type *ty_of(int kind, Type *a) {
    Type *t = ty_new(kind, 0);
    t->args = NEWN(Type *, 2);
    t->args[0] = a;
    return t;
}

static Type *ty_fun(Type *a, Type *b) {
    Type *t = ty_of(TY_FUN, a);
    t->args[1] = b;
    return t;
}

static Type *ty_oper(int n, Type **params, Type *res) {
    Type *t = ty_new(TY_OPER, n);
    if (!n) t->args = NEWN(Type *, 1);
    for (int i = 0; i < n; i++) t->args[i] = params[i];
    t->args[n] = res;
    return t;
}

static Type *ty_tup(int n, Type **elems) {
    Type *t = ty_new(TY_TUP, n);
    for (int i = 0; i < n; i++) t->args[i] = elems[i];
    return t;
}

static int field_cmp(int a, int b) { return strcmp(S(a), S(b)); }

/* A row of fields, sorted by name, and its variable. */
static Type *ty_row(int n, const int *keys, Type **types, Type *tail) {
    Type *t = ty_new(TY_ROW, n);
    for (int i = 0; i < n; i++) {
        int k = i;
        while (k > 0 && field_cmp(t->keys[k - 1], keys[i]) > 0) { t->keys[k] = t->keys[k - 1]; t->args[k] = t->args[k - 1]; k--; }
        t->keys[k] = keys[i];
        t->args[k] = types[i];
    }
    t->tail = tail;
    return t;
}

/* ---------------------------------------------------------------- unification */

static Type **ty_bind;   /* each variable's binding, NULL while free */
static int ty_nvars;
static struct { int var; Type *old; } *ty_trail;   /* the bindings made, to undo them */
static int ty_ntrail;

static Type *ty_fresh(void) {
    PUSH(ty_bind, ty_nvars, NULL);
    Type *t = ty_new(TY_VAR, 0);
    t->var = ty_nvars - 1;
    return t;
}

/* A variable of an annotation, by its name's number: never bound, renamed at each use (ty_named). */
static Type *ty_named_var(int v) {
    Type *t = ty_new(TY_VAR, 0);
    t->var = -1 - v;
    return t;
}

static void ty_set(int v, Type *t) {
    ty_trail = grow(ty_trail, ty_ntrail, sizeof *ty_trail);
    ty_trail[ty_ntrail].var = v;
    ty_trail[ty_ntrail++].old = ty_bind[v];
    ty_bind[v] = t;
}

static void ty_undo(int mark) {
    while (ty_ntrail > mark) { ty_ntrail--; ty_bind[ty_trail[ty_ntrail].var] = ty_trail[ty_ntrail].old; }
}

/* The variable a variable stands for, through bindings to variables. */
static Type *ty_root(Type *t) {
    while (t->kind == TY_VAR && ty_bind[t->var] && ty_bind[t->var]->kind == TY_VAR) t = ty_bind[t->var];
    return t;
}

/* t with its row's variable's binding merged in: its fields, and a free variable or none. */
static Type *row_norm(Type *r) {
    Type *tail = r->tail ? ty_root(r->tail) : NULL;
    if (!tail || !ty_bind[tail->var]) {
        if (tail == r->tail) return r;
        return ty_row(r->n, r->keys, r->args, tail);
    }
    Type *more = row_norm(ty_bind[tail->var]);
    int n = r->n + more->n;
    int *keys = NEWN(int, n ? n : 1);
    Type **types = NEWN(Type *, n ? n : 1);
    for (int i = 0; i < r->n; i++) keys[i] = r->keys[i], types[i] = r->args[i];
    for (int i = 0; i < more->n; i++) keys[r->n + i] = more->keys[i], types[r->n + i] = more->args[i];
    return ty_row(n, keys, types, more->tail);
}

static int ty_occurs(int v, Type *t) {
    if (t->kind == TY_VAR) {
        t = ty_root(t);
        if (t->var == v) return 1;
        return ty_bind[t->var] && ty_occurs(v, ty_bind[t->var]);
    }
    if (t->kind == TY_ROW && t->tail && ty_occurs(v, t->tail)) return 1;
    int n = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    for (int i = 0; i < n && t->args; i++) if (ty_occurs(v, t->args[i])) return 1;
    return 0;
}

static Type *ty_compute(Type *l, Type *r);

/* Apalache's unifyVarWithNonVarTerm: v, a free variable or bound to a term, with t. */
static Type *unify_var(Type *v, Type *t) {
    v = ty_root(v);
    if (ty_occurs(v->var, t)) return NULL;
    Type *bound = ty_bind[v->var];
    if (!bound) { ty_set(v->var, t); return t; }
    Type *u = ty_compute(bound, t);
    if (u && u != bound) ty_set(v->var, u);
    return u;
}

static Type *as_row(Type *t) {
    if (!t) return NULL;
    if (t->kind == TY_VAR) return ty_row(0, NULL, NULL, ty_root(t));
    return t;
}

static Type *unify_rows(Type *l, Type *r) {
    l = row_norm(l), r = row_norm(r);
    Type *lv = l->tail, *rv = r->tail;
    if (!l->n) {
        if (!lv && !rv) return r->n ? NULL : l;
        if (lv && rv) return r->n ? as_row(unify_var(lv, r)) : as_row(ty_compute(lv, rv));
        if (lv) return as_row(unify_var(lv, r));
        return r->n ? NULL : as_row(unify_var(rv, ty_row(0, NULL, NULL, NULL)));
    }
    if (!r->n) return unify_rows(r, l);
    int nshared = 0;
    for (int i = 0; i < l->n; i++)
        for (int k = 0; k < r->n; k++) nshared += l->keys[i] == r->keys[k];
    if (!nshared) {
        Type *tail = ty_fresh();
        if (!ty_compute(lv ? lv : ty_row(0, NULL, NULL, NULL), ty_row(r->n, r->keys, r->args, tail))
            || !ty_compute(rv ? rv : ty_row(0, NULL, NULL, NULL), ty_row(l->n, l->keys, l->args, tail)))
            return NULL;
        return row_norm(ty_row(l->n, l->keys, l->args, lv));
    }
    int *lk = NEWN(int, l->n), *rk = NEWN(int, r->n), nl = 0, nr = 0;
    Type **lt = NEWN(Type *, l->n), **rt = NEWN(Type *, r->n);
    for (int i = 0; i < l->n; i++) {
        int shared = 0;
        for (int k = 0; k < r->n; k++) shared |= l->keys[i] == r->keys[k];
        if (!shared) lk[nl] = l->keys[i], lt[nl++] = l->args[i];
    }
    for (int k = 0; k < r->n; k++) {
        int shared = 0;
        for (int i = 0; i < l->n; i++) shared |= l->keys[i] == r->keys[k];
        if (!shared) rk[nr] = r->keys[k], rt[nr++] = r->args[k];
    }
    Type *rest = ty_compute(ty_row(nl, lk, lt, lv), ty_row(nr, rk, rt, rv));
    if (!rest || rest->kind != TY_ROW) return NULL;
    rest = row_norm(rest);
    int n = nshared + rest->n, m = 0;
    int *keys = NEWN(int, n);
    Type **types = NEWN(Type *, n);
    for (int i = 0; i < l->n; i++)
        for (int k = 0; k < r->n; k++)
            if (l->keys[i] == r->keys[k]) {
                Type *u = ty_compute(l->args[i], r->args[k]);
                if (!u) return NULL;
                keys[m] = l->keys[i], types[m++] = u;
            }
    for (int i = 0; i < rest->n; i++) keys[m] = rest->keys[i], types[m++] = rest->args[i];
    return ty_row(n, keys, types, rest->tail);
}

/* Apalache's TypeUnifier.compute: the unifier of l and r, binding their
   variables, or NULL. */
static Type *ty_compute(Type *l, Type *r) {
    if (l->kind == TY_VAR) l = ty_root(l);
    if (r->kind == TY_VAR) r = ty_root(r);
    if (l->kind == TY_VAR && r->kind == TY_VAR) {
        if (l->var == r->var) return l;
        Type *lb = ty_bind[l->var], *rb = ty_bind[r->var];
        if (!lb) { if (rb && ty_occurs(l->var, rb)) return NULL; ty_set(l->var, r); return r; }
        if (!rb) { if (ty_occurs(r->var, lb)) return NULL; ty_set(r->var, l); return l; }
        ty_set(l->var, r);
        Type *u = ty_compute(lb, rb);
        if (u) ty_set(r->var, u);
        return u;
    }
    if (l->kind == TY_VAR) return unify_var(l, r);
    if (r->kind == TY_VAR) return unify_var(r, l);
    if (l->kind == TY_TUP && r->kind == TY_SPARSE) { Type *x = l; l = r; r = x; }
    if (l->kind == TY_SPARSE && r->kind == TY_TUP) {
        for (int i = 0; i < l->n; i++) if (l->keys[i] < 1 || l->keys[i] > r->n) return NULL;
        Type *t = ty_tup(r->n, r->args);
        for (int i = 0; i < l->n; i++)
            if (!(t->args[l->keys[i] - 1] = ty_compute(l->args[i], r->args[l->keys[i] - 1]))) return NULL;
        return t;
    }
    if (l->kind != r->kind) return NULL;
    Type *t, *u, *v;
    switch (l->kind) {
    case TY_INT: case TY_BOOL: case TY_STR: case TY_REAL: return l;
    case TY_CONST: return l->var == r->var ? l : NULL;
    case TY_SET: case TY_SEQ:
        u = ty_compute(l->args[0], r->args[0]);
        return !u ? NULL : u == l->args[0] ? l : ty_of(l->kind, u);
    case TY_FUN:
        u = ty_compute(l->args[0], r->args[0]);
        v = ty_compute(l->args[1], r->args[1]);
        return u && v ? ty_fun(u, v) : NULL;
    case TY_OPER:
        if (l->n != r->n) return NULL;
        t = ty_new(TY_OPER, l->n);
        if (!l->n) t->args = NEWN(Type *, 1);
        if (!(t->args[l->n] = ty_compute(l->args[l->n], r->args[r->n]))) return NULL;
        for (int i = 0; i < l->n; i++) if (!(t->args[i] = ty_compute(l->args[i], r->args[i]))) return NULL;
        return t;
    case TY_TUP:
        if (l->n != r->n) return NULL;
        t = ty_tup(l->n, l->args);
        for (int i = 0; i < l->n; i++) if (!(t->args[i] = ty_compute(l->args[i], r->args[i]))) return NULL;
        return t;
    case TY_SPARSE: {
        int n = l->n;
        for (int k = 0; k < r->n; k++) {
            int shared = 0;
            for (int i = 0; i < l->n; i++) shared |= l->keys[i] == r->keys[k];
            n += !shared;
        }
        t = ty_new(TY_SPARSE, n);
        int m = 0;
        for (int i = 0; i < l->n; i++) {
            t->keys[m] = l->keys[i];
            t->args[m] = l->args[i];
            for (int k = 0; k < r->n; k++)
                if (r->keys[k] == l->keys[i] && !(t->args[m] = ty_compute(l->args[i], r->args[k]))) return NULL;
            m++;
        }
        for (int k = 0; k < r->n; k++) {
            int shared = 0;
            for (int i = 0; i < l->n; i++) shared |= l->keys[i] == r->keys[k];
            if (!shared) t->keys[m] = r->keys[k], t->args[m++] = r->args[k];
        }
        for (int i = 1; i < n; i++)   /* by index */
            for (int k = i; k > 0 && t->keys[k - 1] > t->keys[k]; k--) {
                int key = t->keys[k]; t->keys[k] = t->keys[k - 1]; t->keys[k - 1] = key;
                Type *x = t->args[k]; t->args[k] = t->args[k - 1]; t->args[k - 1] = x;
            }
        return t;
    }
    case TY_ROW: return unify_rows(l, r);
    case TY_REC: case TY_VARIANT:
        u = unify_rows(l->args[0], r->args[0]);
        return u ? ty_of(l->kind, u) : NULL;
    default: return NULL;
    }
}

/* Unifies l and r, or leaves the bindings as they were. */
static Type *ty_unify(Type *l, Type *r) {
    int mark = ty_ntrail;
    Type *u = ty_compute(l, r);
    if (!u) ty_undo(mark);
    return u;
}

/* t with its variables' bindings substituted. */
static Type *ty_zonk(Type *t) {
    if (t->kind == TY_VAR) {
        t = ty_root(t);
        return ty_bind[t->var] ? ty_zonk(ty_bind[t->var]) : t;
    }
    if (t->kind == TY_ROW) {
        t = row_norm(t);
        Type *r = ty_row(t->n, t->keys, t->args, t->tail);
        for (int i = 0; i < r->n; i++) r->args[i] = ty_zonk(r->args[i]);
        return r;
    }
    int n = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    if (!n || !t->args) return t;
    Type *c = NEW(Type);
    *c = *t;
    c->args = NEWN(Type *, n + 1);
    for (int i = 0; i < n; i++) c->args[i] = ty_zonk(t->args[i]);
    return c;
}

/* The free variables of t, zonked, that are not marked, each once, in order. */
static void ty_vars(Type *t, char *mark, int **vars, int *n) {
    if (t->kind == TY_VAR) {
        if (!mark[t->var]) { mark[t->var] = 1; PUSH(*vars, *n, t->var); }
        return;
    }
    if (t->kind == TY_ROW && t->tail) ty_vars(t->tail, mark, vars, n);
    int k = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    for (int i = 0; i < k && t->args; i++) ty_vars(t->args[i], mark, vars, n);
}

/* t, zonked, with variables vars[i] renamed to to[i]. */
static Type *ty_rename(Type *t, const int *vars, Type **to, int n) {
    if (t->kind == TY_VAR) {
        for (int i = 0; i < n; i++) if (vars[i] == t->var) return to[i];
        return t;
    }
    int k = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    Type *c = NEW(Type);
    *c = *t;
    if (t->kind == TY_ROW && t->tail) c->tail = ty_rename(t->tail, vars, to, n);
    if (k && t->args) {
        c->args = NEWN(Type *, k + 1);
        for (int i = 0; i < k; i++) c->args[i] = ty_rename(t->args[i], vars, to, n);
    }
    return c;
}

/* t with each of its free variables renamed to a fresh one. */
static Type *ty_freshen(Type *t) {
    t = ty_zonk(t);
    char *mark = xcalloc((size_t)ty_nvars + 1, 1);
    int *vars = NULL, n = 0;
    ty_vars(t, mark, &vars, &n);
    free(mark);
    Type **to = NEWN(Type *, n ? n : 1);
    for (int i = 0; i < n; i++) to[i] = ty_fresh();
    Type *r = ty_rename(t, vars, to, n);
    return r;
}

/* An annotation's type, its named variables renamed to fresh ones: the same name, the same variable. */
static Type *ty_named_rec(Type *t, int **names, Type ***to, int *n) {
    if (t->kind == TY_VAR) {
        if (t->var >= 0) return t;
        for (int i = 0; i < *n; i++) if ((*names)[i] == t->var) return (*to)[i];
        Type *v = ty_fresh();
        PUSH(*names, *n, t->var);
        (*n)--;
        PUSH(*to, *n, v);
        return v;
    }
    int k = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    Type *c = NEW(Type);
    *c = *t;
    if (t->kind == TY_ROW && t->tail) c->tail = ty_named_rec(t->tail, names, to, n);
    if (k && t->args) {
        c->args = NEWN(Type *, k + 1);
        for (int i = 0; i < k; i++) c->args[i] = ty_named_rec(t->args[i], names, to, n);
    }
    return c;
}

static Type *ty_named(Type *t) {
    int *names = NULL, n = 0;
    Type **to = NULL;
    Type *r = ty_named_rec(t, &names, &to, &n);
    return r;
}

static void ty_print(Buf *b, Type *t);

static void row_print(Buf *b, Type *r, const char *sep, int variant) {
    for (int i = 0; i < r->n; i++) {
        if (i) buf_puts(b, sep);
        if (variant) { buf_printf(b, "%s(", S(r->keys[i])); ty_print(b, r->args[i]); buf_puts(b, ")"); }
        else { buf_printf(b, "%s: ", S(r->keys[i])); ty_print(b, r->args[i]); }
    }
}

/* t as Apalache prints a type. */
static void ty_print(Buf *b, Type *t) {
    if (!(t->kind == TY_VAR && t->var < 0)) t = ty_zonk(t);
    switch (t->kind) {
    case TY_VAR: {
        int v = t->var < 0 ? -1 - t->var : t->var;
        if (v < 26) buf_printf(b, "%c", 'a' + v); else buf_printf(b, "a%d", v);
        return;
    }
    case TY_INT: buf_puts(b, "Int"); return;
    case TY_BOOL: buf_puts(b, "Bool"); return;
    case TY_STR: buf_puts(b, "Str"); return;
    case TY_REAL: buf_puts(b, "Real"); return;
    case TY_CONST: buf_puts(b, S(t->var)); return;
    case TY_SET: case TY_SEQ:
        buf_puts(b, t->kind == TY_SET ? "Set(" : "Seq(");
        ty_print(b, t->args[0]);
        buf_puts(b, ")");
        return;
    case TY_FUN:
        buf_puts(b, "(");
        ty_print(b, t->args[0]);
        buf_puts(b, " -> ");
        ty_print(b, t->args[1]);
        buf_puts(b, ")");
        return;
    case TY_OPER:
        buf_puts(b, "((");
        for (int i = 0; i < t->n; i++) { if (i) buf_puts(b, ", "); ty_print(b, t->args[i]); }
        buf_puts(b, ") => ");
        ty_print(b, t->args[t->n]);
        buf_puts(b, ")");
        return;
    case TY_TUP:
        buf_puts(b, "<<");
        for (int i = 0; i < t->n; i++) { if (i) buf_puts(b, ", "); ty_print(b, t->args[i]); }
        buf_puts(b, ">>");
        return;
    case TY_SPARSE:
        buf_puts(b, "<| ");
        for (int i = 0; i < t->n; i++) { if (i) buf_puts(b, ", "); buf_printf(b, "%d: ", t->keys[i]); ty_print(b, t->args[i]); }
        buf_puts(b, " |>");
        return;
    case TY_ROW:
        buf_puts(b, "(| ");
        row_print(b, t, " | ", 0);
        if (t->tail) { buf_puts(b, t->n ? " | " : ""); ty_print(b, t->tail); }
        buf_puts(b, " |)");
        return;
    case TY_REC:
        buf_puts(b, "{ ");
        row_print(b, t->args[0], ", ", 0);
        if (t->args[0]->tail) { buf_puts(b, t->args[0]->n ? ", " : ""); ty_print(b, t->args[0]->tail); }
        buf_puts(b, " }");
        return;
    case TY_VARIANT:
        row_print(b, t->args[0], " | ", 1);
        if (t->args[0]->tail) {
            if (t->args[0]->n) { buf_puts(b, " | "); ty_print(b, t->args[0]->tail); }
            else { buf_puts(b, "Variant("); ty_print(b, t->args[0]->tail); buf_puts(b, ")"); }
        }
        return;
    case TY_OLDREC:
        buf_puts(b, "[");
        for (int i = 0; i < t->n; i++) { if (i) buf_puts(b, ", "); buf_printf(b, "%s: ", S(t->keys[i])); ty_print(b, t->args[i]); }
        buf_puts(b, "]");
        return;
    }
}

static const char *ty_text(Type *t) {
    Buf b = {0};
    ty_print(&b, t);
    char *s = strdup(b.s ? b.s : "");
    free(b.s);
    return s;
}

/* ---------------------------------------------------------------- type annotations */

static jmp_buf *tc_unwind;   /* where a typing error ends the checking */
static int tc_status;

/* Apalache's TypingInputException: the annotations are not to be read. */
static __attribute__((noreturn, format(printf, 1, 2))) void tc_input_error(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    printf("Typing input error: ");
    vprintf(fmt, ap);
    printf("\n");
    va_end(ap);
    tc_status = MANYAN_ERROR;
    longjmp(*tc_unwind, 1);
}

/* The tokens of Apalache's type grammar (Type1Lexer). */
enum { TT_IDENT, TT_INT, TT_REAL, TT_BOOL, TT_STR, TT_SET, TT_SEQ, TT_REC, TT_VARIANT, TT_NUM, TT_STRLIT,
       TT_ARROW, TT_DARROW, TT_EQ, TT_LROW, TT_RROW, TT_LTROW, TT_RTROW, TT_LPAREN, TT_RPAREN, TT_PIPE,
       TT_LBRACKET, TT_RBRACKET, TT_LCURLY, TT_RCURLY, TT_LANGLE, TT_RANGLE, TT_COMMA, TT_COLON, TT_DOLLAR };
static const char *const tt_text[] = {"", "Int", "Real", "Bool", "Str", "Set", "Seq", "Rec", "Variant", "", "",
    "->", "=>", "=", "(|", "|)", "<|", "|>", "(", ")", "|", "[", "]", "{", "}", "<<", ">>", ",", ":", "$"};

typedef struct { int kind; int id; int num; } TTok;

/* A parse in the manner of Scala's parser combinators, which Apalache's
   type parser is written in: a success, a failure (st 0) or an error
   (st 2), with the failure that went farthest, which a failed parse
   reports. A failure's position is its token's; past the end it is
   NoPosition, before every other. */
typedef struct { int st; int next; Type *t; int hasf; int fpos; const char *fmsg; } PR;

static TTok *tp_toks;
static int tp_n;

static int tp_pos(int i) { return i < tp_n ? i : -1; }

static PR pr_fail(int i, const char *msg) { return (PR){0, i, NULL, 1, tp_pos(i), msg}; }

/* Scala's selectLastFailure: the later of two failures, the first if level. */
static PR pr_last(PR r, int hasf, int fpos, const char *fmsg) {
    if (!hasf) return r;
    if (!r.hasf || r.fpos < fpos) { r.hasf = 1; r.fpos = fpos; r.fmsg = fmsg; }
    return r;
}

/* p ~ q: q's result, with the farther of the failures. */
static PR pr_then(PR p, PR q) {
    if (q.st == 2) return q;
    if (q.st == 1) return pr_last(q, p.hasf, p.fpos, p.fmsg);
    PR f = q;
    if (p.hasf && f.fpos < p.fpos) { f.fpos = p.fpos; f.fmsg = p.fmsg; }
    return f;
}

/* p | q, q given p failed: q's success with p's failure, or the farther failure, q's if level. */
static PR pr_or(PR p, PR q) {
    if (q.st == 2) return q;
    if (q.st == 1) {
        PR r = q;
        if (!r.hasf || !(p.fpos < r.fpos)) { r.hasf = 1; r.fpos = p.fpos; r.fmsg = p.fmsg; }
        return r;
    }
    return q.fpos < p.fpos ? p : q;
}

static const char *tt_found(int i) {
    TTok *t = &tp_toks[i];
    char *s = xmalloc(64 + (t->kind == TT_IDENT || t->kind == TT_STRLIT ? strlen(S(t->id)) : 0));
    if (t->kind == TT_IDENT) sprintf(s, "record field '%s'", S(t->id));
    else if (t->kind == TT_STRLIT) sprintf(s, "\"%s\"", S(t->id));
    else if (t->kind == TT_NUM) sprintf(s, "%d", t->num);
    else strcpy(s, tt_text[t->kind]);
    return s;
}

static PR tp_tok(int i, int kind) {
    if (i >= tp_n) return pr_fail(i, "end of input");
    if (tp_toks[i].kind == kind) return (PR){1, i + 1, NULL, 0, 0, NULL};
    const char *found = tt_found(i);
    char *msg = xmalloc(strlen(found) + 32);
    sprintf(msg, "'%s' expected but %s found", tt_text[kind], found);
    return pr_fail(i, msg);
}

static int camel_case(const char *s) {   /* ^[a-z]+(?:[A-Z0-9][a-z0-9]*)*$ */
    if (!islower((unsigned char)*s)) return 0;
    while (islower((unsigned char)*s)) s++;
    for (; *s; s++) if (!isalnum((unsigned char)*s)) return 0;
    return 1;
}

static int upper_case(const char *s) {
    for (; *s; s++) if (islower((unsigned char)*s)) return 0;
    return 1;
}

/* A type variable's number: a to z, or a0, a1, ...; -1 if s is none. */
static int var_number(const char *s) {
    if (s[0] >= 'a' && s[0] <= 'z' && !s[1]) return s[0] - 'a';
    if (s[0] != 'a' || !s[1]) return -1;
    long n = 0;
    for (const char *p = s + 1; *p; p++) { if (!isdigit((unsigned char)*p) || n > 100000000) return -1; n = n * 10 + (*p - '0'); }
    return (int)n;
}

/* An identifier that kind accepts: TT_IDENT for a field or tag, 'v' a variable, 'c' a constant, '$' an alias. */
static PR tp_ident(int i, int kind, const char *expected) {
    if (i >= tp_n) return pr_fail(i, "end of input");
    TTok *t = &tp_toks[i];
    const char *s = S(t->id);
    int ok = t->kind == TT_IDENT && (kind == TT_IDENT || (kind == 'v' && var_number(s) >= 0)
                                     || (kind == 'c' && upper_case(s)) || (kind == '$' && camel_case(s)));
    if (!ok) {
        char *msg = xmalloc(strlen(expected) + 10);
        sprintf(msg, "%s expected", expected);
        return pr_fail(i, msg);
    }
    PR r = {1, i + 1, NULL, 0, 0, NULL};
    if (kind == 'v') r.t = ty_named_var(var_number(s));
    else if (kind == 'c') { r.t = ty_new(TY_CONST, 0); r.t->var = t->id; }
    else if (kind == '$') {
        char *name = xmalloc(strlen(s) + 2);
        sprintf(name, "$%s", s);
        r.t = ty_new(TY_CONST, 0);
        r.t->var = intern(name);
        free(name);
    } else {
        r.t = ty_new(TY_CONST, 0);   /* a field's name */
        r.t->var = t->id;
    }
    return r;
}

static PR tp_type(int i);

/* p sep p sep ... (rep1sep; repsep if empty): the parses in *items. As
   Scala's p ~ rep(sep ~> p): rep's failure is the first (sep ~> p)'s or,
   once one succeeded, the last success's unless the next failure is farther. */
static PR tp_list(int i, PR (*item)(int), int sep, int empty, Type ***items, int *n) {
    *items = NULL;
    *n = 0;
    PR r = item(i);
    if (r.st != 1) return !empty || r.st == 2 ? r : pr_or(r, (PR){1, i, NULL, 0, 0, NULL});
    PUSH(*items, *n, r.t);
    PR last = {1, 0, NULL, 0, 0, NULL};
    int next = r.next;
    for (int k = 0;; k++) {
        PR s = tp_tok(next, sep);
        PR x = s.st == 1 ? pr_then(s, item(s.next)) : s;
        if (x.st == 2) return x;
        if (x.st == 0) {
            if (k == 0) last = (PR){1, 0, NULL, 1, x.fpos, x.fmsg};
            else last = pr_last(last, 1, x.fpos, x.fmsg);
            break;
        }
        PUSH(*items, *n, x.t);
        next = x.next;
        last = (PR){1, 0, NULL, x.hasf, x.fpos, x.fmsg};
    }
    PR done = {1, next, NULL, last.hasf, last.fpos, last.fmsg};   /* p ~ rep: rep's failure, p's if farther */
    return pr_last(done, r.hasf, r.fpos, r.fmsg);
}

/* field: Type, as one Type: a TY_CONST field name in t->tail. */
static PR tp_field_any(int i, int number) {
    PR name = number ? (i < tp_n && tp_toks[i].kind == TT_NUM ? (PR){1, i + 1, NULL, 0, 0, NULL}
                                                             : i < tp_n ? pr_fail(i, "field number expected") : pr_fail(i, "end of input"))
                     : tp_ident(i, TT_IDENT, "field name");
    if (name.st != 1) return name;
    PR r = pr_then(name, tp_tok(name.next, TT_COLON));
    if (r.st != 1) return r;
    r = pr_then(r, tp_type(r.next));
    if (r.st != 1) return r;
    Type *f = ty_new(TY_CONST, 0);
    f->var = number ? tp_toks[i].num : tp_toks[i].id;
    f->tail = r.t;
    r.t = f;
    return r;
}
static PR tp_field(int i) { return tp_field_any(i, 0); }
static PR tp_field_no(int i) { return tp_field_any(i, 1); }

/* A row or record from fields: name in tail->var, type in tail. */
static Type *fields_row(Type **items, int n, Type *tail) {
    int *keys = NEWN(int, n ? n : 1);
    Type **types = NEWN(Type *, n ? n : 1);
    for (int i = 0; i < n; i++) keys[i] = items[i]->var, types[i] = items[i]->tail;
    return ty_row(n, keys, types, tail);
}

static const char *tp_dup(Type **items, int n, const char *what) {
    for (int i = 0; i < n; i++)
        for (int k = 0; k < n; k++)
            if (i != k && items[i]->var == items[k]->var) {
                char *msg = xmalloc(strlen(S(items[i]->var)) + 40);
                sprintf(msg, "Found a duplicate %s %s in a %s", what, S(items[i]->var), what[0] == 'k' ? "record" : "variant");
                return msg;
            }
    return NULL;
}

/* Tag(Type) of a variant. */
static PR tp_option(int i) {
    PR r = tp_ident(i, TT_IDENT, "variant tag");
    if (r.st != 1) return r;
    r = pr_then(r, tp_tok(r.next, TT_LPAREN));
    if (r.st != 1) return r;
    r = pr_then(r, tp_type(r.next));
    if (r.st != 1) return r;
    Type *t = r.t;
    r = pr_then(r, tp_tok(r.next, TT_RPAREN));
    if (r.st != 1) return r;
    Type *f = ty_new(TY_CONST, 0);
    f->var = tp_toks[i].id;
    f->tail = t;
    r.t = f;
    return r;
}

/* opt(sep ~ typeVar): the variable, or none. */
static PR tp_opt_var(int i, int sep) {
    PR r = tp_tok(i, sep);
    if (r.st == 1) r = pr_then(r, tp_ident(r.next, 'v', "type variable"));
    if (r.st == 1 || r.st == 2) return r;
    return pr_or(r, (PR){1, i, NULL, 0, 0, NULL});
}

static PR tp_nofun(int i);

/* Set(T), Seq(T) */
static PR tp_of(int i, int kw, int kind) {
    PR r = tp_tok(i, kw);
    if (r.st != 1) return r;
    r = pr_then(r, tp_tok(r.next, TT_LPAREN));
    if (r.st != 1) return r;
    r = pr_then(r, tp_type(r.next));
    if (r.st != 1) return r;
    Type *t = r.t;
    r = pr_then(r, tp_tok(r.next, TT_RPAREN));
    if (r.st == 1) r.t = ty_of(kind, t);
    return r;
}

static PR tp_alt_tuple(int i) {
    PR r = tp_tok(i, TT_LANGLE);
    if (r.st != 1) return r;
    Type **items;
    int n;
    r = pr_then(r, tp_list(r.next, tp_type, TT_COMMA, 0, &items, &n));
    if (r.st != 1) return r;
    r = pr_then(r, tp_tok(r.next, TT_RANGLE));
    if (r.st == 1) r.t = ty_tup(n, items);
    return r;
}

static PR tp_alt_row(int i) {
    PR r = tp_tok(i, TT_LROW);
    if (r.st == 1) {
        Type **items;
        int n;
        r = pr_then(r, tp_list(r.next, tp_field, TT_PIPE, 1, &items, &n));
        if (r.st == 1) {
            PR v = pr_then(r, tp_opt_var(r.next, TT_PIPE));
            if (v.st == 1) {
                Type *tail = v.t;
                r = pr_then(v, tp_tok(v.next, TT_RROW));
                if (r.st == 1) { r.t = fields_row(items, n, tail); return r; }
            } else r = v;
        }
    }
    if (r.st == 2) return r;
    PR b = tp_tok(i, TT_LROW);   /* (| v |) */
    if (b.st == 1) {
        b = pr_then(b, tp_ident(b.next, 'v', "type variable"));
        if (b.st == 1) {
            Type *v = b.t;
            b = pr_then(b, tp_tok(b.next, TT_RROW));
            if (b.st == 1) b.t = ty_row(0, NULL, NULL, v);
        }
    }
    return pr_or(r, b);
}

static PR tp_alt_sparse(int i) {
    PR r = tp_tok(i, TT_LTROW);
    if (r.st != 1) return r;
    Type **items;
    int n;
    r = pr_then(r, tp_list(r.next, tp_field_no, TT_COMMA, 1, &items, &n));
    if (r.st != 1) return r;
    r = pr_then(r, tp_tok(r.next, TT_RTROW));
    if (r.st != 1) return r;
    Type *t = ty_new(TY_SPARSE, n);
    for (int k = 0; k < n; k++) {
        int at = k;
        while (at > 0 && t->keys[at - 1] > items[k]->var) { t->keys[at] = t->keys[at - 1]; t->args[at] = t->args[at - 1]; at--; }
        t->keys[at] = items[k]->var;
        t->args[at] = items[k]->tail;
    }
    r.t = t;
    return r;
}

static PR tp_alt_record(int i) {
    PR r = tp_tok(i, TT_LBRACKET);
    if (r.st != 1) return r;
    Type **items;
    int n;
    r = pr_then(r, tp_list(r.next, tp_field, TT_COMMA, 1, &items, &n));
    if (r.st != 1) return r;
    r = pr_then(r, tp_tok(r.next, TT_RBRACKET));
    if (r.st != 1) return r;
    Type *row = fields_row(items, n, NULL);
    Type *t = ty_new(TY_OLDREC, row->n);
    for (int k = 0; k < row->n; k++) t->keys[k] = row->keys[k], t->args[k] = row->args[k];
    r.t = t;
    return r;
}

/* { f: T, ..., v }: a duplicate key is an error, as Apalache's first rule gives it. */
static PR tp_alt_rowrec(int i) {
    PR r = tp_tok(i, TT_LCURLY);
    if (r.st == 1) {
        Type **items;
        int n;
        r = pr_then(r, tp_list(r.next, tp_field, TT_COMMA, 1, &items, &n));
        if (r.st == 1) {
            PR v = pr_then(r, tp_opt_var(r.next, TT_COMMA));
            if (v.st == 1) {
                Type *tail = v.t;
                PR c = pr_then(v, tp_tok(v.next, TT_RCURLY));
                if (c.st == 1) {
                    const char *dup = tp_dup(items, n, "key");
                    if (dup) return (PR){2, c.next, NULL, 1, tp_pos(c.next), dup};
                    /* the first rule's failure(""), then the second's success */
                    PR ok = c;
                    ok.t = ty_of(TY_REC, fields_row(items, n, tail));
                    return pr_or(pr_then(c, pr_fail(c.next, "")), ok);
                }
                r = c;
            } else r = v;
        }
    }
    if (r.st == 2) return r;
    /* the second rule fails where the first did; the third: { v } */
    PR b = tp_tok(i, TT_LCURLY);
    if (b.st == 1) {
        b = pr_then(b, tp_ident(b.next, 'v', "type variable"));
        if (b.st == 1) {
            Type *v = b.t;
            b = pr_then(b, tp_tok(b.next, TT_RCURLY));
            if (b.st == 1) b.t = ty_of(TY_REC, ty_row(0, NULL, NULL, v));
        }
    }
    return pr_or(r, b);
}

static PR tp_alt_variant(int i) {
    Type **items;
    int n;
    PR r = tp_list(i, tp_option, TT_PIPE, 0, &items, &n);
    if (r.st != 1) return r;
    PR v = pr_then(r, tp_opt_var(r.next, TT_PIPE));
    if (v.st != 1) return v;
    const char *dup = tp_dup(items, n, "tag");
    if (dup) return (PR){2, v.next, NULL, 1, tp_pos(v.next), dup};
    PR ok = v;
    ok.t = ty_of(TY_VARIANT, fields_row(items, n, v.t));
    return pr_or(pr_then(v, pr_fail(v.next, "")), ok);
}

static PR tp_alt_variant_var(int i) {
    PR r = tp_tok(i, TT_VARIANT);
    if (r.st != 1) return r;
    r = pr_then(r, tp_tok(r.next, TT_LPAREN));
    if (r.st != 1) return r;
    PR v = tp_ident(r.next, 'v', "type variable");
    Type *tail = v.st == 1 ? v.t : NULL;
    r = pr_then(r, v.st == 1 ? v : pr_or(v, (PR){1, r.next, NULL, 0, 0, NULL}));
    r = pr_then(r, tp_tok(r.next, TT_RPAREN));
    if (r.st == 1) r.t = ty_of(TY_VARIANT, ty_row(0, NULL, NULL, tail));
    return r;
}

static PR tp_alt_paren(int i) {
    PR r = tp_tok(i, TT_LPAREN);
    if (r.st != 1) return r;
    r = pr_then(r, tp_type(r.next));
    if (r.st != 1) return r;
    Type *t = r.t;
    r = pr_then(r, tp_tok(r.next, TT_RPAREN));
    if (r.st == 1) r.t = t;
    return r;
}

static PR tp_alt_alias(int i) {
    PR r = tp_tok(i, TT_DOLLAR);
    if (r.st != 1) return r;
    return pr_then(r, tp_ident(r.next, '$', "type constant"));
}

static PR tp_basic(int i, int kw, Type *t) {
    PR r = tp_tok(i, kw);
    if (r.st == 1) r.t = t;
    return r;
}

static PR tp_nofun(int i) {
    PR r = tp_basic(i, TT_INT, &ty_int);
    int tries = 0;
    while (r.st == 0) {
        PR q;
        switch (tries++) {
        case 0: q = tp_basic(i, TT_REAL, &ty_real); break;
        case 1: q = tp_basic(i, TT_BOOL, &ty_bool); break;
        case 2: q = tp_basic(i, TT_STR, &ty_str); break;
        case 3: q = tp_of(i, TT_SET, TY_SET); break;
        case 4: q = tp_of(i, TT_SEQ, TY_SEQ); break;
        case 5: q = tp_alt_tuple(i); break;
        case 6: q = tp_alt_row(i); break;
        case 7: q = tp_alt_sparse(i); break;
        case 8: q = tp_alt_record(i); break;
        case 9: q = tp_alt_rowrec(i); break;
        case 10: q = tp_alt_variant(i); break;
        case 11: q = tp_alt_variant_var(i); break;
        case 12: q = tp_ident(i, 'v', "type variable"); break;
        case 13: q = tp_ident(i, 'c', "type constant"); break;
        case 14: q = tp_alt_alias(i); break;
        case 15: q = tp_alt_paren(i); break;
        default: return r;
        }
        r = pr_or(r, q);
    }
    return r;
}

/* operatorArgs: ( T, ... ) or one; the list in *args. */
static PR tp_args(int i, Type ***args, int *n) {
    PR r = tp_tok(i, TT_LPAREN);
    if (r.st == 1) {
        r = pr_then(r, tp_list(r.next, tp_type, TT_COMMA, 1, args, n));
        if (r.st == 1) r = pr_then(r, tp_tok(r.next, TT_RPAREN));
        if (r.st == 1) return r;
    }
    if (r.st == 2) return r;
    PR q = tp_nofun(i);
    if (q.st == 1) { *args = NEWN(Type *, 1); (*args)[0] = q.t; *n = 1; }
    return pr_or(r, q);
}

/* The parses of typeExpr, a packrat parser's: each position's once. */
static PR *tp_memo;
static char *tp_memoized;

static PR tp_type(int i) {
    if (i <= tp_n && tp_memoized[i]) return tp_memo[i];
    Type **args;
    int n;
    PR r = tp_args(i, &args, &n);   /* operator */
    if (r.st == 1) {
        r = pr_then(r, tp_tok(r.next, TT_DARROW));
        if (r.st == 1) {
            r = pr_then(r, tp_type(r.next));
            if (r.st == 1) r.t = ty_oper(n, args, r.t);
        }
    }
    if (r.st == 0) {   /* function */
        PR f = tp_nofun(i);
        if (f.st == 1) {
            Type *from = f.t;
            f = pr_then(f, tp_tok(f.next, TT_ARROW));
            if (f.st == 1) {
                f = pr_then(f, tp_type(f.next));
                if (f.st == 1) f.t = ty_fun(from, f.t);
            }
        }
        r = pr_or(r, f);
        if (r.st == 0) r = pr_or(r, tp_nofun(i));
    }
    tp_memo[i] = r;
    tp_memoized[i] = 1;
    return r;
}

/* Lexes text, as Type1Lexer; returns an error message, or NULL. */
static const char *tp_lex(const char *s) {
    tp_toks = NULL;
    tp_n = 0;
    for (;;) {
        for (;;) {   /* whitespace, line feeds and // comments */
            while (*s == ' ' || *s == '\t' || *s == '\r' || *s == '\f' || *s == '\n') s++;
            if (s[0] == '/' && s[1] == '/') { while (*s && *s != '\n') s++; continue; }
            break;
        }
        if (!*s) return NULL;
        TTok t = {0, 0, 0};
        int len = 0;
        static const struct { const char *kw; int kind; } kws[] = {
            {"Int", TT_INT}, {"Real", TT_REAL}, {"Bool", TT_BOOL}, {"Str", TT_STR}, {"Set", TT_SET},
            {"Seq", TT_SEQ}, {"Rec", TT_REC}, {"Variant", TT_VARIANT}};
        for (size_t k = 0; k < sizeof kws / sizeof *kws && !len; k++) {
            size_t n = strlen(kws[k].kw);
            if (!strncmp(s, kws[k].kw, n) && !(isalnum((unsigned char)s[n]) || s[n] == '_')) { len = (int)n; t.kind = kws[k].kind; }
        }
        if (len) {
        } else if (isalpha((unsigned char)*s) || *s == '_') {
            while (isalnum((unsigned char)s[len]) || s[len] == '_') len++;
            t.kind = TT_IDENT;
            t.id = intern_n(s, len);
        } else if (isdigit((unsigned char)*s)) {
            while (isdigit((unsigned char)s[len])) len++;
            t.kind = TT_NUM;
            t.num = atoi(s);
        } else if (*s == '"' && strchr(s + 1, '"')) {
            len = (int)(strchr(s + 1, '"') - s) + 1;
            t.kind = TT_STRLIT;
            t.id = intern_n(s + 1, len - 2);
        } else {
            static const char *const punct[] = {"->", "=>", "=", "(|", "|)", "<|", "|>", "(", ")", "|", "[", "]", "{", "}", "<<", ">>", ",", ":", "$"};
            static const int kinds[] = {TT_ARROW, TT_DARROW, TT_EQ, TT_LROW, TT_RROW, TT_LTROW, TT_RTROW, TT_LPAREN, TT_RPAREN, TT_PIPE,
                                        TT_LBRACKET, TT_RBRACKET, TT_LCURLY, TT_RCURLY, TT_LANGLE, TT_RANGLE, TT_COMMA, TT_COLON, TT_DOLLAR};
            for (size_t k = 0; k < sizeof punct / sizeof *punct && !len; k++)
                if (!strncmp(s, punct[k], strlen(punct[k]))) { len = (int)strlen(punct[k]); t.kind = kinds[k]; }
            if (!len) return "unexpected character";
        }
        tp_toks = grow(tp_toks, tp_n, sizeof *tp_toks);
        tp_toks[tp_n++] = t;
        s += len;
    }
}

/* A type annotation's type, or (alias) NAME = type; NULL with *error set if it does not parse. */
static Type *tp_parse(const char *text, int alias, int *name, const char **error) {
    if ((*error = tp_lex(text))) return NULL;
    tp_memo = NEWN(PR, tp_n + 1);
    tp_memoized = NEWN(char, tp_n + 1);
    memset(tp_memoized, 0, (size_t)tp_n + 1);
    PR r;
    int start = 0;
    if (alias) {
        r = tp_ident(0, TT_IDENT, "alias name");
        if (r.st == 1) {
            const char *s = S(tp_toks[0].id);
            if (upper_case(s)) *name = tp_toks[0].id;
            else if (camel_case(s)) {
                char *n = xmalloc(strlen(s) + 2);
                sprintf(n, "$%s", s);
                *name = intern(n);
                free(n);
            } else r = pr_fail(0, "alias name expected");
        }
        if (r.st == 1) r = pr_then(r, tp_tok(r.next, TT_EQ));
        if (r.st == 1) start = r.next;
        if (r.st == 1) r = pr_then(r, tp_type(start));
    } else {
        r = tp_type(0);
    }
    if (r.st == 1 && r.next < tp_n) r = r.hasf ? pr_fail(0, r.fmsg) : pr_fail(r.next, "end of input expected");
    if (r.st != 1) { *error = r.fmsg; return NULL; }
    return r.t;
}

/* The annotations in comments, as Apalache's CommentPreprocessor finds
   them: each @name: text; or @name(args), with its text. */
typedef struct { int name; char *text; } Note;

static int note_start(const char *s, size_t at) { return at == 0 || isspace((unsigned char)s[at - 1]) || s[at - 1] == '*'; }
static int note_end(char c) { return !c || strchr(" \n\t\r*", c); }

#define INLINE_CHARS "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_~!#\\$%^&*-+=|(){}[],:`'<>.?/\r\n \t\f"

static Note *read_notes(const char *text, int *count) {
    Note *notes = NULL;
    *count = 0;
    if (!text) return NULL;
    int one_line = 0, level = 0, parens = 0, colon = 0, in_string = 0;
    Buf b = {0};
    size_t last = 0, n = strlen(text);
    for (size_t i = 0; i < n;) {
        const char *s = text + i;
        size_t len = 0;
        if (*s == '\n' || *s == ')' || *s == ';' || *s == '"') len = 1;
        else if ((s[0] == '\\' && s[1] == '*') || (s[0] == '(' && s[1] == '*') || (s[0] == '*' && s[1] == ')')) len = 2;
        else if (s[0] == '@' && (isalpha((unsigned char)s[1]) || s[1] == '_')) for (len = 1; isalnum((unsigned char)s[len]) || s[len] == '_'; len++) {}
        if (!len) { i++; continue; }
        int good = note_start(text, i);
        int in_note = parens || colon;
        if (i > last && !((one_line && level > 0) || level > 1) && in_note) buf_add(&b, text + last, i - last);
        last = i + len;
        char look = text[last];
        int at = s[0] == '@';
        if (!in_note && !in_string && at && good && (look == ':' || look == '(')) last++;
        /* the next state */
        int np = parens, nc = colon, ns = in_string;
        if (len == 2 && s[0] == '\\') one_line = 1;
        else if (*s == '\n') one_line = 0;
        else if (*s == '"') { if (!colon) ns = !in_string; }
        else if (len == 2 && s[0] == '(') { if (!one_line) level++; }
        else if (len == 2 && s[0] == '*') { if (level > 0) { one_line = 0; level--; } else if (one_line) one_line = 0; }
        else if (*s == ')') { if (!in_string && !colon) np = nc = ns = 0; }
        else if (*s == ';') { if (!in_string && in_note) np = nc = ns = 0; }
        else if (at && good) {
            if (look == '(' && !in_note) np = 1, nc = 0, ns = 0;
            else if (look == ':' && !in_note) np = 0, nc = 1, ns = 0;
            else if (!in_note && note_end(look)) {}
            else if (!in_string) np = nc = ns = 0;
        }
        int now = np || nc;
        if (!in_note && now) { b.n = 0; buf_add(&b, s, len); buf_add(&b, &look, 1); }
        else if (in_note && now) { if (!(len == 2 && (s[0] == '\\' || s[0] == '(' || s[0] == '*'))) buf_add(&b, s, len); }
        else if (in_note && !now) {
            buf_add(&b, s, len);
            Note k = {0, strndup(b.s, b.n)};
            PUSH(notes, *count, k);
            b.n = 0;
        }
        parens = np, colon = nc, in_string = ns;
        i += len;
    }
    if (b.n) { Note k = {0, strndup(b.s, b.n)}; PUSH(notes, *count, k); }
    free(b.s);
    /* @name: text;  or  @name("text"); Apalache drops, with a warning, a
       text that does not end with ; or holds a character its
       AnnotationLexer does not take. */
    int kept = 0;
    for (int k = 0; k < *count; k++) {
        char *s = notes[k].text, *p = s + 1;
        while (isalnum((unsigned char)*p) || *p == '_') p++;
        notes[k].name = intern_n(s + 1, (int)(p - s - 1));
        if (*p == ':') {
            char *end = s + strlen(s);
            if (end == p + 1 || end[-1] != ';' || p[strspn(p + 1, INLINE_CHARS) + 1] != ';') continue;
            end--;
            memmove(s, p + 1, (size_t)(end - p - 1));
            s[end - p - 1] = 0;
        } else if (*p == '(' && strchr(p, '"') && strchr(strchr(p, '"') + 1, '"')) {
            char *q = strchr(p, '"') + 1, *e = strchr(q, '"');
            memmove(s, q, (size_t)(e - q));
            s[e - q] = 0;
        } else {
            s[0] = 0;
        }
        notes[kept++] = notes[k];
    }
    *count = kept;
    return notes;
}

/* ---------------------------------------------------------------- the checker */

/* An instance a definition is typed in: its substitutions are typed in the parent's. */
typedef struct TInst TInst;
struct TInst { Def *def; TInst *parent; };

/* What a name stands for, in an instance: a value of a type, an
   operator of a type quantified over vars, or another definition (to, in
   frame to_frame) that it gives way to. */
enum { TE_VALUE, TE_OPER, TE_ALIAS };
typedef struct { TInst *frame; Def *def; int kind; Type *t; int *q; int nq; Def *to; TInst *to_frame; } TEntry;

static TEntry *tc_entries;   /* a hash table, by frame and definition */
static int tc_nentries, tc_capentries;

static unsigned tc_hash(TInst *f, Def *d) { return (unsigned)(((uintptr_t)f * 31 + (uintptr_t)d) * 2654435761u); }

static TEntry *tc_find(TInst *f, Def *d) {
    if (!tc_capentries) return NULL;
    for (unsigned h = tc_hash(f, d) & (unsigned)(tc_capentries - 1);; h = (h + 1) & (unsigned)(tc_capentries - 1)) {
        if (!tc_entries[h].def) return NULL;
        if (tc_entries[h].def == d && tc_entries[h].frame == f) return &tc_entries[h];
    }
}

static TEntry *tc_put(TInst *f, Def *d) {
    TEntry *e = tc_find(f, d);
    if (e) return e;
    if (2 * (tc_nentries + 1) > tc_capentries) {
        TEntry *old = tc_entries;
        int cap = tc_capentries;
        tc_capentries = cap ? cap * 2 : 256;
        tc_entries = xcalloc((size_t)tc_capentries, sizeof *tc_entries);
        tc_nentries = 0;
        for (int i = 0; i < cap; i++) if (old[i].def) *tc_put(old[i].frame, old[i].def) = old[i];
        free(old);
    }
    unsigned h = tc_hash(f, d) & (unsigned)(tc_capentries - 1);
    while (tc_entries[h].def) h = (h + 1) & (unsigned)(tc_capentries - 1);
    tc_nentries++;
    tc_entries[h].frame = f;
    tc_entries[h].def = d;
    return &tc_entries[h];
}

static TInst **tc_frames;
static int tc_nframes;

static TInst *tc_frame_of(Def *def, TInst *parent) {
    for (int i = 0; i < tc_nframes; i++) if (tc_frames[i]->def == def && tc_frames[i]->parent == parent) return tc_frames[i];
    TInst *f = NEW(TInst);
    f->def = def;
    f->parent = parent;
    PUSH(tc_frames, tc_nframes, f);
    return f;
}

/* A constraint, as Apalache's TClause: var equals term, or one of alts.
   why says what its failure means, at at. */
enum { CL_PLAIN, CL_SET, CL_DEF, CL_ARGS, CL_SIG };   /* why */
enum { EX_NONE, EX_EQ, EX_CALL, EX_APPLY };          /* how an application's failure is explained */
typedef struct {
    Type *var, *term;
    Type **alts;
    int nalts;
    int why, expl;
    Expr *at;
    Type **args;      /* an application's arguments' types */
    int nargs;
    int name;         /* the operator's; the definition's */
} TClause;

typedef struct { TClause *c; int n; } TSolver;

static TSolver *tc_solver;
static TInst *tc_frame;
static Type **tc_env;   /* the types of the names bound around: their variables are not quantified */
static int tc_nenv;

static Type *tc(Expr *e);

static const char *tc_source(Expr *e) {
    static char *cached;
    static const char *cached_path;
    if (!e || !e->mod || !e->mod->path) return NULL;
    if (cached_path != e->mod->path) {
        free(cached);
        cached = read_file(e->mod->path);
        if (!cached) {
            for (int i = 0; standard_modules[i].name; i++) if (!strcmp(standard_modules[i].name, S(e->mod->name))) cached = strdup(standard_modules[i].text);
        }
        cached_path = e->mod->path;
    }
    if (!cached) return NULL;
    const char *p = cached;
    for (int l = 1; l < e->l1 && *p; l++) { p = strchr(p, '\n'); if (!p) return NULL; p++; }
    const char *q = p;
    int len = 0;
    for (int l = e->l1, c = 1; *q; q++) {
        if (l == e->l1 && c == e->c1) p = q;
        if (l == e->l2 && c == e->c2) { len = (int)(q - p) + 1; break; }
        if (*q == '\n') l++, c = 1; else c++;
    }
    if (len <= 0) return NULL;
    char *s = strndup(p, (size_t)len);
    for (char *x = s; *x; x++) if (*x == '\n' || *x == '\t') *x = ' ';
    return s;
}

static const char *tc_where(Expr *e) {
    char *s = xmalloc(512);
    const char *path = e && e->mod && e->mod->path ? e->mod->path : "?";
    const char *base = strrchr(path, '/');
    snprintf(s, 512, "%s:%d:%d-%d:%d", base ? base + 1 : path, e ? e->l1 : 0, e ? e->c1 : 0, e ? e->l2 : 0, e ? e->c2 : 0);
    return s;
}

static __attribute__((format(printf, 2, 3))) void tc_error(Expr *at, const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    printf("[%s]: ", tc_where(at));
    vprintf(fmt, ap);
    printf("\n");
    va_end(ap);
}

static __attribute__((noreturn)) void tc_stop(void) {
    tc_status = 120;
    longjmp(*tc_unwind, 1);
}

static void tc_add(TClause c) {
    tc_solver->c = grow(tc_solver->c, tc_solver->n, sizeof *tc_solver->c);
    tc_solver->c[tc_solver->n++] = c;
}

static void tc_eq(Type *var, Type *term, int why, Expr *at) { tc_add((TClause){var, term, NULL, 0, why, 0, at, NULL, 0, 0}); }

static const char *types_text(Type **ts, int n, const char *sep) {
    Buf b = {0};
    for (int i = 0; i < n; i++) { if (i) buf_puts(&b, sep); ty_print(&b, ts[i]); }
    char *s = strdup(b.s ? b.s : "");
    free(b.s);
    return s;
}

/* What Apalache says of a clause that has no solution. */
static void tc_explain(TClause *c) {
    if (c->why == CL_PLAIN) return;
    if (c->why == CL_SET) { tc_error(c->at, "Expected a set. Found: %s", ty_text(c->term)); return; }
    if (c->why == CL_DEF) { tc_error(c->at, "Expected %s in %s. Found: %s", ty_text(c->var), S(c->name), ty_text(c->term)); return; }
    const char *text = tc_source(c->at), *args = types_text(c->args, c->nargs, " and ");
    const char *plural = c->nargs == 1 ? "argument" : "arguments";
    if (!text) text = "";
    if (c->expl == EX_EQ)
        tc_error(c->at, "Arguments to %s should have the same type. For arguments with types %s, in expression %s",
                 S(c->name), types_text(c->args, c->nargs, ", "), text);
    else if (c->expl == EX_APPLY) tc_error(c->at, "Cannot apply the function to its argument in %s.", text);
    else if (c->expl == EX_CALL && !c->alts && c->why == CL_SIG && c->term->kind == TY_OPER)
        tc_error(c->at, "The operator %s of type %s is applied to arguments of incompatible types in %s", S(c->name), ty_text(c->term), text);
    else if (c->alts)
        tc_error(c->at, "Annotation required. Found %d matching operator signatures %s for %s %s", c->nalts,
                 types_text(c->alts, c->nalts, " or "), plural, args);
    else
        tc_error(c->at, "An operator with the signature %s cannot be applied to the provided %s of type %s",
                 ty_text(c->why == CL_ARGS ? c->var : c->term), plural, args);
}

/* Apalache's solvePartially: equations at once, a choice once only one of its alternatives fits. */
static int tc_solve_partially(TSolver *s) {
    for (int progress = 1; s->n && progress;) {
        progress = 0;
        int kept = 0;
        for (int i = 0; i < s->n; i++) {
            TClause *c = &s->c[i];
            if (!c->alts) {
                if (!ty_unify(c->var, c->term)) {
                    tc_explain(c);
                    s->n = 0;
                    return 0;
                }
                progress = 1;
                continue;
            }
            int fits = 0, which = -1;
            for (int k = 0; k < c->nalts && fits < 2; k++) {
                int mark = ty_ntrail;
                if (ty_compute(c->var, c->alts[k])) fits++, which = k;
                ty_undo(mark);
            }
            if (fits == 1) { ty_unify(c->var, c->alts[which]); progress = 1; }
            else s->c[kept++] = *c;
        }
        s->n = kept;
    }
    return 1;
}

static int tc_solve(TSolver *s) {
    if (!tc_solve_partially(s)) return 0;
    if (!s->n) return 1;
    for (int i = 0; i < s->n; i++) tc_explain(&s->c[i]);
    s->n = 0;
    return 0;
}

/* An application of an operator of one of sigs to arguments of types args: its result. */
static Type *tc_app_why(Expr *at, int expl, int name, Type **sigs, int nsigs, Type **args, int n) {
    Type *res = ty_fresh(), *oper = ty_fresh();
    Type **kept = NEWN(Type *, n ? n : 1);
    memcpy(kept, args, sizeof(Type *) * (size_t)n);
    tc_add((TClause){oper, ty_oper(n, kept, res), NULL, 0, CL_ARGS, expl, at, kept, n, name});
    if (nsigs == 1) tc_add((TClause){oper, sigs[0], NULL, 0, CL_SIG, expl, at, kept, n, name});
    else {
        Type **alts = NEWN(Type *, nsigs);
        memcpy(alts, sigs, sizeof(Type *) * (size_t)nsigs);
        tc_add((TClause){oper, NULL, alts, nsigs, CL_SIG, expl, at, kept, n, name});
    }
    return res;
}

static Type *tc_app(Expr *at, Type *sig, Type **args, int n) { return tc_app_why(at, 0, 0, &sig, 1, args, n); }

/* (T, ..., T) => R for n parameters */
static Type *sig_same(int n, Type *t, Type *res) {
    Type **ps = NEWN(Type *, n ? n : 1);
    for (int i = 0; i < n; i++) ps[i] = t;
    return ty_oper(n, ps, res);
}

static Type *sig1(Type *a, Type *res) { return ty_oper(1, &a, res); }
static Type *sig2(Type *a, Type *b, Type *res) { Type *ps[2] = {a, b}; return ty_oper(2, ps, res); }

/* The types of e's arguments, in order. */
static Type **tc_args(Expr **args, int n) {
    Type **ts = NEWN(Type *, n ? n : 1);
    for (int i = 0; i < n; i++) ts[i] = tc(args[i]);
    return ts;
}

static Type *tc_op(Expr *e, Type *sig) { Type **ts = tc_args(e->args, e->n); return tc_app(e, sig, ts, e->n); }

static int model_sort(int s);
static Type *str_type(int s);

/* mkFunLikeByArg: what f in f[x] may be, for each kind of x: function, argument and result types. */
static int fun_like(Expr *x, Type **funs, Type **argts, Type **ress) {
    Type *a = ty_fresh();
    if (x && x->kind == X_NUM && x->num >= 0) {
        Type *sparse = ty_new(TY_SPARSE, 1);
        sparse->keys[0] = (int)x->num;
        sparse->args[0] = a;
        funs[0] = ty_fun(&ty_int, a), funs[1] = ty_of(TY_SEQ, a), funs[2] = sparse;
        for (int i = 0; i < 3; i++) argts[i] = &ty_int, ress[i] = a;
        return 3;
    }
    if (x && x->kind == X_STR) {
        if (model_sort((int)x->num) >= 0) {
            Type *c = str_type((int)x->num);
            funs[0] = ty_fun(c, a), argts[0] = c, ress[0] = a;
            return 1;
        }
        int field = (int)x->num;
        funs[0] = ty_fun(&ty_str, a), argts[0] = &ty_str, ress[0] = a;
        funs[1] = ty_of(TY_REC, ty_row(1, &field, &a, ty_fresh())), argts[1] = &ty_str, ress[1] = a;
        return 2;
    }
    Type *b = ty_fresh();
    funs[0] = ty_fun(a, b), argts[0] = a, ress[0] = b;
    funs[1] = ty_of(TY_SEQ, a), argts[1] = &ty_int, ress[1] = a;
    return 2;
}

/* A model value's type: NAME_OF_SORT, as Apalache's ModelValueHandler reads it, is of type SORT; -1 for a string. */
static int model_sort(int s) {
    const char *text = S(s);
    for (const char *p = text; *p; p++) if (!isalnum((unsigned char)*p) && *p != '_') return -1;
    for (const char *of = text + strlen(text) - 4; of > text; of--) {
        if (strncmp(of, "_OF_", 4)) continue;
        const char *sort = of + 4;
        int ok = isupper((unsigned char)*sort) || *sort == '_';
        for (const char *p = sort; ok && *p; p++) ok = isupper((unsigned char)*p) || isdigit((unsigned char)*p) || *p == '_';
        if (ok) return intern(sort);
    }
    return -1;
}

static Type *str_type(int s) {
    int sort = model_sort(s);
    if (sort < 0) return &ty_str;
    Type *c = ty_new(TY_CONST, 0);
    c->var = sort;
    return c;
}

static Type *tc_tuple(Expr *at, Expr **elems, int n) {
    if (!n) return ty_of(TY_SEQ, ty_fresh());
    Type **vars = NEWN(Type *, n), *sigs[2];
    for (int i = 0; i < n; i++) vars[i] = ty_fresh();
    sigs[0] = ty_oper(n, vars, ty_tup(n, vars));
    sigs[1] = sig_same(n, vars[0], ty_of(TY_SEQ, vars[0]));
    Type **ts = tc_args(elems, n);
    return tc_app_why(at, 0, 0, sigs, 2, ts, n);
}

/* f[x]: f of type fun applied to arg x, of type argt. */
static Type *tc_apply(Expr *at, Type *fun, Expr *x, Type *argt) {
    Type *funs[3], *argts[3], *ress[3], *sigs[3];
    int n = fun_like(x, funs, argts, ress);
    for (int i = 0; i < n; i++) sigs[i] = sig2(funs[i], argts[i], ress[i]);
    Type *ts[2] = {fun, argt};
    return tc_app_why(at, EX_APPLY, 0, sigs, n, ts, 2);
}

/* Binds the names of bounds, as Apalache's translateBindings and translateBinders: their types in *elems. */
static int tc_bind(Expr *at, Bound *bs, int nb, Type ***elems, Def ***defs) {
    Type **sets = NULL;
    Def **names = NULL;
    int n = 0, nd = 0;
    for (int i = 0; i < nb; i++) {
        Bound *b = &bs[i];
        if (b->tuple) {
            for (int k = 0; k < b->n; k++) {
                Type *set = tc(b->set);
                Type **vars = NEWN(Type *, b->n);
                for (int j = 0; j < b->n; j++) vars[j] = ty_fresh();
                Type *tup = ty_tup(b->n, vars), *ts[2] = {tup, set};
                PUSH(sets, n, tc_app(at, sig2(tup, ty_of(TY_SET, tup), ty_of(TY_SET, vars[k])), ts, 2));
                PUSH(names, nd, b->defs[k]);
            }
            continue;
        }
        for (int k = 0; k < b->n; k++) {
            PUSH(sets, n, b->set ? tc(b->set) : ty_of(TY_SET, ty_fresh()));
            PUSH(names, nd, b->defs[k]);
        }
    }
    Type **vars = NEWN(Type *, n ? n : 1), **es = NEWN(Type *, n ? n : 1);
    for (int i = 0; i < n; i++) vars[i] = ty_fresh();
    for (int i = 0; i < n; i++) es[i] = ty_fresh();
    for (int i = 0; i < n; i++) tc_eq(vars[i], ty_of(TY_SET, es[i]), CL_SET, at);
    for (int i = 0; i < n; i++) tc_eq(vars[i], sets[i], CL_SET, at);
    for (int i = 0; i < n; i++) {
        TEntry *t = tc_put(tc_frame, names[i]);
        t->kind = TE_VALUE;
        t->t = es[i];
        PUSH(tc_env, tc_nenv, es[i]);
    }
    *elems = es;
    if (defs) *defs = names;
    return n;
}

/* The domain of a function over bounds: each name's type, a tuple's for a tuple, and a tuple of several. */
static Type *tc_domain(Bound *bs, int nb, Type **vars) {
    int nparts = 0, k = 0, at = 0;
    for (int i = 0; i < nb; i++) nparts += bs[i].tuple ? 1 : bs[i].n;
    Type **parts = NEWN(Type *, nparts);
    for (int i = 0; i < nb; i++) {
        if (bs[i].tuple) { parts[k++] = ty_tup(bs[i].n, vars + at); at += bs[i].n; }
        else for (int j = 0; j < bs[i].n; j++) parts[k++] = vars[at++];
    }
    return nparts == 1 ? parts[0] : ty_tup(nparts, parts);
}

/* A lambda over bounds: \A, \E, CHOOSE, { : }, [ |-> ]: the principal type given its bindings' types. */
typedef Type *(*Principal)(Type **vars, int n, Bound *bs, int nb, Type *body, void *data);

static Type *tc_lambda(Expr *at, Bound *bs, int nb, Expr *body, Principal principal, void *data) {
    int env = tc_nenv;
    Type **es;
    int n = tc_bind(at, bs, nb, &es, NULL);
    Type *bt = tc(body);
    tc_nenv = env;
    Type **vars = NEWN(Type *, n ? n : 1);
    for (int i = 0; i < n; i++) vars[i] = ty_fresh();
    Type *res = ty_fresh(), *sig = principal(vars, n, bs, nb, res, data);
    Type *lambda = ty_oper(n, es, bt);
    return tc_app(at, sig, &lambda, 1);
}

static Type *pr_bool(Type **vars, int n, Bound *bs, int nb, Type *res, void *data) {
    (void)bs, (void)nb, (void)res, (void)data;
    return sig1(ty_oper(n, vars, &ty_bool), &ty_bool);
}
static Type *pr_choose(Type **vars, int n, Bound *bs, int nb, Type *res, void *data) {
    (void)bs, (void)nb, (void)res, (void)data;
    return sig1(ty_oper(n, vars, &ty_bool), vars[0]);
}
static Type *pr_filter(Type **vars, int n, Bound *bs, int nb, Type *res, void *data) {
    (void)bs, (void)nb, (void)res, (void)data;
    return sig1(ty_oper(n, vars, &ty_bool), ty_of(TY_SET, n == 1 ? vars[0] : ty_tup(n, vars)));
}
static Type *pr_map(Type **vars, int n, Bound *bs, int nb, Type *res, void *data) {
    (void)bs, (void)nb, (void)data;
    return sig1(ty_oper(n, vars, res), ty_of(TY_SET, res));
}
static Type *pr_fcn(Type **vars, int n, Bound *bs, int nb, Type *res, void *data) {
    (void)data;
    return sig1(ty_oper(n, vars, res), ty_fun(tc_domain(bs, nb, vars), res));
}

/* [x \in S |-> e] that names itself, f, in e: a recursive function. */
static Type *tc_recfcn(Expr *at, Def *f, Bound *bs, int nb, Expr *body) {
    int nnames = 0;
    for (int i = 0; i < nb; i++) nnames += bs[i].n;
    Type *res = ty_fresh(), **args = NEWN(Type *, nnames ? nnames : 1), **others = NEWN(Type *, nnames ? nnames : 1);
    for (int i = 0; i < nnames; i++) args[i] = ty_fresh();
    Type *fun = ty_fun(tc_domain(bs, nb, args), res);
    Type *principal = sig1(sig1(fun, ty_oper(nnames, args, res)), fun);
    for (int i = 0; i < nnames; i++) others[i] = ty_fresh();
    Type *self_set = ty_of(TY_SET, ty_fun(tc_domain(bs, nb, others), ty_fresh()));
    /* the outer lambda binds f to an element of self_set */
    Type *set_var = ty_fresh(), *self = ty_fresh();
    tc_eq(set_var, ty_of(TY_SET, self), CL_SET, at);
    tc_eq(set_var, self_set, CL_SET, at);
    TEntry *t = tc_put(tc_frame, f);
    TEntry saved = *t;
    t->kind = TE_VALUE;
    t->t = self;
    t->q = NULL;
    t->nq = 0;
    PUSH(tc_env, tc_nenv, self);
    int env = tc_nenv;
    Type **es;
    int n = tc_bind(at, bs, nb, &es, NULL);
    Type *bt = tc(body);
    tc_nenv = env - 1;
    *tc_put(tc_frame, f) = saved;
    Type *inner = ty_oper(n, es, bt), *outer = sig1(self, inner);
    return tc_app(at, principal, &outer, 1);
}

static Type *tc_except_tower(Expr *e, Path *p, int j, Expr *value) {
    Expr *key = p->fields && p->fields[j] >= 0 ? NULL : p->keys[j];
    Type *kt;
    Expr lit;
    if (!key) {
        memset(&lit, 0, sizeof lit);
        lit.kind = X_STR;
        lit.num = p->fields[j];
        key = &lit;
        kt = &ty_str;
    } else {
        kt = tc(key);
    }
    Type *inner = j + 1 < p->n ? tc_except_tower(e, p, j + 1, value) : tc(value);
    Type *funs[3], *argts[3], *ress[3], *sigs[3];
    int n = fun_like(key, funs, argts, ress);
    for (int i = 0; i < n; i++) sigs[i] = sig2(argts[i], ress[i], funs[i]);
    Type *ts[2] = {kt, inner};
    return tc_app_why(e, 0, 0, sigs, n, ts, 2);
}

/* @ in an EXCEPT: the function, applied along the path so far; outer,
   the @ where the EXCEPT is, which an @ in the function means. */
typedef struct TAt TAt;
struct TAt { Expr *fun; Path *path; TAt *outer; };
static TAt tc_at;

static Type *tc_old_value(Expr *at) {
    TAt here = tc_at;
    tc_at = here.outer ? *here.outer : (TAt){0};
    Type *t = tc(here.fun);
    tc_at = here;
    for (int j = 0; j < tc_at.path->n; j++) {
        Expr *key = tc_at.path->fields && tc_at.path->fields[j] >= 0 ? NULL : tc_at.path->keys[j];
        Expr lit;
        if (!key) {
            memset(&lit, 0, sizeof lit);
            lit.kind = X_STR;
            lit.num = tc_at.path->fields[j];
            key = &lit;
        }
        t = tc_apply(at, t, key, key == &lit ? &ty_str : tc(key));
    }
    return t;
}

static Type *tc_letdef(Def *d);
static Type *lib_type(Def *d, Expr *at);
static Type *tc_decl(Def *d, Expr *at);

/* An operator's type at a use: a fresh instance of its scheme. */
/* The last instance tc_instance made: its variables q, and to what. */
static struct { int *q, nq; Type **to; } tc_made;

static Type *tc_instance(TEntry *t) {
    if (t->kind == TE_VALUE || !t->nq) return t->t;
    Type **to = NEWN(Type *, t->nq);
    for (int i = 0; i < t->nq; i++) to[i] = ty_fresh();
    tc_made.q = t->q, tc_made.nq = t->nq, tc_made.to = to;
    return ty_rename(ty_zonk(t->t), t->q, to, t->nq);
}

static TEntry *tc_lookup(Def *d) {
    for (TInst *f = tc_frame;; f = f->parent) {
        TEntry *t = tc_find(f, d);
        if (t && t->kind == TE_ALIAS) {
            TInst *saved = tc_frame;
            tc_frame = t->to_frame;
            t = tc_lookup(t->to);
            tc_frame = saved;
        }
        if (t || !f) return t;
    }
}

/* What name d stands for: a value's type, or an operator's, for a use at at. */
static Type *tc_name(Def *d, Expr *at, int *oper) {
    *oper = 1;
    if (d->kind == D_CONST || d->kind == D_VAR) { *oper = d->arity > 0; return tc_decl(d, at); }
    Type *lib = lib_type(d, at);
    if (lib) return lib;
    TEntry *t = tc_lookup(d);
    if (!t) {
        tc_error(at, "The operator %s is used before it is defined.", S(d->name));
        tc_stop();
    }
    *oper = t->kind == TE_OPER;
    return tc_instance(t);
}

/* A call of an operator of Variants, whose type is its tag's: NULL for another. */
static Type *tc_variant(Expr *e, Def *d) {
    if (!d->mod || strcmp(S(d->mod->name), "Variants") || d->kind != D_OP) return NULL;
    const char *s = S(d->name);
    int tagged = !strcmp(s, "Variant") || !strcmp(s, "VariantFilter") || !strcmp(s, "VariantGetUnsafe") || !strcmp(s, "VariantGetOrElse");
    if (!tagged && strcmp(s, "VariantTag")) return NULL;
    if (tagged && (e->n < 1 || e->args[0]->kind != X_STR)) {
        const char *text = e->n ? tc_source(e->args[0]) : NULL;
        tc_input_error("The first argument of %s must be a string, found: %s", s, text ? text : "?");
    }
    Type *a = ty_fresh(), *b = ty_fresh(), *sig;
    int tag = tagged ? (int)e->args[0]->num : 0;
    Type *variant = ty_of(TY_VARIANT, tagged ? ty_row(1, &tag, &a, b) : ty_row(0, NULL, NULL, a));
    if (!strcmp(s, "Variant")) sig = sig2(&ty_str, a, variant);
    else if (!strcmp(s, "VariantFilter")) sig = sig2(&ty_str, ty_of(TY_SET, variant), ty_of(TY_SET, a));
    else if (!strcmp(s, "VariantTag")) sig = sig1(variant, &ty_str);
    else if (!strcmp(s, "VariantGetUnsafe")) sig = sig2(&ty_str, variant, a);
    else { Type *ps[3] = {&ty_str, variant, a}; sig = ty_oper(3, ps, a); }
    return tc_op(e, sig);
}

/* An operator named as an argument, uncalled. */
static Type *tc_opname(Def *d, Expr *at) {
    int oper;
    if (d->kind == D_PARAM) { TEntry *t = tc_lookup(d); return t ? t->t : ty_fresh(); }
    if (d->nparams && d->params[0]->name == intern("#a")) {   /* a built-in operator, as operator_def wraps it: as a LAMBDA */
        if (!tc_lookup(d)) tc_letdef(d);
        return tc_instance(tc_lookup(d));
    }
    return tc_name(d, at, &oper);
}

/* The type of each call of Apalache's Gen, generic in a polymorphic
   operator; and each call of one, how its type's variables were
   instantiated there, which tells the Gen of a call. */
static struct { Expr *e; Type *t; } *gen_types;
static int ngen_types;
typedef struct { Expr *e; int *q, nq; Type **to; } CallInst;
static CallInst *call_insts;
static int ncall_insts;

/* For symbolic checking: the type of each expression typed, generic in
   a polymorphic operator, which Apalache checks once inlined. */
typedef struct { Expr *e; Type *t; int generic; } TSeen;
static TSeen *tc_seen;
static int ntc_seen;
static int tc_quiet;   /* for symbolic checking: only the errors */

static Type *tc_expr(Expr *e);
static Type *tc(Expr *e) {
    Type *t = tc_expr(e);
    if (tc_quiet) { TSeen x = {e, t, 0}; PUSH(tc_seen, ntc_seen, x); }
    return t;
}

static Type *tc_expr(Expr *e) {
    Type *a, *b, **ts;
    switch (e->kind) {
    case X_NUM: return e->num < 0 ? &ty_real : &ty_int;
    case X_STR: return str_type((int)e->num);
    case X_BOOL: return &ty_bool;
    case K_BOOLEAN: return ty_of(TY_SET, &ty_bool);
    case K_STRINGSET: return ty_of(TY_SET, &ty_str);
    case K_BOUND: {
        TEntry *t = tc_lookup(e->def);
        if (!t) { tc_error(e, "No annotation found for %s. Make sure that you've put one in front of %s.", S(e->def->name), S(e->def->name)); tc_stop(); }
        return t->t;
    }
    case K_DECL: return tc_decl(e->def, e);
    case K_CALL: case K_PARAMCALL: case K_INSTCALL: {
        Def *d = e->def;
        TInst *caller = tc_frame, *callee = tc_frame;
        for (int i = 0; e->kind == K_INSTCALL && i < e->ndefs; i++) {
            if (e->defs[i]->nparams) tc_input_error("Manyan does not type an instance with parameters: %s", S(e->defs[i]->name));
            callee = tc_frame_of(e->defs[i], callee);
        }
        if (!e->n && (d->kind == D_PARAM || (d->kind == D_OP && d->nparams) || (d->kind == D_CONST && d->arity))) {
            tc_frame = callee;   /* an operator, as an argument */
            a = tc_opname(d, e);
            tc_frame = caller;
            return a;
        }
        if ((a = tc_variant(e, d))) return a;
        ts = tc_args(e->args, e->n);
        int oper;
        tc_frame = callee;
        tc_made.nq = 0;
        a = tc_name(d, e, &oper);
        if (tc_made.nq && tc_quiet) { CallInst ci = {e, tc_made.q, tc_made.nq, tc_made.to}; PUSH(call_insts, ncall_insts, ci); }
        tc_frame = caller;
        a = !oper && !e->n ? a : tc_app_why(e, EX_CALL, d->name, &a, 1, ts, e->n);
        if (is_gen(d)) {   /* for symbolic checking to make its value */
            gen_types = xrealloc(gen_types, sizeof *gen_types * (size_t)(ngen_types + 1));
            gen_types[ngen_types].e = e, gen_types[ngen_types++].t = a;
        }
        return a;
    }
    case X_OPREF: return tc_opname(e->def, e);
    case X_LAMBDA: {
        tc_letdef(e->def);
        TEntry *t = tc_lookup(e->def);
        return tc_instance(t);
    }
    case K_AND: case K_OR: return tc_op(e, sig_same(e->n, &ty_bool, &ty_bool));
    case K_NOT: case K_ENABLED: case K_ALWAYS: case K_EVENTUALLY: return tc_op(e, sig1(&ty_bool, &ty_bool));
    case K_IMPLIES: case K_EQUIV: case K_LEADSTO: case K_WHILE: case K_CDOT: return tc_op(e, sig2(&ty_bool, &ty_bool, &ty_bool));
    case K_EQ: case K_NEQ:
        a = ty_fresh();
        ts = tc_args(e->args, e->n);
        { Type *s = sig2(a, a, &ty_bool); return tc_app_why(e, EX_EQ, intern(e->kind == K_EQ ? "=" : "/="), &s, 1, ts, 2); }
    case K_IN: case K_NOTIN: a = ty_fresh(); return tc_op(e, sig2(a, ty_of(TY_SET, a), &ty_bool));
    case K_SUBSETEQ: a = ty_of(TY_SET, ty_fresh()); return tc_op(e, sig2(a, a, &ty_bool));
    case K_CUP: case K_CAP: case K_SETMINUS: a = ty_of(TY_SET, ty_fresh()); return tc_op(e, sig2(a, a, a));
    case K_SUBSET: a = ty_of(TY_SET, ty_fresh()); return tc_op(e, sig1(a, ty_of(TY_SET, a)));
    case K_UNION: a = ty_of(TY_SET, ty_fresh()); return tc_op(e, sig1(ty_of(TY_SET, a), a));
    case K_DOMAIN: {
        Type *sigs[4];
        Type *x = ty_fresh(), *y = ty_fresh(), *z = ty_fresh(), *w = ty_fresh();
        (void)y;
        sigs[0] = sig1(ty_fun(x, ty_fresh()), ty_of(TY_SET, x));
        sigs[1] = sig1(ty_of(TY_SEQ, z), ty_of(TY_SET, &ty_int));
        sigs[2] = sig1(ty_of(TY_REC, ty_row(0, NULL, NULL, w)), ty_of(TY_SET, &ty_str));
        sigs[3] = sig1(ty_new(TY_SPARSE, 0), ty_of(TY_SET, &ty_int));
        ts = tc_args(e->args, 1);
        return tc_app_why(e, 0, 0, sigs, 4, ts, 1);
    }
    case K_PRIME: a = ty_fresh(); return tc_op(e, sig1(a, a));
    case K_UNCHANGED:
        if (e->args[0]->kind == X_TUPLE) {
            Expr *t = e->args[0];
            Type **vars = NEWN(Type *, t->n ? t->n : 1);
            for (int i = 0; i < t->n; i++) vars[i] = ty_fresh();
            Type *tup = ty_tup(t->n, vars);
            ts = tc_args(t->args, t->n);
            Type *tt = tc_app(t, ty_oper(t->n, vars, tup), ts, t->n);
            return tc_app(e, sig1(tup, &ty_bool), &tt, 1);
        }
        return tc_op(e, sig1(ty_fresh(), &ty_bool));
    case X_SQACT: case X_ANGLEACT: return tc_op(e, sig2(&ty_bool, ty_fresh(), &ty_bool));
    case X_WF: case X_SF: {
        ts = tc_args(e->args, e->n);
        Type *ps[2] = {ty_fresh(), &ty_bool};
        if (e->n == 1) return tc_app(e, sig1(&ty_bool, &ty_bool), ts, 1);
        return tc_app(e, ty_oper(2, ps, &ty_bool), ts, 2);
    }
    case K_TIMES: {
        Type **vars = NEWN(Type *, e->n), **sets = NEWN(Type *, e->n);
        for (int i = 0; i < e->n; i++) vars[i] = ty_fresh(), sets[i] = ty_of(TY_SET, vars[i]);
        return tc_op(e, ty_oper(e->n, sets, ty_of(TY_SET, ty_tup(e->n, vars))));
    }
    case X_SETENUM:
        if (!e->n) return ty_of(TY_SET, ty_fresh());
        a = ty_fresh();
        return tc_op(e, sig_same(e->n, a, ty_of(TY_SET, a)));
    case X_TUPLE: return tc_tuple(e, e->args, e->n);
    case X_RECORD: case X_RCDSET: {
        Type **vars = NEWN(Type *, e->n), **ps = NEWN(Type *, e->n);
        int *keys = NEWN(int, e->n);
        for (int i = 0; i < e->n; i++) vars[i] = ty_fresh(), keys[i] = e->segs[i].name;
        for (int i = 0; i < e->n; i++) ps[i] = e->kind == X_RCDSET ? ty_of(TY_SET, vars[i]) : vars[i];
        Type *rec = ty_of(TY_REC, ty_row(e->n, keys, vars, NULL));
        return tc_op(e, ty_oper(e->n, ps, e->kind == X_RCDSET ? ty_of(TY_SET, rec) : rec));
    }
    case X_FCNSET:
        a = ty_fresh(), b = ty_fresh();
        return tc_op(e, sig2(ty_of(TY_SET, a), ty_of(TY_SET, b), ty_of(TY_SET, ty_fun(a, b))));
    case X_FCN: return tc_lambda(e, e->bounds, e->nb, e->args[0], pr_fcn, NULL);
    case X_APPLY: {
        Type *f = tc(e->args[0]);
        Type *x = e->n == 2 ? tc(e->args[1]) : tc_tuple(e, e->args + 1, e->n - 1);
        return tc_apply(e, f, e->n == 2 ? e->args[1] : NULL, x);
    }
    case X_DOT: {
        Type *f = tc(e->args[0]);
        Expr lit;
        memset(&lit, 0, sizeof lit);
        lit.kind = X_STR;
        lit.num = e->op;
        return tc_apply(e, f, &lit, str_type(e->op));
    }
    case X_EXCEPT: {
        a = ty_fresh();
        Type **parts = NEWN(Type *, e->n);
        parts[0] = tc(e->args[0]);
        for (int i = 0; i < e->n - 1; i++) {
            TAt saved = tc_at;
            tc_at = (TAt){e->args[0], &e->paths[i], &saved};
            parts[i + 1] = tc_except_tower(e, &e->paths[i], 0, e->args[i + 1]);
            tc_at = saved;
        }
        return tc_app(e, sig_same(e->n, a, a), parts, e->n);
    }
    case X_AT:
        if (!tc_at.fun) { tc_error(e, "@ outside an EXCEPT."); tc_stop(); }
        {
            TAt saved = tc_at;
            Type *t = tc_old_value(e);
            tc_at = saved;
            return t;
        }
    case X_FORALL: case X_EXISTS: case X_TFORALL: case X_TEXISTS:
        return tc_lambda(e, e->bounds, e->nb, e->args[0], pr_bool, NULL);
    case X_CHOOSE: return tc_lambda(e, e->bounds, e->nb, e->args[0], pr_choose, NULL);
    case X_FILTER: return tc_lambda(e, e->bounds, e->nb, e->args[0], pr_filter, NULL);
    case X_MAP: return tc_lambda(e, e->bounds, e->nb, e->args[0], pr_map, NULL);
    case X_IF: a = ty_fresh(); { Type *ps[3] = {&ty_bool, a, a}; return tc_op(e, ty_oper(3, ps, a)); }
    case X_CASE: {
        int pairs = e->n / 2, other = !e->args[e->n - 2];
        int n = e->n - (other ? 1 : 0);
        Type **ps = NEWN(Type *, n), **args = NEWN(Type *, n);
        a = ty_fresh();
        int k = 0;
        if (other) { ps[k] = a; args[k++] = tc(e->args[e->n - 1]); }
        for (int i = 0; i < pairs - other; i++) {
            ps[k] = &ty_bool; args[k++] = tc(e->args[2 * i]);
            ps[k] = a; args[k++] = tc(e->args[2 * i + 1]);
        }
        return tc_app(e, ty_oper(n, ps, a), args, n);
    }
    case X_LET: {
        for (int i = 0; i < e->ndefs; i++) if (e->defs[i]->kind == D_OP || e->defs[i]->kind == D_FCN) tc_letdef(e->defs[i]);
        Type *body = tc(e->args[0]);
        a = ty_fresh();
        return tc_app(e, sig1(a, a), &body, 1);
    }
    default:
        tc_error(e, "Manyan does not type this expression.");
        tc_stop();
    }
}

/* The types of the standard modules' operators: Apalache's StandardLibrary,
   and the annotations of the modules it rewires (src/tla/__rewire_*.tla). */
static const char *const lib_types[][3] = {
    {"Naturals", "Nat", "Set(Int)"}, {"Naturals", "+", "(Int, Int) => Int"}, {"Naturals", "-", "(Int, Int) => Int"},
    {"Naturals", "*", "(Int, Int) => Int"}, {"Naturals", "^", "(Int, Int) => Int"}, {"Naturals", "%", "(Int, Int) => Int"},
    {"Naturals", "\\div", "(Int, Int) => Int"}, {"Naturals", "<", "(Int, Int) => Bool"}, {"Naturals", ">", "(Int, Int) => Bool"},
    {"Naturals", "\\leq", "(Int, Int) => Bool"}, {"Naturals", "\\geq", "(Int, Int) => Bool"}, {"Naturals", "..", "(Int, Int) => Set(Int)"},
    {"Integers", "Int", "Set(Int)"}, {"Integers", "-.", "Int => Int"},
    {"Reals", "Real", "Set(Real)"}, {"Reals", "/", "(Real, Real) => Real"}, {"Reals", "Infinity", "Real"},
    {"Bags", "IsABag", "(a -> Int) => Bool"}, {"Bags", "BagToSet", "(a -> Int) => Set(a)"},
    {"Bags", "SetToBag", "Set(a) => (a -> Int)"}, {"Bags", "BagIn", "(a, a -> Int) => Bool"},
    {"Bags", "EmptyBag", "() => (a -> Int)"}, {"Bags", "\\oplus", "(a -> Int, a -> Int) => (a -> Int)"},
    {"Bags", "\\ominus", "(a -> Int, a -> Int) => (a -> Int)"}, {"Bags", "BagUnion", "Set(a -> Int) => (a -> Int)"},
    {"Bags", "\\sqsubseteq", "(a -> Int, a -> Int) => Bool"}, {"Bags", "SubBag", "(a -> Int) => Set(a -> Int)"},
    {"Bags", "BagOfAll", "((a) => b, a -> Int) => (b -> Int)"}, {"Bags", "BagCardinality", "(a -> Int) => Int"},
    {"Bags", "CopiesIn", "(a, a -> Int) => Int"},
    {"Sequences", "Seq", "Set(a) => Set(Seq(a))"}, {"Sequences", "Len", "Seq(a) => Int"},
    {"Sequences", "\\o", "(Seq(a), Seq(a)) => Seq(a)"}, {"Sequences", "Append", "(Seq(a), a) => Seq(a)"},
    {"Sequences", "Head", "Seq(a) => a"}, {"Sequences", "Tail", "Seq(a) => Seq(a)"},
    {"Sequences", "SubSeq", "(Seq(a), Int, Int) => Seq(a)"}, {"Sequences", "SelectSeq", "(Seq(a), a => Bool) => Seq(a)"},
    {"FiniteSets", "IsFiniteSet", "Set(a) => Bool"}, {"FiniteSets", "Cardinality", "Set(a) => Int"},
    {"Apalache", ":=", "(a, a) => Bool"}, {"Apalache", "Gen", "Int => a"}, {"Apalache", "Skolem", "Bool => Bool"},
    {"Apalache", "Guess", "Set(a) => a"}, {"Apalache", "Expand", "a => a"}, {"Apalache", "ConstCardinality", "Bool => Bool"},
    {"Apalache", "MkSeq", "(Int, (Int => a)) => Seq(a)"}, {"Apalache", "SetAsFun", "Set(<<a, b>>) => (a -> b)"},
    {"Apalache", "ApaFoldSet", "((a, b) => a, a, Set(b)) => a"}, {"Apalache", "ApaFoldSeqLeft", "((a, b) => a, a, Seq(b)) => a"},
    {"Apalache", "Repeat", "((a, Int) => a, Int, a) => a"}, {"Apalache", "FunAsSeq", "((Int -> a), Int, Int) => Seq(a)"},
    {"TLC", ":>", "(a, b) => (a -> b)"}, {"TLC", "@@", "(a -> b, a -> b) => (a -> b)"}, {"TLC", "Print", "(a, b) => b"},
    {"TLC", "PrintT", "a => Bool"}, {"TLC", "Assert", "(Bool, Str) => Bool"}, {"TLC", "JavaTime", "() => Int"},
    {"TLC", "TLCGet", "b => a"}, {"TLC", "TLCSet", "(b, a) => Bool"}, {"TLC", "Permutations", "Set(a) => Set(a -> a)"},
    {"TLC", "SortSeq", "(Seq(a), (a, a) => Bool) => (Int -> a)"}, {"TLC", "RandomElement", "Set(a) => a"},
    {"TLC", "Any", "() => a"}, {"TLC", "ToString", "a => Str"}, {"TLC", "TLCEval", "a => a"},
    {"Bags", "IsABag", "(a -> Int) => Bool"}, {"Bags", "BagToSet", "(a -> Int) => Set(a)"},
    {"Bags", "SetToBag", "(Set(a)) => a -> Int"}, {"Bags", "BagIn", "(a, a -> Int) => Bool"}, {"Bags", "EmptyBag", "() => a -> Int"},
    {"Bags", "(+)", "(a -> Int, a -> Int) => a -> Int"}, {"Bags", "(-)", "(a -> Int, a -> Int) => a -> Int"},
    {"Bags", "BagUnion", "(Set(a -> Int)) => a -> Int"}, {"Bags", "\\sqsubseteq", "(a -> Int, a -> Int) => Bool"},
    {"Bags", "SubBag", "(a -> Int) => Set(a -> Int)"}, {"Bags", "BagOfAll", "((a) => b, a -> Int) => b -> Int"},
    {"Bags", "BagCardinality", "(a -> Int) => Int"}, {"Bags", "CopiesIn", "(a, a -> Int) => Int"},
    {"BagsExt", "BagAdd", "(a -> Int, a) => (a -> Int)"}, {"BagsExt", "BagRemove", "(a -> Int, a) => (a -> Int)"},
    {"BagsExt", "BagRemoveAll", "(a -> Int, a) => (a -> Int)"},
    {"BagsExt", "MapThenFoldBag", "((a, b) => b, b, a => b, Set(a) => a, a -> Int) => b"},
    {"BagsExt", "FoldBag", "((a, b) => b, b, a -> Int) => (a -> Int)"}, {"BagsExt", "SumBag", "(Int -> Int) => Int"},
    {"BagsExt", "ProductBag", "(Int -> Int) => Int"},
    {"Functions", "Restrict", "(a -> b, Set(a)) => (a -> b)"}, {"Functions", "Range", "(a -> b) => Set(b)"},
    {"Functions", "Inverse", "(a -> b, Set(a), Set(b)) => (b -> a)"}, {"Functions", "AntiFunction", "(a -> b) => (b -> a)"},
    {"Functions", "IsInjective", "(a -> b) => Bool"}, {"Functions", "Injection", "(Set(a), Set(b)) => Set(a -> b)"},
    {"Functions", "IsSurjective", "(Set(a), Set(b), a -> b) => Bool"}, {"Functions", "Surjection", "(Set(a), Set(b)) => Set(a -> b)"},
    {"Functions", "Bijection", "(Set(a), Set(b)) => Set(a -> b)"}, {"Functions", "ExistsInjection", "(Set(a), Set(b)) => Bool"},
    {"Functions", "ExistsSurjection", "(Set(a), Set(b)) => Bool"}, {"Functions", "ExistsBijection", "(Set(a), Set(b)) => Bool"},
    {"Functions", "FoldFunction", "((b, c) => c, c, a -> b) => c"},
    {"Functions", "FoldFunctionOnSet", "((b, c) => c, c, a -> b, Set(a)) => c"},
    {"FiniteSetsExt", "FoldSet", "((a, b) => b, b, Set(a)) => b"}, {"FiniteSetsExt", "SumSet", "Set(Int) => Int"},
    {"FiniteSetsExt", "ProductSet", "Set(Int) => Int"}, {"FiniteSetsExt", "ReduceSet", "((a, b) => b, Set(a), b) => b"},
    {"FiniteSetsExt", "FlattenSet", "Set(Set(a)) => Set(a)"}, {"FiniteSetsExt", "SymDiff", "(Set(a), Set(a)) => Set(a)"},
    {"FiniteSetsExt", "Quantify", "(Set(a), (a => Bool)) => Int"}, {"FiniteSetsExt", "kSubset", "(Int, Set(a)) => Set(Set(a))"},
    {"FiniteSetsExt", "Max", "Set(Int) => Int"}, {"FiniteSetsExt", "Min", "Set(Int) => Int"},
    {"FiniteSetsExt", "Choices", "Set(Set(a)) => Set(Set(a))"}, {"FiniteSetsExt", "ChooseUnique", "(Set(a), (a => Bool)) => a"},
    {"SequencesExt", "ToSet", "Seq(a) => Set(a)"}, {"SequencesExt", "SetToSeq", "Set(a) => Seq(a)"},
    {"SequencesExt", "SetToSortSeq", "(Set(a), (a, a) => Bool) => Seq(a)"}, {"SequencesExt", "TupleOf", "(Set(a), Int) => (Int -> Set(a))"},
    {"SequencesExt", "SeqOf", "(Set(a), Int) => Set(Seq(a))"}, {"SequencesExt", "BoundedSeq", "(Set(a), Int) => Set(Seq(a))"},
    {"SequencesExt", "Contains", "(Seq(a), a) => Bool"}, {"SequencesExt", "Reverse", "Seq(a) => Seq(a)"},
    {"SequencesExt", "Remove", "(Seq(a), a) => Seq(a)"}, {"SequencesExt", "ReplaceAll", "(Seq(a), a, a) => Seq(a)"},
    {"SequencesExt", "InsertAt", "(Seq(a), Int, a) => Seq(a)"}, {"SequencesExt", "ReplaceAt", "(Seq(a), Int, a) => Seq(a)"},
    {"SequencesExt", "RemoveAt", "(Seq(a), Int) => Seq(a)"}, {"SequencesExt", "Cons", "(a, Seq(a)) => Seq(a)"},
    {"SequencesExt", "Front", "Seq(a) => Seq(a)"}, {"SequencesExt", "Last", "Seq(a) => a"},
    {"SequencesExt", "IsPrefix", "(Seq(a), Seq(a)) => Bool"}, {"SequencesExt", "IsStrictPrefix", "(Seq(a), Seq(a)) => Bool"},
    {"SequencesExt", "IsSuffix", "(Seq(a), Seq(a)) => Bool"}, {"SequencesExt", "IsStrictSuffix", "(Seq(a), Seq(a)) => Bool"},
    {"SequencesExt", "Prefixes", "Seq(a) => Set(Seq(a))"}, {"SequencesExt", "CommonPrefixes", "Set(Seq(a)) => Set(Seq(a))"},
    {"SequencesExt", "LongestCommonPrefix", "Set(Seq(a)) => Seq(a)"}, {"SequencesExt", "SeqMod", "(Int, Int) => Int"},
    {"SequencesExt", "FoldSeq", "((a, b) => b, b, Seq(a)) => b"}, {"SequencesExt", "FoldLeft", "((b, a) => b, b, Seq(a)) => b"},
    {"SequencesExt", "FoldRight", "((a, b) => b, Seq(a), b) => b"}, {"SequencesExt", "FlattenSeq", "Seq(Seq(a)) => Seq(a)"},
    {"SequencesExt", "Zip", "(Seq(a), Seq(b)) => Seq(<<a, b>>)"}, {"SequencesExt", "SubSeqs", "Seq(a) => Set(Seq(a))"},
    {"SequencesExt", "IndexFirstSubSeq", "(Seq(a), Seq(a)) => Int"},
    {"SequencesExt", "ReplaceSubSeqAt", "(Int, Seq(a), Seq(a), Seq(a)) => Seq(a)"},
    {"SequencesExt", "ReplaceFirstSubSeq", "(Seq(a), Seq(a), Seq(a)) => Seq(a)"},
    {"Folds", "MapThenFoldSet", "((a, b) => b, b, c => a, Set(c) => c, Set(c)) => b"},
    {"__apalache_folds", "__ApalacheFoldSet", "((a, b) => a, a, Set(b)) => a"},
    {"__apalache_folds", "__ApalacheFoldSeq", "((a, b) => a, a, Seq(b)) => a"},
    {"__apalache_folds", "__ApalacheMkSeq", "(Int, (Int => a)) => Seq(a)"},
    {"__apalache_internal", "__NotSupportedByModelChecker", "Str => a"},
    {"__apalache_internal", "__ApalacheSeqCapacity", "Seq(a) => Int"},
    {NULL, NULL, NULL}};

static Type *lib_parsed[sizeof lib_types / sizeof *lib_types];

/* Whether module m's operators are all Apalache's library: none is typed from its body. */
static int lib_module(Module *m) {
    /* and the community modules Apalache rewires, with the types of its rewirings */
    static const char *const names[] = {"Naturals", "Integers", "Reals", "Sequences", "FiniteSets", "TLC", "Bags", "Apalache",
                                        "__apalache_folds", "__apalache_internal",
                                        "BagsExt", "Functions", "FiniteSetsExt", "SequencesExt", "Folds", NULL};
    for (int i = 0; names[i]; i++) if (!strcmp(S(m->name), names[i])) return 1;
    return m->standard;
}

static int lib_index(Def *d) {
    if (!d->mod) return -1;
    const char *m = S(d->mod->name), *n = S(d->name);
    if (!strcmp(n, "<=")) n = "\\leq";
    if (!strcmp(n, ">=")) n = "\\geq";
    for (int i = 0; lib_types[i][0]; i++) if (!strcmp(lib_types[i][0], m) && !strcmp(lib_types[i][1], n)) return i;
    return -1;
}

static Type *lib_type(Def *d, Expr *at) {
    int i = lib_index(d);
    if (i < 0) {
        if (d->mod && lib_module(d->mod) && (d->kind == D_OP || d->kind == D_FCN)) {
            tc_error(at, "Manyan has no type for %s of module %s.", S(d->name), S(d->mod->name));
            tc_stop();
        }
        return NULL;
    }
    if (!lib_parsed[i]) {
        int name;
        const char *error;
        lib_parsed[i] = tp_parse(lib_types[i][2], 0, &name, &error);
    }
    Type *t = ty_named(lib_parsed[i]);
    return t->kind == TY_OPER ? t : ty_oper(0, NULL, t);
}

/* ---------------------------------------------------------------- annotations of declarations */

/* A declaration of the module typed, in order: definitions, constants and variables, in their instances. */
typedef struct { TInst *frame; Def *def; Expr *assume; Type *annot; int has_annot; } TDecl;

static TDecl *tc_decls;
static int tc_ndecls;
static int *tc_alias_names;
static Type **tc_alias_types;
static int tc_naliases;

/* Whether d is substituted in frame f's instances. */
static int tc_substituted(TInst *f, Def *d) {
    for (; f; f = f->parent) if (subst_index(f->def, d) >= 0) return 1;
    return 0;
}

static void tc_walk(Module *m, TInst *frame, Module ***seen, int *nseen, Module *from);

/* The definition named name in m or the modules it extends, or NULL. */
static Def *own_def(Module *m, int name, int depth) {
    for (int i = 0; i < m->nunits; i++) {
        Unit *u = &m->units[i];
        if (u->kind == 0 && (u->def->kind == D_OP || u->def->kind == D_FCN) && u->def->name == name) return u->def;
    }
    for (int i = 0; i < m->nextends && depth < 32; i++) {
        Def *d = own_def(load_module(m->extends[i], m), name, depth + 1);
        if (d) return d;
    }
    return NULL;
}

static void tc_walk_instance(Def *inst, TInst *frame, Module *from) {
    Module **seen = NULL;
    int nseen = 0;
    tc_walk(inst->target, tc_frame_of(inst, frame), &seen, &nseen, inst->name ? NULL : from);
}

/* The declarations of m, its extended modules' first, as Apalache flattens
   a module. Of a module instantiated without a name in from, a definition
   from defines by its name gives way to that one, as Apalache keeps one
   definition of a name. */
static void tc_walk(Module *m, TInst *frame, Module ***seen, int *nseen, Module *from) {
    for (int i = 0; i < *nseen; i++) if ((*seen)[i] == m) return;
    PUSH(*seen, *nseen, m);
    if (lib_module(m)) return;
    for (int i = 0; i < m->nextends; i++) tc_walk(load_module(m->extends[i], m), frame, seen, nseen, from);
    for (int i = 0; i < m->nunits; i++) {
        Unit *u = &m->units[i];
        if (u->kind == 1 || (u->kind == 0 && u->def->kind == D_INST)) {
            if (!u->def->nparams && !lib_module(u->def->target)) tc_walk_instance(u->def, frame, m);
            continue;
        }
        Def *outer = from && u->kind == 0 && (u->def->kind == D_OP || u->def->kind == D_FCN) ? own_def(from, u->def->name, 0) : NULL;
        if (outer) {
            TEntry *t = tc_put(frame, u->def);
            t->kind = TE_ALIAS;
            t->to = outer;
            t->to_frame = frame->parent;
            continue;
        }
        if (u->kind == 2) {
            /* An instance brings its definitions, not its assumptions. */
            if (!frame) { TDecl d = {frame, u->def, u->expr, NULL, 0}; PUSH(tc_decls, tc_ndecls, d); }
            continue;
        }
        if (u->kind == 4 && u->def->body && u->def->kind != D_RECURSIVE) {   /* ASSUME Name == ...: Name, an operator */
            Sym *s = module_lookup(m, u->def->name);
            if (s && s->def != u->def) { TDecl d = {frame, s->def, NULL, NULL, 0}; PUSH(tc_decls, tc_ndecls, d); }
            continue;
        }
        if (u->kind != 0) continue;
        Def *d = u->def;
        if (d->kind == D_CONST || d->kind == D_VAR) { if (tc_substituted(frame, d)) continue; }
        else if (d->kind != D_OP && d->kind != D_FCN) continue;
        else if (lib_index(d) >= 0) continue;
        if (!strcmp(S(m->name), "Variants") && d->kind == D_OP && d->nparams) continue;
        TDecl x = {frame, d, NULL, NULL, 0};
        PUSH(tc_decls, tc_ndecls, x);
    }
}

/* Apalache names a declaration without an annotation as it translates
   SANY's root module, its constants then its variables, each in its
   Hashtable's order (tlc_constants), from the last: where all are the
   root module's own. */
static void tc_unannotated(void) {
    Def *last = NULL;
    int cap = root_table_cap();
    for (int i = 0; i < tc_ndecls; i++) {
        Def *d = tc_decls[i].def;
        if (!d || (d->kind != D_CONST && d->kind != D_VAR) || tc_decls[i].has_annot) continue;
        int own = 0;
        for (int k = 0; k < root->ndecls && !own; k++) own = root->decls[k] == d;
        if (tc_decls[i].frame || !own) return;
        if (!last || d->kind > last->kind || (d->kind == last->kind && java_bucket(d->name, cap) >= java_bucket(last->name, cap))) last = d;
    }
    if (last) tc_input_error("Expected a type annotation for %s %s", last->kind == D_CONST ? "CONSTANT" : "VARIABLE", S(last->name));
}

/* Apalache's ensureTypeSystem12: old records are not types of Type System 1.2. */
static int ts12(Type *t) {
    if (t->kind == TY_OLDREC) return 0;
    int n = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    for (int i = 0; i < n && t->args; i++) if (!ts12(t->args[i])) return 0;
    return 1;
}

static void tc_ensure_ts12(Type *t) {
    if (!ts12(t))
        tc_input_error("Found imprecise record types, while Type System 1.2 is enabled. "
                       "Either update the annotations, or use --features=no-rows.");
}

/* t with the aliases substituted; changed set if any was. */
static Type *tc_unalias(Type *t, int *changed) {
    if (t->kind == TY_CONST) {
        for (int i = 0; i < tc_naliases; i++) if (tc_alias_names[i] == t->var) { *changed = 1; return tc_alias_types[i]; }
        if (S(t->var)[0] == '$') tc_input_error("Missing @typeAlias: %s = <type>;", S(t->var) + 1);
        return t;
    }
    int n = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    if (!n || !t->args) return t;
    Type *c = NEW(Type);
    *c = *t;
    c->args = NEWN(Type *, n + 1);
    for (int i = 0; i < n; i++) c->args[i] = tc_unalias(t->args[i], changed);
    return c;
}

static const char *decl_name(Def *d) { return d ? S(d->name) : "ASSUME"; }

/* The annotations of the declarations: aliases, then types, as Apalache's TypeCheckerTool reads them. */
static void tc_annotations(void) {
    for (int i = 0; i < tc_ndecls; i++) {
        int n;
        Note *notes = read_notes(tc_decls[i].def ? tc_decls[i].def->notes : NULL, &n);
        for (int k = 0; k < n; k++) {
            if (strcmp(S(notes[k].name), "typeAlias")) continue;
            int name;
            const char *error;
            Type *t = tp_parse(notes[k].text, 1, &name, &error);
            if (!t) {
                printf("Parsing error in the alias annotation: %s\n", notes[k].text);
                tc_input_error("Parser error in type alias of %s: %s", decl_name(tc_decls[i].def), error);
            }
            tc_ensure_ts12(t);
            PUSH(tc_alias_names, tc_naliases, name);
            tc_naliases--;
            PUSH(tc_alias_types, tc_naliases, t);
        }
    }
    for (int tries = 100; tries > 0; tries--) {   /* the aliases' closure */
        int changed = 0;
        for (int i = 0; i < tc_naliases; i++) tc_alias_types[i] = tc_unalias(tc_alias_types[i], &changed);
        if (!changed) break;
    }
    for (int i = 0; i < tc_ndecls; i++) {
        int n, found = 0;
        Def *d = tc_decls[i].def;
        Note *notes = read_notes(d ? d->notes : NULL, &n);
        for (int k = 0; k < n; k++) {
            if (strcmp(S(notes[k].name), "type")) continue;
            if (found++) {
                int count = 0;
                for (int j = 0; j < n; j++) count += !strcmp(S(notes[j].name), "type");
                tc_input_error("Found %d @type annotations in front of %s", count, decl_name(d));
            }
            int name;
            const char *error;
            Type *t = tp_parse(notes[k].text, 0, &name, &error);
            if (!t) {
                printf("Parsing error in the type annotation: %s\n", notes[k].text);
                tc_input_error("Parser error in type annotation of %s: %s", decl_name(d), error);
            }
            tc_ensure_ts12(t);
            tc_decls[i].annot = t;
            tc_decls[i].has_annot = 1;
        }
    }
    tc_unannotated();
    for (int i = tc_ndecls - 1; i >= 0; i--) {   /* as Apalache translates them, from the last */
        Def *d = tc_decls[i].def;
        if (d && (d->kind == D_CONST || d->kind == D_VAR) && !tc_decls[i].has_annot)
            tc_input_error("Expected a type annotation for %s %s", d->kind == D_CONST ? "CONSTANT" : "VARIABLE", S(d->name));
        if (tc_decls[i].has_annot) {
            int changed = 0;
            for (int k = 0; k < 100; k++) {
                changed = 0;
                tc_decls[i].annot = tc_unalias(tc_decls[i].annot, &changed);
                if (!changed) break;
            }
        }
    }
}

/* ---------------------------------------------------------------- typing declarations */

static TDecl *tc_cur_decl;

static Type *tc_annotation(Def *d) {
    for (int i = 0; i < tc_ndecls; i++)
        if (tc_decls[i].def == d && tc_decls[i].frame == tc_frame) return tc_decls[i].has_annot ? ty_named(tc_decls[i].annot) : NULL;
    if (!d->notes) return NULL;
    int n;
    Note *notes = read_notes(d->notes, &n);   /* a LET definition's */
    Type *t = NULL;
    for (int k = 0; k < n; k++) {
        if (strcmp(S(notes[k].name), "type")) continue;
        if (t) tc_input_error("Found 2 @type annotations in front of %s", S(d->name));
        int name;
        const char *error;
        t = tp_parse(notes[k].text, 0, &name, &error);
        if (!t) {
            printf("Parsing error in the type annotation: %s\n", notes[k].text);
            tc_input_error("Parser error in type annotation of %s: %s", S(d->name), error);
        }
        tc_ensure_ts12(t);
        int changed = 0;
        for (int i = 0; i < 100; i++) { changed = 0; t = tc_unalias(t, &changed); if (!changed) break; }
    }
    return t ? ty_named(t) : NULL;
}

/* A constant's or variable's type, or its substitute's. */
static Type *tc_decl(Def *d, Expr *at) {
    for (TInst *f = tc_frame; f; f = f->parent) {
        int i = subst_index(f->def, d);
        if (i < 0) continue;
        TInst *saved = tc_frame;
        int env = tc_nenv;
        tc_frame = f->parent;
        Expr *x = f->def->subst_expr[i];
        Type *t = x->kind == X_OPREF || ((x->kind == K_CALL || x->kind == K_PARAMCALL || x->kind == K_INSTCALL) && !x->n && d->arity)
                ? tc_opname(x->def, x) : tc(x);
        tc_frame = saved;
        tc_nenv = env;
        return t;
    }
    TEntry *t = tc_find(NULL, d);
    if (!t) {
        tc_error(at, "No annotation found for %s. Make sure that you've put one in front of %s.", S(d->name), S(d->name));
        tc_stop();
    }
    return tc_instance(t);
}

/* Types definition d as Apalache types LET d IN ...: in a solver of its own,
   then quantified over the variables the names around leave free. */
static Type *tc_letdef_in(Def *d);
static Type *tc_letdef(Def *d) {
    int from = ntc_seen;
    Type *t = tc_letdef_in(d);
    if (d->nparams || tc_find(tc_frame, d)->nq)
        for (int i = from; i < ntc_seen; i++) tc_seen[i].generic = 1;
    return t;
}

static Type *tc_letdef_in(Def *d) {
    if (!tc_solve_partially(tc_solver)) tc_stop();
    Type *annot = tc_annotation(d);
    if (annot && d->nparams == 0 && annot->kind != TY_OPER) annot = ty_oper(0, NULL, annot);
    TSolver inner = {NULL, 0}, *outer = tc_solver;
    tc_solver = &inner;
    int np = d->nparams;
    Type *scheme;
    if (annot) scheme = annot;
    else {
        Type **ps = NEWN(Type *, np ? np : 1);
        for (int i = 0; i < np; i++) ps[i] = ty_fresh();
        scheme = ty_oper(np, ps, ty_fresh());
    }
    char *mark = xcalloc((size_t)ty_nvars + 1, 1);
    int *q = NULL, nq = 0;
    ty_vars(scheme, mark, &q, &nq);
    free(mark);
    TEntry *self = tc_put(tc_frame, d);
    self->kind = TE_OPER;
    self->t = scheme;
    self->q = q;
    self->nq = nq;
    int env = tc_nenv;
    Type **params = NEWN(Type *, np ? np : 1), **sets = NEWN(Type *, np ? np : 1);
    for (int i = 0; i < np; i++) {   /* each parameter: of a fresh type, an operator's for an operator */
        Def *p = d->params[i];
        if (p->arity) {
            Type **as = NEWN(Type *, p->arity);
            for (int k = 0; k < p->arity; k++) as[k] = ty_fresh();
            sets[i] = ty_of(TY_SET, ty_oper(p->arity, as, ty_fresh()));
        } else sets[i] = ty_of(TY_SET, ty_fresh());
    }
    Type **vars = NEWN(Type *, np ? np : 1);
    for (int i = 0; i < np; i++) vars[i] = ty_fresh();
    for (int i = 0; i < np; i++) params[i] = ty_fresh();
    for (int i = 0; i < np; i++) tc_eq(vars[i], ty_of(TY_SET, params[i]), CL_SET, d->where);
    for (int i = 0; i < np; i++) tc_eq(vars[i], sets[i], CL_SET, d->where);
    for (int i = 0; i < np; i++) {
        TEntry *t = tc_put(tc_frame, d->params[i]);
        t->kind = TE_VALUE;
        t->t = params[i];
        PUSH(tc_env, tc_nenv, params[i]);
    }
    if (scheme->kind == TY_OPER)
        for (int i = 0; i < np && i < scheme->n; i++) tc_eq(params[i], scheme->args[i], CL_PLAIN, d->where);
    Type *oper = ty_fresh();
    tc_add((TClause){oper, scheme, NULL, 0, CL_DEF, 0, d->where, NULL, 0, d->name});
    Type *body;
    if (d->kind == D_FCN)
        body = d->self ? tc_recfcn(d->where, d, d->bounds, d->nb, d->body) : tc_lambda(d->where, d->bounds, d->nb, d->body, pr_fcn, NULL);
    else body = tc(d->body);
    Type *def = ty_oper(np, params, body);
    tc_add((TClause){oper, def, NULL, 0, CL_DEF, 0, d->where, NULL, 0, d->name});
    if (!tc_solve(&inner)) {
        tc_error(d->where, "Error when computing the type of %s", S(d->name));
        tc_stop();
    }
    tc_solver = outer;
    tc_nenv = env;
    Type *principal = ty_zonk(def);
    /* quantified: the variables no name around has */
    mark = xcalloc((size_t)ty_nvars + 1, 1);
    int *around = NULL, naround = 0;
    for (int i = 0; i < tc_nenv; i++) ty_vars(ty_zonk(tc_env[i]), mark, &around, &naround);
    int *free_vars = NULL, nfree = 0;
    ty_vars(principal, mark, &free_vars, &nfree);
    free(mark);
    if (annot) {   /* Apalache warns of an annotation more general than the type found */
        int mark2 = ty_ntrail;
        Type *u = ty_unify(ty_freshen(principal), ty_freshen(annot));
        if (u) {
            char *m1 = xcalloc((size_t)ty_nvars + 1, 1), *m2 = xcalloc((size_t)ty_nvars + 1, 1);
            int *v1 = NULL, n1 = 0, *v2 = NULL, n2 = 0;
            ty_vars(ty_zonk(u), m1, &v1, &n1);
            ty_vars(annot, m2, &v2, &n2);
            if (n1 < n2) printf(" > %s: %s's type annotation %s is too general, inferred: %s\n", tc_where(d->where), S(d->name), ty_text(annot), ty_text(principal));
            free(m1), free(m2);
        }
        ty_undo(mark2);
    }
    self = tc_put(tc_frame, d);
    self->kind = TE_OPER;
    self->t = principal;
    self->q = free_vars;
    self->nq = nfree;
    return principal;
}

/* -typecheck: the root module's declarations, as Apalache's TypeCheckerTool checks them. */

static int typecheck(Module *m) {
    if (!tc_quiet) printf("Type checking %s.tla\n", S(m->name));
    jmp_buf here;
    tc_unwind = &here;
    tc_status = 0;
    arena = &perm_arena;
    TSolver root_solver = {NULL, 0};
    tc_solver = &root_solver;
    tc_frame = NULL;
    if (!setjmp(here)) {
        Module **seen = NULL;
        int nseen = 0;
        tc_walk(m, NULL, &seen, &nseen, NULL);
        tc_annotations();
        for (int i = 0; i < tc_ndecls; i++) {
            TDecl *x = &tc_decls[i];
            tc_cur_decl = x;
            tc_frame = x->frame;
            Def *d = x->def;
            if (x->assume) {   /* a definition of no parameters: (Bool) => Bool applied to it */
                TSolver inner = {NULL, 0}, *outer = tc_solver;
                if (!tc_solve_partially(tc_solver)) tc_stop();
                tc_solver = &inner;
                Type *body = tc(x->assume);
                tc_app(x->assume, sig1(&ty_bool, &ty_bool), &body, 1);
                if (!tc_solve(&inner)) { tc_error(x->assume, "Error when computing the type of %s", decl_name(d)); tc_stop(); }
                tc_solver = outer;
                continue;
            }
            if (d->kind == D_CONST || d->kind == D_VAR) {
                TEntry *t = tc_put(NULL, d);
                t->kind = TE_VALUE;
                t->t = ty_named(x->annot);
                char *mark = xcalloc((size_t)ty_nvars + 1, 1);
                int *q = NULL, nq = 0;
                ty_vars(t->t, mark, &q, &nq);
                free(mark);
                if (nq) t->kind = TE_OPER, t->q = q, t->nq = nq;   /* a polymorphic constant: each use an instance */
                if (d->arity) t->kind = TE_OPER;
                continue;
            }
            tc_letdef(d);
        }
        tc_frame = NULL;
        if (!tc_solve(&root_solver)) { printf("Error when computing the type of the top expression\n"); tc_status = 120; }
    }
    tc_unwind = NULL;
    if (tc_status == MANYAN_ERROR) return MANYAN_ERROR;
    if (tc_status) {
        printf(" > Snowcat asks you to fix the types. Meow.\n");
        printf("Type checker [FAILED]\n");
        return 120;
    }
    if (!tc_quiet) printf(" > Your types are purrfect!\n");
    if (!tc_quiet) printf("Type checker [OK]\n");
    return MANYAN_OK;
}

/* ---------------------------------------------------------------- Gen */

/* A string of sort (-1: Str) that Gen makes, as Apalache makes one: one
   the specification has made, or a fresh one, FRESHk or FRESHk_OF_SORT. */
static SVal *gen_atom(int sort) {
    static int fresh;
    char name[64];
    snprintf(name, sizeof name, sort < 0 ? "FRESH%d" : "FRESH%d_OF_%s", ++fresh, sort < 0 ? "" : S(sort));
    mk_str(intern(name));
    SVal *r = NULL;
    for (int i = nstrs - 1; i >= 0; i--) {   /* the fresh one last */
        if ((!strs[i].value && !strs[i].model) || model_sort(i) != sort) continue;
        for (int m = 0; m < 2; m++) {
            if (!(m ? strs[i].model : strs[i].value)) continue;
            SVal *v = sv_bits(SV_ATOM, bv_const(2 * (int64_t)i + m));
            r = r ? sv_ite(2 * sat_var(), v, r) : v;
        }
    }
    return r;
}

/* Apalache's Gen(n): any value of its type, with sets, functions and
   sequences of up to n elements, which the type checker tells. */
static SVal *gen_of(Type *t, int n, Expr *at) {
    t = ty_zonk(t);
    SVal *r;
    switch (t->kind) {
    case TY_BOOL: return sv_bool(2 * sat_var());
    case TY_INT: return sv_bits(SV_INT, bv_fresh());
    case TY_STR: return gen_atom(-1);
    case TY_CONST: return gen_atom(t->var);
    case TY_SET:
        r = sv_set(n);
        for (int i = 0; i < n; i++) set_add(r, gen_of(t->args[0], n, at), 2 * sat_var());
        return r;
    case TY_SEQ:
        r = sv_fcn(n, 0);
        for (int i = 0; i < n; i++) {
            int g = 2 * sat_var();
            if (i) sat_add2(g ^ 1, r->u.fcn.guards[i - 1]);   /* its indices are 1..Len */
            fcn_add(r, sv_int_const(i + 1), gen_of(t->args[0], n, at), g);
        }
        return r;
    case TY_FUN:
        r = sv_fcn(n, 0);
        for (int i = 0; i < n; i++) {
            fcn_add(r, gen_of(t->args[0], n, at), gen_of(t->args[1], n, at), 2 * sat_var());
            for (int j = 0; j < i; j++)   /* a key once */
                sat_add2(g_and(r->u.fcn.guards[i], r->u.fcn.guards[j]) ^ 1, sv_eq(r->u.fcn.keys[i], r->u.fcn.keys[j]) ^ 1);
        }
        return r;
    case TY_TUP:
        r = sv_fcn(t->n, 0);
        for (int i = 0; i < t->n; i++) fcn_add(r, sv_int_const(i + 1), gen_of(t->args[i], n, at), L_TRUE);
        return r;
    case TY_REC: {
        Type *row = ty_zonk(t->args[0]);
        if (row->kind != TY_ROW || (row->tail && ty_zonk(row->tail)->kind != TY_ROW)) break;
        r = sv_fcn(row->n, 1);
        for (int i = 0; i < row->n; i++) fcn_add(r, sv_const(mk_str(row->keys[i])), gen_of(row->args[i], n, at), L_TRUE);
        return r;
    }
    case TY_VARIANT: {   /* a record of one of its tags */
        Type *row = ty_zonk(t->args[0]);
        if (row->kind != TY_ROW || row->tail || !row->n) break;
        int *tag = one_hot(row->n);
        r = sv_fcn(row->n, 1);
        for (int i = 0; i < row->n; i++) fcn_add(r, sv_const(mk_str(row->keys[i])), gen_of(row->args[i], n, at), tag[i]);
        return r;
    }
    default: break;
    }
    if (t->kind == TY_VAR) fail_at(at, "Symbolic checking cannot tell the type of this Gen: the operator's parameters leave it open.");
    Buf b = {0};
    ty_print(&b, t);
    fail_at(at, "Symbolic checking cannot make a Gen of type %s.", b.s);
}

/* Apalache's check, once the operators are inlined, that each set and
   empty sequence the specification writes has one type: an empty set,
   say, needs one of its elements. The set a quantifier ranges over may be
   open, as Apalache rewrites \A x \in {}: P to TRUE. */
static int tc_seen_order(const void *a, const void *b) {
    const Expr *x = ((const TSeen *)a)->e, *y = ((const TSeen *)b)->e;
    return x < y ? -1 : x > y;
}

static Expr *mono_walk(Expr *e, Def ***seen, int *nseen);
static Expr *mono_def(Def *d, Def ***seen, int *nseen) {
    if (d->replacement) d = d->replacement;
    for (int i = 0; i < *nseen; i++) if ((*seen)[i] == d) return NULL;
    PUSH(*seen, *nseen, d);
    Expr *bad = mono_walk(d->body, seen, nseen);
    for (int i = 0; !bad && i < d->nb; i++) bad = mono_walk(d->bounds[i].set, seen, nseen);
    for (int i = 0; !bad && d->kind == D_INST && i < d->nsubst; i++) bad = mono_walk(d->subst_expr[i], seen, nseen);
    return bad;
}

static int mono_open(Expr *e) {
    if (e->kind != X_SETENUM && !(e->kind == X_TUPLE && !e->n)) return 0;
    TSeen key = {e, NULL, 0}, *x = bsearch(&key, tc_seen, (size_t)ntc_seen, sizeof *x, tc_seen_order);
    if (!x) return 0;
    while (x > tc_seen && x[-1].e == e) x--;
    for (; x < tc_seen + ntc_seen && x->e == e; x++) {
        if (x->generic) continue;
        char *mark = xcalloc((size_t)ty_nvars + 1, 1);
        int *q = NULL, nq = 0;
        ty_vars(ty_zonk(x->t), mark, &q, &nq);
        free(mark);
        if (nq) return 1;
    }
    return 0;
}

/* Repeat's count: a literal, once the constants and operators are
   inlined; an operator's parameter is its argument's. */
static int repeat_count(Expr *e) {
    if (e->kind == X_NUM || (e->kind == K_DECL && e->def->kind == D_CONST) || (e->kind == K_BOUND && e->def->kind == D_PARAM)) return 1;
    return e->kind == K_CALL && !e->n && e->def->body && repeat_count(e->def->body);
}

static int mono_repeat;   /* what mono_walk found: a Repeat of no literal count */
static int mono_fcnsets;  /* or { [S -> T] : x \in U }, a set of sets of functions Apalache would expand */
static Expr *mono_walk(Expr *e, Def ***seen, int *nseen) {
    if (!e) return NULL;
    if (mono_open(e)) return e;
    if (e->kind == K_CALL && e->n == 3 && apalache_op(e->def, "Repeat") && e->mod != e->def->mod && !repeat_count(e->args[1])) { mono_repeat = 1; return e; }
    if (e->kind == X_MAP && e->args[0]->kind == X_FCNSET && !lib_module(e->mod)) { mono_fcnsets = 1; return e; }
    Expr *bad = e->def ? mono_def(e->def, seen, nseen) : NULL;
    for (int i = 0; !bad && i < e->n; i++) bad = mono_walk(e->args[i], seen, nseen);
    for (int i = 0; !bad && i < e->nb; i++) {
        Expr *set = e->bounds[i].set;
        if ((e->kind == X_FORALL || e->kind == X_EXISTS) && mono_open(set)) for (int k = 0; !bad && k < set->n; k++) bad = mono_walk(set->args[k], seen, nseen);
        else bad = mono_walk(set, seen, nseen);
    }
    if (e->kind == X_EXCEPT)
        for (int i = 0; !bad && i < e->n - 1; i++)
            for (int k = 0; !bad && k < e->paths[i].n; k++) if (e->paths[i].fields[k] < 0) bad = mono_walk(e->paths[i].keys[k], seen, nseen);
    for (int i = 0; !bad && e->kind == X_LET && i < e->ndefs; i++) bad = mono_def(e->defs[i], seen, nseen);
    for (int i = 0; !bad && i < e->nseg; i++)
        for (int k = 0; !bad && k < e->segs[i].n; k++) bad = mono_walk(e->segs[i].args[k], seen, nseen);
    return bad;
}

/* A LET definition in e named as a constant or variable of the root
   module: Apalache, flattening the modules, refuses the two. */
static Def *let_clash(Expr *e) {
    if (!e) return NULL;
    Def *bad = NULL;
    for (int i = 0; e->kind == X_LET && !bad && i < e->ndefs; i++) {
        Sym *s = root_sym(e->defs[i]->name);
        bad = s && (s->def->kind == D_VAR || s->def->kind == D_CONST) ? e->defs[i] : let_clash(e->defs[i]->body);
    }
    for (int i = 0; !bad && i < e->n; i++) bad = let_clash(e->args[i]);
    for (int i = 0; !bad && i < e->nb; i++) bad = let_clash(e->bounds[i].set);
    return bad;
}

/* The expression Apalache refuses, of those the specification uses. */
static Expr *sym_refused(void) {
    qsort(tc_seen, (size_t)ntc_seen, sizeof *tc_seen, tc_seen_order);
    Def **seen = NULL;
    int nseen = 0;
    Expr *bad = mono_walk(init_expr, &seen, &nseen);
    if (!bad) bad = mono_walk(next_expr, &seen, &nseen);
    for (int i = 0; !bad && i < ninvariants; i++) bad = mono_walk(invariants[i].expr, &seen, &nseen);
    for (int i = 0; !bad && i < ntemporal_props; i++) bad = mono_walk(temporal_props[i].expr, &seen, &nseen);
    for (int i = 0; !bad && i < nsym_assumes; i++) bad = mono_walk(sym_assumes[i]->expr, &seen, &nseen);
    Sym *c = sym_cinit_name ? module_lookup(root, intern(sym_cinit_name)) : NULL;
    if (!bad && c) bad = mono_def(c->def, &seen, &nseen);
    return bad;
}

/* The type of a constant's configured value, as Apalache reads it: a
   model value is a string, but NAME_OF_SORT of type SORT. */
static Type *value_type(Value *v) {
    switch (v->kind) {
    case V_BOOL: return &ty_bool;
    case V_INT: return &ty_int;
    case V_STR: case V_MODEL: return str_type((int)v->u.i);
    case V_INTERVAL: return ty_of(TY_SET, &ty_int);
    case V_SET: {
        Type *elem = ty_fresh();
        for (int i = 0; i < v->n; i++) {
            Type *t = value_type(v->u.set.elems[i]);
            if (!t || !(elem = ty_unify(elem, t))) return NULL;
        }
        return ty_of(TY_SET, elem);
    }
    default: return NULL;
    }
}

/* A constant the configuration gives a value not of its type. */
static Def *sym_misvalued(void) {
    for (int i = 0; i < root->ndecls; i++) {
        Def *d = root->decls[i];
        TEntry *t = d->kind == D_CONST && d->value ? tc_find(NULL, d) : NULL;
        if (!t || t->kind != TE_VALUE) continue;
        int mark = ty_ntrail;
        Type *v = value_type(d->value);
        int ok = v && ty_unify(ty_freshen(t->t), v);
        ty_undo(mark);
        if (!ok) return d;
    }
    return NULL;
}

/* The types of the specification, for symbolic checking: as -typecheck
   checks them, printing only what is wrong. */
static int sym_open_gens;   /* whether a Gen's type is generic, for sym_typed */
static Def typed_mark;

static int ty_open(Type *t) {
    if (t->kind == TY_VAR) return 1;
    if (t->kind == TY_ROW && t->tail && ty_open(t->tail)) return 1;
    int k = t->kind == TY_SET || t->kind == TY_SEQ || t->kind == TY_REC || t->kind == TY_VARIANT ? 1
          : t->kind == TY_FUN ? 2 : t->kind == TY_OPER ? t->n + 1 : t->n;
    for (int i = 0; i < k && t->args; i++) if (ty_open(t->args[i])) return 1;
    return 0;
}

static int call_inst_order(const void *a, const void *b) {
    const Expr *x = ((const CallInst *)a)->e, *y = ((const CallInst *)b)->e;
    return x < y ? -1 : x > y;
}

static CallInst *call_inst(Expr *call) {
    CallInst key = {call, NULL, 0, NULL};
    return ncall_insts ? bsearch(&key, call_insts, (size_t)ncall_insts, sizeof key, call_inst_order) : NULL;
}

static SEnv *sym_typed(Expr *call, SCtx caller, SEnv *s) {
    return sym_open_gens && call && call_inst(call) ? senv_bind(&typed_mark, NULL, call, caller, s) : s;
}

/* t, generic, as the calls in s and their callers instantiate it. */
static Type *gen_type(Type *t, SEnv *s) {
    for (; s && ty_open(t); s = s->next) {
        if (s->def != &typed_mark) continue;
        CallInst *ci = call_inst(s->e);
        return gen_type(ty_zonk(ty_rename(t, ci->q, ci->to, ci->nq)), s->ctx.s);
    }
    return t;
}

static int sym_types(void) {
    Arena *saved = arena;
    tc_quiet = 1;
    int status = typecheck(root);
    tc_quiet = 0;
    Def *misvalued = status ? NULL : sym_misvalued();
    if (misvalued) {
        printf("Error: The configuration gives constant %s a value not of its type, %s.\n", S(misvalued->name), ty_text(tc_find(NULL, misvalued)->t));
        status = MANYAN_ERROR;
    }
    for (int i = 0; !status && i < root->nsyms; i++) {
        Def *d = root->syms[i].def, *bad = d->kind == D_OP ? let_clash(d->body) : NULL;
        if (!bad) continue;
        printf("Error: The specification is malformed: Found two different declarations with the same name [%s]: [%s %s] and [%s == ...].\n",
               S(bad->name), root_sym(bad->name)->def->kind == D_VAR ? "VARIABLE" : "CONSTANT", S(bad->name), S(bad->name));
        status = MANYAN_ERROR;
    }
    Expr *open = status ? NULL : sym_refused();
    if (open && mono_fcnsets) {
        printf("Error: %s: rewriter error: Trying to expand a set of functions. This will blow up the solver.\n", tc_where(open));
        status = MANYAN_ERROR;
    } else if (open && mono_repeat) {
        printf("Error: %s: Apalache!Repeat expects a constant positive integer as its second argument.\n", tc_where(open));
        status = MANYAN_ERROR;
    } else if (open) {
        TSeen key = {open, NULL, 0}, *x = bsearch(&key, tc_seen, (size_t)ntc_seen, sizeof *x, tc_seen_order);
        printf("Error: %s: Expected a non-polymorphic type, found: %s. You may need to annotate an empty collection.\n", tc_where(open), ty_text(ty_zonk(x->t)));
        status = MANYAN_ERROR;
    }
    for (int i = 0; i < ngen_types && !sym_open_gens; i++) sym_open_gens = ty_open(ty_zonk(gen_types[i].t));
    qsort(call_insts, (size_t)ncall_insts, sizeof *call_insts, call_inst_order);
    arena = saved;
    return status;
}

/* Counterexamples in the Informal Trace Format, as Apalache writes them
   (its ADR-015), laid out as its JSON library does: each value by its
   type, a sequence as a list, a tuple as #tup. A lasso's loop is the
   ADR's "loop", not Apalache's own variables. */

static void itf_item(Buf *b, int *count, int depth) {
    buf_printf(b, "%s\n%*s", (*count)++ ? "," : "", 2 * depth + 2, "");
}

static void itf_close(Buf *b, int count, int depth, char c) {
    if (count) buf_printf(b, "\n%*s", 2 * depth, "");
    buf_add(b, &c, 1);
}

static void itf_string(Buf *b, const char *s) {
    buf_puts(b, "\"");
    for (; *s; s++) {
        const char *esc = strchr("\b\t\n\f\r\"\\", *s);
        if (esc) buf_printf(b, "\\%c", "btnfr\"\\"[esc - "\b\t\n\f\r\"\\"]);
        else if ((unsigned char)*s < 0x20) buf_printf(b, "\\u%04x", (unsigned char)*s);
        else buf_add(b, s, 1);
    }
    buf_puts(b, "\"");
}

static void itf_key(Buf *b, int *count, int depth, const char *key) {
    itf_item(b, count, depth);
    itf_string(b, key);
    buf_puts(b, ": ");
}

static int itf_by_name(const void *a, const void *b) {
    return strcmp(S((*(Value *const *)a)->u.i), S((*(Value *const *)b)->u.i));
}

static void itf_value(Buf *b, Value *v, Type *t, int depth);

/* The elements of v, a set, a function or a tuple: {"tag": [...]}, or
   with no tag a list; a function's as [key, value] pairs. */
static void itf_elems(Buf *b, Value *v, const char *tag, Type *key, Type *val, int depth) {
    int count = 0, d = depth + !!tag;
    if (tag) { buf_puts(b, "{"); itf_key(b, &count, depth, tag); }
    buf_puts(b, "[");
    int n = 0;
    for (int i = 0; i < v->n; i++) {
        itf_item(b, &n, d);
        Value *k = v->kind == V_SET ? v->u.set.elems[i] : v->kind == V_TUPLE ? mk_int(i + 1) : v->u.fcn.keys[i];
        Value *x = v->kind == V_SET ? NULL : v->u.fcn.vals[i];
        if (!key) { itf_value(b, x ? x : k, val, d); continue; }
        int pair = 0;
        buf_puts(b, "[");
        itf_item(b, &pair, d + 1), itf_value(b, k, key, d + 2);
        itf_item(b, &pair, d + 1), itf_value(b, x, val, d + 2);
        itf_close(b, pair, d + 1, ']');
    }
    itf_close(b, n, d, ']');
    if (tag) itf_close(b, count, depth, '}');
}

static void itf_value(Buf *b, Value *v, Type *t, int depth) {
    v = realize(v);
    if (v->kind == V_INTERVAL) v = enumerate(v);
    int fcn = v->kind == V_FCN || v->kind == V_TUPLE, count = 0;
    switch (t ? (t = ty_zonk(t))->kind : -1) {
    case TY_INT:
        if (v->kind != V_INT) break;
        buf_puts(b, "{");
        itf_key(b, &count, depth, "#bigint");
        buf_printf(b, "\"%lld\"", (long long)v->u.i);
        itf_close(b, count, depth, '}');
        return;
    case TY_BOOL:
        if (v->kind != V_BOOL) break;
        buf_puts(b, v->u.i ? "true" : "false");
        return;
    case TY_STR: case TY_CONST:
        if (v->kind != V_STR && v->kind != V_MODEL) break;
        itf_string(b, S(v->u.i));
        return;
    case TY_SET:
        if (v->kind != V_SET) break;
        itf_elems(b, v, "#set", NULL, t->args[0], depth);
        return;
    case TY_SEQ: case TY_TUP:
        if (v->kind != V_TUPLE) break;
        if (t->kind == TY_SEQ) { itf_elems(b, v, NULL, NULL, t->args[0], depth); return; }
        buf_puts(b, "{");
        itf_key(b, &count, depth, "#tup");
        buf_puts(b, "[");
        int n = 0;
        for (int i = 0; i < v->n; i++) itf_item(b, &n, depth + 1), itf_value(b, v->u.fcn.vals[i], i < t->n ? t->args[i] : NULL, depth + 2);
        itf_close(b, n, depth + 1, ']');
        itf_close(b, count, depth, '}');
        return;
    case TY_FUN:
        if (!fcn) break;
        itf_elems(b, v, "#map", t->args[0], t->args[1], depth);
        return;
    case TY_REC: case TY_OLDREC: case TY_VARIANT: {
        Type *row = t->kind == TY_OLDREC ? t : t->args[0];
        if (!fcn_is_record(v) || (t->kind == TY_VARIANT && v->n != 1)) break;
        Value **keys = NEWN(Value *, v->n);
        memcpy(keys, v->u.fcn.keys, sizeof *keys * (size_t)v->n);
        qsort(keys, (size_t)v->n, sizeof *keys, itf_by_name);
        buf_puts(b, "{");
        for (int i = 0; i < v->n; i++) {
            Type *f = NULL;
            for (int k = 0; k < row->n; k++) if (row->keys[k] == keys[i]->u.i) f = row->args[k];
            Value *x = v->u.fcn.vals[0];
            for (int k = 0; k < v->n; k++) if (v->u.fcn.keys[k] == keys[i]) x = v->u.fcn.vals[k];
            if (t->kind == TY_VARIANT) {
                itf_key(b, &count, depth, "tag");
                itf_string(b, S(keys[i]->u.i));
                itf_key(b, &count, depth, "value");
            } else itf_key(b, &count, depth, S(keys[i]->u.i));
            itf_value(b, x, f, depth + 1);
        }
        itf_close(b, count, depth, '}');
        return;
    }
    default: break;
    }
    buf_puts(b, "{");
    itf_key(b, &count, depth, "#unserializable");
    itf_string(b, pretty(v));
    itf_close(b, count, depth, '}');
}

/* Writes the behavior of the n states s, a lasso back to state loop if
   loop >= 0, as violation<index>.itf.json and violation.itf.json of the
   run directory, as Apalache does. */
static void itf_write(Value ***s, int n, int loop, int index) {
    if (!sym_run_dir) return;
    Buf b = {0};
    int top = 0, meta = 0, types = 0;
    buf_puts(&b, "{");
    itf_key(&b, &top, 0, "#meta");
    buf_puts(&b, "{");
    itf_key(&b, &meta, 1, "format"), itf_string(&b, "ITF");
    itf_key(&b, &meta, 1, "format-description"), itf_string(&b, "https://apalache-mc.org/docs/adr/015adr-trace.html");
    itf_key(&b, &meta, 1, "description"), itf_string(&b, "Created by Manyan");
    itf_key(&b, &meta, 1, "varTypes");
    buf_puts(&b, "{");
    for (int v = 0; v < nvars; v++) {
        TEntry *t = tc_find(NULL, vars[v]);
        itf_key(&b, &types, 2, S(vars[v]->name));
        itf_string(&b, t ? ty_text(t->t) : "");
    }
    itf_close(&b, types, 2, '}');
    itf_close(&b, meta, 1, '}');
    Def **names = NEWN(Def *, root->ndecls + nvars);   /* the constants with values, then the variables */
    int nconsts = 0, nnames, count = 0;
    for (int i = 0; i < root->ndecls; i++) {
        Def *d = root->decls[i];
        if (d->kind == D_CONST && !d->arity && d->value) names[nconsts++] = d;
    }
    for (int i = 0; i < 2; i++) {
        int from = i ? nconsts : 0, to = i ? nconsts + nvars : nconsts;
        if (i) memcpy(names + nconsts, vars, sizeof *vars * (size_t)nvars);
        if (from == to) continue;
        itf_key(&b, &top, 0, i ? "vars" : "params");
        buf_puts(&b, "[");
        count = 0;
        for (int k = from; k < to; k++) itf_item(&b, &count, 1), itf_string(&b, S(names[k]->name));
        itf_close(&b, count, 1, ']');
    }
    nnames = nconsts + nvars;
    for (int i = 1; i < nnames; i++)   /* a state's fields, by name */
        for (int j = i; j > 0 && strcmp(S(names[j - 1]->name), S(names[j]->name)) > 0; j--) { Def *t = names[j]; names[j] = names[j - 1]; names[j - 1] = t; }
    itf_key(&b, &top, 0, "states");
    buf_puts(&b, "[");
    count = 0;
    for (int i = 0; i < n; i++) {
        int fields = 0, index_meta = 0;
        itf_item(&b, &count, 1);
        buf_puts(&b, "{");
        itf_key(&b, &fields, 2, "#meta");
        buf_puts(&b, "{");
        itf_key(&b, &index_meta, 3, "index");
        buf_printf(&b, "%d", i);
        itf_close(&b, index_meta, 3, '}');
        for (int k = 0; k < nnames; k++) {
            Def *d = names[k];
            int v = d->kind == D_CONST ? -1 : 0;
            while (v >= 0 && vars[v] != d) v++;
            TEntry *t = tc_find(NULL, d);
            itf_key(&b, &fields, 2, S(d->name));
            itf_value(&b, v < 0 ? d->value : s[i][v], t ? t->t : NULL, 3);
        }
        itf_close(&b, fields, 2, '}');
    }
    itf_close(&b, count, 1, ']');
    if (loop >= 0) itf_key(&b, &top, 0, "loop"), buf_printf(&b, "%d", loop);
    itf_close(&b, top, 0, '}');
    mkdir(sym_run_dir, 0777);
    for (int i = 0; i < 2; i++) {
        char *path = xmalloc(strlen(sym_run_dir) + 64);
        if (i) sprintf(path, "%s/violation.itf.json", sym_run_dir);
        else sprintf(path, "%s/violation%d.itf.json", sym_run_dir, index);
        FILE *f = fopen(path, "w");
        if (!f) fail("Cannot write the counterexample to %s: %s.", path, strerror(errno));
        fwrite(b.s, 1, b.n, f);
        fclose(f);
        free(path);
    }
    free(b.s);
}

static SVal *sym_gen(Expr *e, SCtx sc) {
    SVal *size = e->n == 1 ? sym(e->args[0], sc, P_BOTH) : NULL;
    if (!size || size->kind != SV_CONST || size->value->kind != V_INT || size->value->u.i < 0 || size->value->u.i > 64)
        fail_at(e, "Symbolic checking needs Gen's size as a constant from 0 to 64.");
    Type *t = NULL;
    for (int i = 0; i < ngen_types && !t; i++) if (gen_types[i].e == e) t = gen_types[i].t;
    if (!t) fail_at(e, "Symbolic checking cannot tell the type of this Gen.");
    t = gen_type(ty_zonk(t), sc.s);
    SVal *v = gen_of(t, (int)size->value->u.i, e);
    sym_gens = xrealloc(sym_gens, sizeof *sym_gens * (size_t)(nsym_gens + 1));
    sym_gens[nsym_gens].e = e, sym_gens[nsym_gens].step = sym_gen_step, sym_gens[nsym_gens++].v = v;
    return v;
}

/* The invariant -inv expr names, as TLC's: an operator of the root, or
   expr defined as __DebuggerExpr__N in a module __DebuggerModule__N that
   extends the root, N the time in milliseconds. */
static int inv_name(const char *expr) {
    Sym *s = root_sym(intern(expr));
    if (s && s->def->kind == D_OP) return s->name;
    struct timespec now;
    clock_gettime(CLOCK_REALTIME, &now);
    long long n = (long long)now.tv_sec * 1000 + now.tv_nsec / 1000000;
    char name[64];
    do sprintf(name, "__DebuggerModule__%lld", n++); while (find_module(intern(name)));
    char *text = xmalloc(strlen(expr) + strlen(S(root->name)) + 128);
    sprintf(text, "---- MODULE %s ----\nEXTENDS %s\n\n__DebuggerExpr__%lld == %s\n====\n", name, S(root->name), n - 1, expr);
    breakpoint = expr;
    Module *m = parse_text(text, strdup(name));
    modules = xrealloc(modules, sizeof(Module *) * (size_t)(nmodules + 1));
    modules[nmodules++] = m;
    load_references(m);
    finish_module(m);
    resolve_module(m);
    s = &m->syms[m->nsyms - 1];
    if (expr_level(s->def->body) > 2) breakpoint_error(0, "Debug expressions must be action-level or below; actual level: 3 (Temporal)");
    breakpoint = NULL;
    add_sym(root, s->name, s->def, NULL, 0, 0, NULL);
    return s->name;
}

int manyan_check(const ManyanOptions *o) {
    printf("manyan version %s\n", MANYAN_VERSION);
    stack_limit = o->stack > 0 ? o->stack : 0;
    symbolic_mode = o->symbolic;
    sym_cinit_name = o->symbolic ? o->cinit : NULL;
    size_t len = strlen(o->spec);
    char *path = xmalloc(len + 5);
    strcpy(path, o->spec);
    if (len < 4 || strcmp(path + len - 4, ".tla") != 0) strcat(path, ".tla");
    char *slash = strrchr(path, '/');
    spec_dir = xmalloc(strlen(path) + 1);
    if (slash) { memcpy(spec_dir, path, (size_t)(slash - path + 1)); spec_dir[slash - path + 1] = 0; }
    else spec_dir[0] = 0;
    char *config_path;
    if (o->config) {
        config_path = (char *)o->config;
    } else {
        config_path = xmalloc(strlen(path) + 1);
        strcpy(config_path, path);
        strcpy(config_path + strlen(config_path) - 4, ".cfg");
    }
    config_text = o->typecheck ? strdup("") : read_file(config_path);
    if (!config_text) config_error("Cannot open the configuration file %s.", config_path);
    read_config(config_text, 1);
    char *text = read_file(path);
    if (!text) {
        printf("Error: Cannot find source file %s.\n", path);
        printf("Error: Parsing or semantic analysis failed.\n");
        return MANYAN_ERROR_PARSE;
    }

    for (int i = 0; builtin_names[i]; i++) intern(builtin_names[i]);
    for (int i = -1; i < 1023; i++) {
        Value *v = NEW(Value);
        v->kind = V_INT;
        v->u.i = i;
        small_ints[i + 1] = v;
    }
    for (int i = 0; i < 64; i++) index_hash[i] = fmix(atom_word(V_INT, i + 1));
    boolean_set = mk_set(2);
    boolean_set->u.set.elems[0] = FALSEV;
    boolean_set->u.set.elems[1] = TRUEV;
    check_deadlock = o->check_deadlock;
    nowarning = o->nowarning;
    diff_trace = o->difftrace;
    view_trace = o->view;
    keep_going = o->keep_going;
    te_spec = !o->keep_going && !o->no_te_spec;
    for (const char *const *p = o->properties; p && *p; p++) {
        int n = (int)(strchr(*p, '=') - *p);
        char *key = xmalloc((size_t)n + 3);
        sprintf(key, "-D%.*s", n, *p);
        *prop(key) = intern(*p + n + 1);
        free(key);
    }
    if (user_file) fclose(user_file);   /* each write is flushed: a run may end anywhere */
    user_file = NULL;
    if (o->user_file && !(user_file = fopen(o->user_file, "w"))) {
        fprintf(stderr, "manyan: cannot write %s\n", o->user_file);
        return MANYAN_ERROR;
    }

    root_text = text;
    root = parse_text(text, path);
    char *base = strndup(path + strlen(spec_dir), strlen(path) - strlen(spec_dir) - 4);
    check_file_name(root, base);
    free(base);
    modules = xrealloc(modules, sizeof(Module *) * (size_t)(nmodules + 1));
    modules[nmodules++] = root;
    /* TLC extends the root with the module of each -postCondition, and -dumpTrace json's */
    int extra = (o->dump_trace != NULL);
    for (const char *const *p = o->postconditions; p && *p; p++) extra++;
    int *extends = NEWN(int, root->nextends + extra + 1);
    if (root->nextends) memcpy(extends, root->extends, sizeof(int) * (size_t)root->nextends);
    root->extends = extends;
    for (const char *const *p = o->postconditions; p && *p; p++) root->extends[root->nextends++] = intern_n(*p, (int)(strchr(*p, '!') - *p));
    if (o->dump_trace) {
        intern("action");   /* before _JsonTrace's "state", as TLC */
        root->extends[root->nextends++] = intern("_JsonTrace");
    }
    load_references(root);
    finish_module(root);
    resolve_module(root);
    if (lint.n) printf("%s", lint.s);
    if (o->typecheck) return typecheck(root);
    int ninvs = 0, *invs = NULL;
    for (const char *const *p = o->invariants; p && *p; p++) {
        invs = xrealloc(invs, sizeof(int) * (size_t)(ninvs + 1));
        invs[ninvs++] = inv_name(*p);
    }
    for (int i = 0; i < nfinished; i++) {
        Expr *e = finished[i]->outer ? NULL : odd_literal(finished[i]);
        if (e && e->num < 0) config_error("TLC can't handle real numbers.\n%s", S(e->op));
        if (e) {
            printf("Error: TLC can't handle a number this big.\n%s\n", S(e->op));
            return MANYAN_ERROR;
        }
    }
    bind_natives();
    /* TLC's simulation: random without -seed */
    draw_seed = o->simulate && !o->seed_given ? (int64_t)time(NULL) * 1000003 ^ getpid() : o->seed;
    jr_seed(&draw_model, draw_seed);
    jr_seed(&draw_behaviors, draw_seed);
    starting = 1;
    read_config(config_text, 0);
    for (int i = 0; i < ninvs; i++) cfg_add("INVARIANT", invs[i], 0, NULL, 0, 0, NULL);
    for (const char *const *p = o->postconditions; p && *p; p++)
        cfg_add("POSTCONDITION", intern(strchr(*p, '!') + 1), 0, NULL, 0, intern_n(*p, (int)(strchr(*p, '!') - *p)), NULL);
    if (o->dump_trace) {
        cfg_add("CONSTANT", intern("_JsonTraceFile"), '=', mk_str(intern(o->dump_trace)), 0, 0, NULL);
        cfg_add("POSTCONDITION", intern("_JsonTrace"), 0, NULL, 0, intern("_JsonTrace"), NULL);
    }
    setup_model();

    for (int i = 0; i < nfinished; i++) evaluate_constants(finished[i]);
    starting = 0;
    started = time(NULL);
    simulating = o->simulate;   /* the assumptions see a simulation's TLCGet */
    generating = o->generate;
    if (o->simulate) {
        sim_traces_max = o->traces ? o->traces : -1;
        sim_depth = o->depth ? o->depth : 100;
    }
    if (!o->simulate && !nowarning && ntemporal_props) {   /* as TLC's checker starts, before the assumptions */
        if (nsymmetry)
            warning("Declaring symmetry during liveness checking is dangerous. It might cause TLC to miss "
                    "violations of the stated liveness properties. Please check liveness without symmetry defined.");
    }
    int status = symbolic_mode ? 0 : check_temporal_forms(o->simulate);   /* TLC's tableau, built as its checker starts */
    for (int i = 0; i < nmodules && !status; i++) {
        Module *m = modules[i];
        int used = m == root;
        for (int k = 0; k < root->nextends && !used; k++) used = load_module(root->extends[k], root) == m;
        if (used && m != root) check_assumptions(m, &status);
    }
    if (!status) check_assumptions(root, &status);
    if (status) return status;
    if (!init_expr) {
        if (nvars || ninvariants || nimplied_inits || naction_props || ntemporal_props)
            config_error("The configuration file did not specify the initial state predicate.");
        if (o->simulate) {   /* TLC's simulator wants an initial state */
            printf("Computed 0 initial states...\n");
            printf("Error: There is no state satisfying the initial state predicate.\n");
            return MANYAN_ERROR;
        }
        printf("Finished computing initial states: 0 distinct states generated.\n");
        printf("Model checking completed. No error has been found.\n");
        print_counts(0);
        return MANYAN_OK;
    }
    /* With nothing to check on steps, TLC computes the initial states first. */
    if (!next_expr && (ninvariants || naction_props || ntemporal_props))
        config_error("The configuration file did not specify the next state predicate.");
    arena = &perm_arena;
    sigjmp_buf here;
    handler = &here;
    if (sigsetjmp(here, 0)) {   /* TLC splits the actions as it starts */
        handler = NULL;
        print_exception("java.lang.RuntimeException", ": ");
        print_error_text();
        return MANYAN_ERROR;
    }
    if (next_expr) {
        int named = (next_expr->kind == K_CALL || next_expr->kind == K_INSTCALL) && !next_expr->def->part;
        split_action(next_expr, root_ctx, named ? next_expr->def->name : intern("Action"), NULL);
    }
    handler = NULL;
    if (o->dump && !o->simulate) {
        if (!(dump_file = fopen(o->dump, "w"))) { fprintf(stderr, "manyan: cannot write %s\n", o->dump); return MANYAN_ERROR; }
        fputs("strict digraph DiskGraph {\nnode [shape=box,style=rounded]\nnodesep=0.35;\nsubgraph cluster_graph {\ncolor=\"white\";\n", dump_file);
        dump_actions = o->dump_actions;
    }
    /* A simulation is TLC's with one worker; -continue reports in the search's order. */
    nworkers = o->workers > 1 && !o->simulate && !o->keep_going ? o->workers : 1;
    sym_length = o->length ? o->length : 10;
    sym_max_error = o->max_error > 0 ? o->max_error : 1;
    sym_run_dir = o->symbolic ? o->run_dir : NULL;
    status = o->symbolic ? symbolic() : o->simulate ? simulate(o) : search();
    handler = NULL;
    if (dump_file) dump_close();
    stop_workers();
    return status;
}

#ifndef MANYAN_NO_MAIN
#include "manyan-std.h"
#ifdef MANYAN_LEAK_CHECK
#include <sanitizer/lsan_interface.h>
#endif

int main(int argc, char **argv) {
    if (manyan_std_init()) { fprintf(stderr, "manyan: out of memory\n"); return MANYAN_ERROR; }
    ManyanOptions o = {0};
    o.check_deadlock = 1;
    const char **properties = xcalloc((size_t)argc, sizeof(char *));
    const char **invariants = xcalloc((size_t)argc, sizeof(char *));
    const char **postconditions = xcalloc((size_t)argc, sizeof(char *));
    int nproperties = 0, ninvariants = 0, npostconditions = 0;
    o.properties = properties;
    o.invariants = invariants;
    o.postconditions = postconditions;
    const char *usage = "usage: manyan [-config FILE] [-deadlock] [-workers N|auto] [-dump dot FILE] SPEC\n";
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-config") == 0 && i + 1 < argc) o.config = argv[++i];
        else if (strcmp(argv[i], "-deadlock") == 0) o.check_deadlock = 0;
        else if (strcmp(argv[i], "-simulate") == 0 || strcmp(argv[i], "-generate") == 0) {
            o.simulate = 1;
            o.generate = argv[i][1] == 'g';
            if (i + 1 < argc && (strstr(argv[i + 1], "num=") || strstr(argv[i + 1], "file="))) {
                for (char *arg = strtok(argv[++i], ","); arg; arg = strtok(NULL, ","))
                    if (strncmp(arg, "num=", 4) == 0) o.traces = atol(arg + 4);
                    else if (strncmp(arg, "file=", 5) == 0) o.trace_file = arg + 5;
                    else { fprintf(stderr, "manyan: %s %s is not supported\n", o.generate ? "-generate" : "-simulate", arg); return MANYAN_ERROR; }
            }
        }
        else if (strcmp(argv[i], "-depth") == 0 && i + 1 < argc) o.depth = atol(argv[++i]);
        else if (strcmp(argv[i], "-symbolic") == 0) o.symbolic = 1;
        else if (strcmp(argv[i], "-typecheck") == 0) o.typecheck = 1;
        else if (strcmp(argv[i], "-length") == 0 && i + 1 < argc) o.length = atol(argv[++i]);
        else if (strcmp(argv[i], "-cinit") == 0 && i + 1 < argc) o.cinit = argv[++i];
        else if (strcmp(argv[i], "-max-error") == 0 && i + 1 < argc) o.max_error = atol(argv[++i]);
        else if (strcmp(argv[i], "-run-dir") == 0 && i + 1 < argc) o.run_dir = argv[++i];
        else if (strcmp(argv[i], "-seed") == 0 && i + 1 < argc) { o.seed = atoll(argv[++i]); o.seed_given = 1; }
        else if (strcmp(argv[i], "-stack") == 0 && i + 1 < argc) o.stack = atoi(argv[++i]);
        else if (strcmp(argv[i], "-aril") == 0 && i + 1 < argc) o.aril = atoll(argv[++i]);
        else if (strcmp(argv[i], "-workers") == 0 && i + 1 < argc) {
            i++;
            o.workers = strcmp(argv[i], "auto") == 0 ? (int)sysconf(_SC_NPROCESSORS_ONLN) : atoi(argv[i]);
        }
        else if (strcmp(argv[i], "-dump") == 0 && i + 2 < argc) {
            /* -dump dot[,actionlabels,...] FILE writes FILE.dot, as TLC. */
            const char *format = argv[++i], *file = argv[++i];
            if (strncmp(format, "dot", 3) != 0 || (format[3] && format[3] != ',')) {
                fprintf(stderr, "manyan: -dump writes only dot: -dump dot FILE\n");
                return MANYAN_ERROR;
            }
            o.dump_actions = strstr(format, "actionlabels") != NULL;
            size_t n = strlen(file);
            char *path = xmalloc(n + 5);
            sprintf(path, "%s%s", file, n >= 4 && strcmp(file + n - 4, ".dot") == 0 ? "" : ".dot");
            o.dump = path;
        } else if (strcmp(argv[i], "-version") == 0) { printf("manyan version %s\n", MANYAN_VERSION); return 0; }
        else if (strcmp(argv[i], "-nowarning") == 0) o.nowarning = 1;
        else if (strcmp(argv[i], "-difftrace") == 0) o.difftrace = 1;
        else if (strcmp(argv[i], "-continue") == 0) o.keep_going = 1;
        else if (strcmp(argv[i], "-view") == 0) o.view = 1;
        else if (strcmp(argv[i], "-userFile") == 0 && i + 1 < argc) o.user_file = argv[++i];
        else if (!strncmp(argv[i], "-D", 2) && strchr(argv[i], '=')) properties[nproperties++] = argv[i] + 2;
        else if (strcmp(argv[i], "-inv") == 0 && i + 1 < argc) invariants[ninvariants++] = argv[++i];
        else if (strcmp(argv[i], "-invlevel") == 0 && i + 1 < argc) {
            /* as TLC: the invariant that the level is below N */
            char *end, *n = argv[++i];
            strtol(n, &end, 10);
            if (!*n || *end) { fprintf(stderr, "manyan: -invlevel takes an integer, not %s\n", n); return MANYAN_ERROR; }
            char *e = xmalloc(strlen(n) + 80);
            sprintf(e, "LET _T == INSTANCE TLC _N == INSTANCE Naturals IN _N!<(_T!TLCGet(\"level\"), %s)", n);
            invariants[ninvariants++] = e;
        }
        else if (strcmp(argv[i], "-postCondition") == 0 && i + 1 < argc) {
            const char *pc = argv[++i], *bang = strchr(pc, '!');
            if (!bang || bang == pc || !bang[1] || strchr(bang + 1, '!') || strchr(pc, '.')) {
                fprintf(stderr, "manyan: -postCondition takes Module!Operator, not %s\n", pc);
                return MANYAN_ERROR;
            }
            postconditions[npostconditions++] = pc;
        }
        else if (strcmp(argv[i], "-dumpTrace") == 0 && i + 2 < argc) {
            if (strcmp(argv[++i], "json")) { fprintf(stderr, "manyan: -dumpTrace writes only json: -dumpTrace json FILE\n"); return MANYAN_ERROR; }
            o.dump_trace = argv[++i];
        }
        else if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "-help") == 0) { printf("%s", usage); return 0; }
        /* TLC's, for its own files, fingerprints and when it checks liveness: manyan has no files, its own
           fingerprints, and checks liveness once the states are found */
        else if ((!strcmp(argv[i], "-metadir") || !strcmp(argv[i], "-fp") || !strcmp(argv[i], "-fpmem") || !strcmp(argv[i], "-fpbits") ||
                  !strcmp(argv[i], "-teSpecOutDir") || !strcmp(argv[i], "-lncheck")) && i + 1 < argc) i++;
        else if (strcmp(argv[i], "-noGenerateSpecTE") == 0) o.no_te_spec = 1;
        else if (!strcmp(argv[i], "-gzip") || !strcmp(argv[i], "-cleanup")) {}
        else if (argv[i][0] == '-') { fprintf(stderr, "manyan: unknown option %s\n", argv[i]); return MANYAN_ERROR; }
        else o.spec = argv[i];
    }
    if (!o.spec) {
        fprintf(stderr, "%s", usage);
        return MANYAN_ERROR;
    }
    int status = manyan_check(&o);
#ifdef MANYAN_LEAK_CHECK
    __lsan_do_leak_check();   /* what manyan_check made and returned without is lost */
#endif
    return status;
}
#endif
