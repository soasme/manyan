/* manyan-std: the operators TLC computes in Java for its modules and for
   CommunityModules', written on manyan.h's native operators. Each is TLC's
   Java, error messages included (docs/std.md). */
#define _DEFAULT_SOURCE
#define _DARWIN_C_SOURCE
#include "manyan-std.h"

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <math.h>
#include <poll.h>
#include <regex.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <unistd.h>

#define J_V "tlc2.value.impl.Value"
#define J_S "tlc2.value.impl.StringValue"
#define J_I "tlc2.value.impl.IntValue"
#define J_OP "tlc2.value.impl.OpValue"
#define J_EVAL "tlc2.tool.impl.Tool,tla2sany.semantic.ExprOrOpArgNode[],tlc2.util.Context," \
               "tlc2.tool.TLCState,tlc2.tool.TLCState,int,tlc2.tool.coverage.CostModel"

static ManyanValue *str(const char *s) { return manyan_string(s, strlen(s)); }

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

/* A function whose keys are strings, as <<>> is: a record. */
static int is_record(ManyanValue *v) {
    if (manyan_kind(v) != MANYAN_FUNCTION && manyan_kind(v) != MANYAN_TUPLE) return 0;
    for (size_t i = 0; i < manyan_size(v); i++) if (manyan_kind(manyan_key(v, i)) != MANYAN_STRING) return 0;
    return 1;
}

/* A function on 1..n as the tuple it is, as TLC's toTuple; NULL for another value. */
static ManyanValue *to_tuple(ManyanValue *v) {
    if (manyan_kind(v) == MANYAN_TUPLE) return v;
    if (manyan_kind(v) != MANYAN_FUNCTION) return NULL;
    size_t n = manyan_size(v);
    for (size_t i = 0; i < n; i++)
        if (manyan_kind(manyan_key(v, i)) != MANYAN_INT || manyan_int_value(manyan_key(v, i)) != (int64_t)i + 1) return NULL;
    ManyanValue **elems = xcalloc(n + 1, sizeof *elems);
    for (size_t i = 0; i < n; i++) elems[i] = manyan_value(v, i);
    ManyanValue *t = manyan_tuple(n, elems);
    free(elems);
    return t;
}

/* A growing array of values. */
typedef struct { ManyanValue **v; size_t n, cap; } Values;

static void add(Values *l, ManyanValue *v) {
    if (l->n == l->cap) {
        l->cap = l->cap ? 2 * l->cap : 8;
        l->v = xrealloc(l->v, sizeof(ManyanValue *) * l->cap);
    }
    l->v[l->n++] = v;
}

/* ---------------------------------------------------------------- IOUtils */

extern char **environ;

static ManyanValue *io_env(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    (void)call, (void)a;
    Values names = {0}, values = {0};
    for (char **e = environ; *e; e++) {
        const char *eq = strchr(*e, '=');
        if (!eq) continue;
        add(&names, manyan_string(*e, (size_t)(eq - *e)));
        add(&values, str(eq + 1));
    }
    ManyanValue *r = manyan_record(names.n, names.v, values.v);
    free(names.v), free(values.v);
    return r;
}

static ManyanValue *atoi_(ManyanCall *call, ManyanValue **a) {
    if (manyan_kind(a[0]) == MANYAN_STRING) {   /* Java's Integer.parseInt */
        const char *t = manyan_string_value(a[0], NULL), *d = t + (*t == '-' || *t == '+');
        char *end;
        errno = 0;
        long long i = *d >= '0' && *d <= '9' ? strtoll(t, &end, 10) : 0;
        if (*d >= '0' && *d <= '9' && !*end && !errno && i >= INT32_MIN && i <= INT32_MAX) return manyan_int(i);
    }
    manyan_fail(call, "The argument of atoi should be a string, but instead it is:\n%s", manyan_print(a[0]));
}

/* The command's words, each a string, as IOExec takes them. */
static char **command_words(ManyanCall *call, ManyanValue *v, const char *op) {
    if (manyan_kind(v) != MANYAN_TUPLE) manyan_fail(call, "The argument of %s should be a sequence, but instead it is:\n%s", op, manyan_print(v));
    for (size_t i = 0; i < manyan_size(v); i++)
        if (manyan_kind(manyan_value(v, i)) != MANYAN_STRING)
            manyan_fail(call, "The argument of IOExec should be a sequence, but instead it is:\n%s", manyan_print(manyan_value(v, i)));
    char **argv = xcalloc(manyan_size(v) + 1, sizeof(char *));
    for (size_t i = 0; i < manyan_size(v); i++) argv[i] = (char *)manyan_string_value(manyan_value(v, i), NULL);
    return argv;
}

/* What IOExec and Serialize give: [exitValue, stdout, stderr]. */
static ManyanValue *exec_record(int64_t code, const char *out, size_t nout, const char *err) {
    ManyanValue *keys[] = {str("exitValue"), str("stdout"), str("stderr")};
    ManyanValue *vals[] = {manyan_int(code), manyan_string(out, nout), str(err)};
    return manyan_record(3, keys, vals);
}

/* Runs argv with env's variables added, its standard input empty. */
static ManyanValue *run_process(ManyanCall *call, char **argv, ManyanValue *env) {
    manyan_effect(call);
    int out[2], err[2];
    fflush(stdout);
    if (pipe(out) || pipe(err)) manyan_fail(call, "Cannot run program \"%s\": %s", argv[0], strerror(errno));
    pid_t pid = fork();
    if (pid == 0) {
        int in = open("/dev/null", O_RDONLY);
        dup2(in, 0), dup2(out[1], 1), dup2(err[1], 2);
        close(out[0]), close(err[0]);
        for (size_t i = 0; env && i < manyan_size(env); i++) {
            ManyanValue *v = manyan_value(env, i);
            setenv(manyan_string_value(manyan_key(env, i), NULL), manyan_kind(v) == MANYAN_STRING ? manyan_string_value(v, NULL) : manyan_print(v), 1);
        }
        execvp(argv[0], argv);
        _exit(127);
    }
    free(argv);
    close(out[1]), close(err[1]);
    char *text[2] = {NULL, NULL};
    size_t len[2] = {0, 0};
    struct pollfd fds[2] = {{out[0], POLLIN, 0}, {err[0], POLLIN, 0}};
    for (int open = 2; open;) {
        poll(fds, 2, -1);
        for (int i = 0; i < 2; i++) {
            if (fds[i].fd < 0 || !fds[i].revents) continue;
            char chunk[4096];
            ssize_t n = read(fds[i].fd, chunk, sizeof chunk);
            if (n <= 0) { close(fds[i].fd), fds[i].fd = -1, open--; continue; }
            text[i] = xrealloc(text[i], len[i] + (size_t)n + 1);
            memcpy(text[i] + len[i], chunk, (size_t)n);
            text[i][len[i] += (size_t)n] = 0;
        }
    }
    int status = 0;
    waitpid(pid, &status, 0);
    ManyanValue *r = exec_record(WIFEXITED(status) ? WEXITSTATUS(status) : 128 + WTERMSIG(status),
                              text[0] ? text[0] : "", len[0], text[1] ? text[1] : "");
    free(text[0]), free(text[1]);
    return r;
}

static ManyanValue *io_exec(ManyanCall *call, ManyanValue **a) { return run_process(call, command_words(call, a[0], "IOExec"), NULL); }

static ManyanValue *io_env_exec(ManyanCall *call, ManyanValue **a) {
    if (!is_record(a[0])) manyan_fail(call, "The argument of IOEnvExec should be a record, but instead it is:\n%s", manyan_print(a[0]));
    return run_process(call, command_words(call, a[1], "IOEnvExec"), a[0]);
}

/* Serialize(payload, file, [format |-> "TXT", charset |-> ..., openOptions |-> ...])
   writes the string payload to file, with Java's StandardOpenOptions; TLC
   leaves another format to the definition. */
static ManyanValue *serialize(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    (void)a;
    ManyanValue *opts = manyan_arg(call, 2), *format = manyan_field(opts, "format");
    if (!format || manyan_kind(format) != MANYAN_STRING || strcmp(manyan_string_value(format, NULL), "TXT")) return NULL;
    ManyanValue *payload = manyan_arg(call, 0), *file = manyan_arg(call, 1);
    ManyanValue *options = manyan_field(opts, "openOptions"), *charset = manyan_field(opts, "charset");
    int ok = manyan_kind(payload) == MANYAN_STRING && manyan_kind(file) == MANYAN_STRING && options && manyan_kind(options) == MANYAN_TUPLE
          && charset && manyan_kind(charset) == MANYAN_STRING;
    int flags = ok && manyan_size(options) ? 0 : O_WRONLY | O_CREAT | O_TRUNC;
    static const struct { const char *name; int flags; } open_options[] = {
        {"READ", 0}, {"WRITE", O_WRONLY}, {"APPEND", O_WRONLY | O_APPEND}, {"TRUNCATE_EXISTING", O_TRUNC},
        {"CREATE", O_CREAT}, {"CREATE_NEW", O_CREAT | O_EXCL}, {"DSYNC", O_DSYNC}, {"SYNC", O_SYNC}, {NULL, 0}};
    for (size_t i = 0; ok && i < manyan_size(options); i++) {
        ManyanValue *o = manyan_value(options, i);
        int k = 0;
        while (open_options[k].name && (manyan_kind(o) != MANYAN_STRING || strcmp(open_options[k].name, manyan_string_value(o, NULL)))) k++;
        ok = open_options[k].name != NULL;
        flags |= ok ? open_options[k].flags : 0;
    }
    if (!ok) return exec_record(1, "", 0, "Serialize error invalid parameters");
    size_t n;
    const char *text = manyan_string_value(payload, &n), *path = manyan_string_value(file, NULL);
    int fd = open(path, flags, 0644);
    int written = fd >= 0 && write(fd, text, n) == (ssize_t)n, err = errno;
    if (fd >= 0) close(fd);
    if (written) return exec_record(0, "Finish writing to the file with success!", 40, "");
    char message[4096];
    snprintf(message, sizeof message, "Serialize error writing to the file: %s: %s", path, strerror(err));
    return exec_record(1, "", 0, message);
}

/* ---------------------------------------------------------------- SequencesExt */

/* A finite set's elements in order. */
static ManyanValue *set_to_seq(ManyanCall *call, ManyanValue **a) {
    ManyanValue *s = manyan_elements(a[0]);
    if (!s) manyan_fail(call, "Attempted to enumerate a set that is not enumerable:\n%s", manyan_print(a[0]));
    Values l = {0};
    for (size_t i = 0; i < manyan_size(s); i++) add(&l, manyan_element(s, i));
    ManyanValue *t = manyan_tuple(l.n, l.v);
    free(l.v);
    return t;
}

/* A function's fold, as Functions' FoldFunction: op(f[k], acc) for each k
   of its domain in TLC's order, from base. */
static ManyanValue *fold_function(ManyanCall *call, ManyanValue **a) {
    ManyanKind k = manyan_kind(a[2]);
    if (k != MANYAN_TUPLE && k != MANYAN_FUNCTION)
        manyan_fail(call, "The third argument of FoldFunction should be a function, but instead it is:\n%s", manyan_print(a[2]));
    ManyanValue *acc = a[1];
    for (size_t i = 0; i < manyan_size(a[2]); i++) {
        ManyanValue *args[2] = {manyan_value(a[2], i), acc};
        acc = manyan_apply(call, a[0], 2, args);
    }
    return acc;
}

/* f[x], or TLC's error applying f outside its domain. */
static ManyanValue *apply_at(ManyanCall *call, ManyanValue *f, ManyanValue *x) {
    size_t lo = 0, hi = manyan_size(f);   /* its keys in TLC's order: sorted */
    while (lo < hi) {
        size_t mid = (lo + hi) / 2;
        ManyanValue *key = manyan_key(f, mid);
        int c = manyan_kind(key) == manyan_kind(x) ? manyan_compare(key, x) : (int)manyan_kind(key) - (int)manyan_kind(x);
        if (!c) return manyan_value(f, mid);
        if (c < 0) lo = mid + 1;
        else hi = mid;
    }
    manyan_fail(call, "Attempted to apply function:\n%s\nto argument %s, which is not in the domain of the function.",
                manyan_print(f), manyan_print(x));
}

/* FoldFunctionOnSet(op, base, f, S): FoldFunction's on the keys in S. */
static ManyanValue *fold_function_on_set(ManyanCall *call, ManyanValue **a) {
    ManyanKind k = manyan_kind(a[2]);
    if (k != MANYAN_TUPLE && k != MANYAN_FUNCTION)
        manyan_fail(call, "The third argument of FoldFunctionOnSet should be a function, but instead it is:\n%s", manyan_print(a[2]));
    ManyanValue *keys = manyan_elements(a[3]), *acc = a[1];
    if (!keys) manyan_fail(call, "The fourth argument of FoldFunctionOnSet should be a set, but instead it is:\n%s", manyan_print(a[3]));
    for (size_t i = 0; i < manyan_size(keys); i++) {
        ManyanValue *args[2] = {apply_at(call, a[2], manyan_element(keys, i)), acc};
        acc = manyan_apply(call, a[0], 2, args);
    }
    return acc;
}

/* SelectInSeq(s, Test), SelectInSubSeq(s, from, to, Test) and their Last
   forms: the index of the first (last) element of s, from..to, Test
   holds for, or 0; with TLC's errors, whose words differ from one to
   another. */
static ManyanValue *select_in(ManyanCall *call, ManyanValue **a, const char *op, int sub, int last) {
    ManyanValue *s = to_tuple(a[0]), *test = a[sub ? 3 : 1];
    if (!s) manyan_fail(call, "The first argument of %s should be a sequence, but instead it is:\n%s", op, manyan_print(a[0]));
    int64_t n = (int64_t)manyan_size(s), from = 1, to = n;
    for (int i = 1; sub && i <= 2; i++) {
        const char *pos = i == 1 ? "second" : "third";
        if (manyan_kind(a[i]) != MANYAN_INT)
            manyan_fail(call, "The %s argument of %s should be a natural, but instead it is:\n%s", pos, op, manyan_print(a[i]));
    }
    if (sub) {
        from = manyan_int_value(a[1]), to = manyan_int_value(a[2]);
        if (from > to) return manyan_int(0);
        for (int i = 1; i <= 2; i++) {
            int64_t k = i == 1 ? from : to;
            if (k < 1 || k > n)
                manyan_fail(call, "The %s argument of %s must be in the domain of its first argument:\n%s\n, but instead it is\n%s",
                            i == 1 ? "second" : "third", op, manyan_print(a[0]), manyan_print(a[i]));
        }
    }
    for (int64_t k = last ? to : from; last ? k >= from : k <= to; k += last ? -1 : 1) {
        ManyanValue *x = manyan_value(s, (size_t)(k - 1)), *r = manyan_apply(call, test, 1, &x);
        if (manyan_kind(r) != MANYAN_BOOL)
            manyan_fail(call, "The %s argument of %s should be a boolean-valued %s, but instead it is:\n%s",
                        sub ? "fourth" : "third", op, last ? "function" : "operator", manyan_print(test));
        if (manyan_is_true(r)) return manyan_int(k);
    }
    return manyan_int(0);
}
static ManyanValue *select_in_seq(ManyanCall *call, ManyanValue **a) { return select_in(call, a, "SelectInSeq", 0, 0); }
static ManyanValue *select_in_sub_seq(ManyanCall *call, ManyanValue **a) { return select_in(call, a, "SelectInSubSeq", 1, 0); }
static ManyanValue *select_last_in_seq(ManyanCall *call, ManyanValue **a) { return select_in(call, a, "SelectLastInSeq", 0, 1); }
static ManyanValue *select_last_in_sub_seq(ManyanCall *call, ManyanValue **a) { return select_in(call, a, "SelectLastInSubSeq", 1, 1); }

/* BagsExt's FoldBag(op, base, B): op(acc, e) for each copy of each
   element e of B, in TLC's order, from base. */
static ManyanValue *fold_bag(ManyanCall *call, ManyanValue **a) {
    ManyanKind k = manyan_kind(a[2]);
    if (k != MANYAN_TUPLE && k != MANYAN_FUNCTION)
        manyan_fail(call, "The third argument of FoldBag should be a bag, but instead it is:\n%s", manyan_print(a[2]));
    ManyanValue *acc = a[1];
    for (size_t i = 0; i < manyan_size(a[2]); i++) {
        ManyanValue *e = manyan_key(a[2], i), *c = manyan_value(a[2], i);
        if (manyan_kind(c) != MANYAN_INT || manyan_int_value(c) <= 0)
            manyan_fail(call, "Applying FoldBag to the following value,\nwhich is not an element of Nat:\n%s (in: %s:>%s)",
                        manyan_print(c), manyan_print(e), manyan_print(c));
        for (int64_t j = 0; j < manyan_int_value(c); j++) {
            ManyanValue *args[2] = {acc, e};
            acc = manyan_apply(call, a[0], 2, args);
        }
    }
    return acc;
}

/* IsPrefix(s, t): of strings, or of sequences, element by element. */
static ManyanValue *is_prefix(ManyanCall *call, ManyanValue **a) {
    if (manyan_kind(a[0]) == MANYAN_STRING && manyan_kind(a[1]) == MANYAN_STRING) {
        size_t m, n;
        const char *s = manyan_string_value(a[0], &m), *t = manyan_string_value(a[1], &n);
        return manyan_bool(m <= n && !memcmp(s, t, m));
    }
    ManyanValue *s = to_tuple(a[0]), *t = to_tuple(a[1]);
    if (!s || !t) manyan_throw(call, "Cannot invoke \"tlc2.value.impl.TupleValue.size()\" because \"%s\" is null", !s ? "s" : "t");
    if (manyan_size(s) > manyan_size(t)) return manyan_bool(0);
    for (size_t i = 0; i < manyan_size(s); i++) {
        ManyanValue *x = manyan_value(s, i), *y = manyan_value(t, i);
        if (manyan_kind(x) != manyan_kind(y) || manyan_compare(x, y)) return manyan_bool(0);
    }
    return manyan_bool(1);
}

/* ---------------------------------------------------------------- SVG */

/* An element [name, attrs, children, innerText] as its markup. */
typedef struct { char *s; size_t n; } Text;

static void put(Text *t, const char *s, size_t n) {
    t->s = xrealloc(t->s, t->n + n + 1);
    memcpy(t->s + t->n, s, n);
    t->s[t->n += n] = 0;
}
static void puts_(Text *t, const char *s) { put(t, s, strlen(s)); }

static void svg_markup(ManyanCall *call, Text *t, ManyanValue *elem) {
    ManyanValue *name = manyan_field(elem, "name"), *attrs = manyan_field(elem, "attrs");
    ManyanValue *children = manyan_field(elem, "children"), *text = manyan_field(elem, "innerText");
    if (!name || manyan_kind(name) != MANYAN_STRING || !attrs || !children || !text || manyan_kind(text) != MANYAN_STRING
        || (manyan_kind(attrs) != MANYAN_FUNCTION && manyan_kind(attrs) != MANYAN_TUPLE)
        || (manyan_kind(children) != MANYAN_FUNCTION && manyan_kind(children) != MANYAN_TUPLE))
        manyan_fail(call, "An SVG element must be a record of name, attrs, children and innerText:\n%s", manyan_print(elem));
    puts_(t, "<"), puts_(t, manyan_string_value(name, NULL));
    for (size_t i = 0; manyan_kind(attrs) == MANYAN_FUNCTION && i < manyan_size(attrs); i++) {
        ManyanValue *k = manyan_key(attrs, i), *v = manyan_value(attrs, i);
        if (manyan_kind(k) != MANYAN_STRING || manyan_kind(v) != MANYAN_STRING) manyan_fail(call, "An SVG attribute must be a string:\n%s", manyan_print(attrs));
        puts_(t, " ");
        for (const char *c = manyan_string_value(k, NULL); *c; c++) put(t, *c == '_' ? "-" : c, 1);
        puts_(t, "='"), puts_(t, manyan_string_value(v, NULL)), puts_(t, "'");
    }
    puts_(t, ">");
    for (const char *c = manyan_string_value(text, NULL); *c; c++) {   /* a tuple <<1, 2>> in the text */
        if (!strncmp(c, "<<", 2)) puts_(t, "&lt;&lt;"), c++;
        else if (!strncmp(c, ">>", 2)) puts_(t, "&gt;&gt;"), c++;
        else put(t, c, 1);
    }
    for (size_t i = 0; i < manyan_size(children); i++) svg_markup(call, t, manyan_value(children, i));
    puts_(t, "</"), puts_(t, manyan_string_value(name, NULL)), puts_(t, ">");
}

static ManyanValue *svg_elem_to_string(ManyanCall *call, ManyanValue **a) {
    Text t = {0};
    svg_markup(call, &t, a[0]);
    ManyanValue *v = manyan_string(t.s ? t.s : "", t.n);
    free(t.s);
    return v;
}

/* Java's double to int: NaN 0, out of range the nearest int. */
static int64_t java_d2i(double d) { return d != d ? 0 : d >= 2147483647.0 ? INT32_MAX : d <= -2147483648.0 ? INT32_MIN : (int64_t)d; }

/* NodeOfRingNetwork(cx, cy, r, n, m): node n's place on a ring of m about (cx, cy). */
static ManyanValue *ring_network(ManyanCall *call, ManyanValue **a) {
    (void)call;
    double angle = 6.283185307179586 / (double)manyan_int_value(a[4]) * (double)manyan_int_value(a[3]), r = (double)manyan_int_value(a[2]);
    ManyanValue *names[] = {str("x"), str("y")};
    ManyanValue *at[] = {manyan_int(java_d2i((double)manyan_int_value(a[0]) + r * cos(angle))),
                      manyan_int(java_d2i((double)manyan_int_value(a[1]) + r * sin(angle)))};
    return manyan_record(2, names, at);
}

/* ---------------------------------------------------------------- Json */

/* JSON text as Json's getValue makes it a value: an array a tuple, an
   object a record, a number Gson's getAsInt, true, false and strings
   themselves; null is no value. */
typedef struct { ManyanCall *call; const char *p, *end; } Json;

static void json_space(Json *j) { while (j->p < j->end && strchr(" \t\r\n", *j->p)) j->p++; }

static _Noreturn void json_bad(Json *j) {
    manyan_throw(j->call, "com.google.gson.JsonSyntaxException: malformed JSON at %.20s", j->p < j->end ? j->p : "end of input");
}

static void json_expect(Json *j, char c) {
    json_space(j);
    if (j->p == j->end || *j->p != c) json_bad(j);
    j->p++;
}

/* The UTF-8 of code point u, at t. */
static void utf8(Text *t, unsigned u) {
    char b[4];
    size_t n = u < 0x80 ? 1 : u < 0x800 ? 2 : u < 0x10000 ? 3 : 4;
    if (n == 1) b[0] = (char)u;
    else {
        for (size_t i = n - 1; i > 0; i--) b[i] = (char)(0x80 | (u & 0x3f)), u >>= 6;
        b[0] = (char)(((0xf00 >> n) & 0xff) | u);
    }
    put(t, b, n);
}

static unsigned json_hex4(Json *j) {
    unsigned u = 0;
    for (int i = 0; i < 4; i++, j->p++) {
        char c = j->p < j->end ? *j->p : 0;
        int d = c >= '0' && c <= '9' ? c - '0' : c >= 'a' && c <= 'f' ? c - 'a' + 10 : c >= 'A' && c <= 'F' ? c - 'A' + 10 : -1;
        if (d < 0) json_bad(j);
        u = u * 16 + (unsigned)d;
    }
    return u;
}

static ManyanValue *json_string(Json *j) {
    json_expect(j, '"');
    Text t = {0};
    put(&t, "", 0);
    while (j->p < j->end && *j->p != '"') {
        if (*j->p != '\\') { put(&t, j->p++, 1); continue; }
        if (++j->p == j->end) json_bad(j);
        char c = *j->p++;
        switch (c) {
        case '"': case '\\': case '/': put(&t, &c, 1); break;
        case 'b': put(&t, "\b", 1); break;
        case 'f': put(&t, "\f", 1); break;
        case 'n': put(&t, "\n", 1); break;
        case 'r': put(&t, "\r", 1); break;
        case 't': put(&t, "\t", 1); break;
        case 'u': {
            unsigned u = json_hex4(j);
            if (u >= 0xd800 && u < 0xdc00 && j->end - j->p >= 6 && j->p[0] == '\\' && j->p[1] == 'u') {   /* a surrogate pair */
                j->p += 2;
                u = 0x10000 + ((u - 0xd800) << 10) + (json_hex4(j) - 0xdc00);
            }
            utf8(&t, u);
            break;
        }
        default: json_bad(j);
        }
    }
    if (j->p == j->end) json_bad(j);
    j->p++;
    ManyanValue *v = manyan_string(t.s, t.n);
    free(t.s);
    return v;
}

static ManyanValue *json_value(Json *j) {
    json_space(j);
    if (j->p == j->end) json_bad(j);
    if (*j->p == '"') return json_string(j);
    if (*j->p == '[' || *j->p == '{') {
        int object = *j->p++ == '{';
        Values keys = {0}, values = {0};
        json_space(j);
        if (j->p < j->end && *j->p == (object ? '}' : ']')) j->p++;
        else for (;;) {
            if (object) {   /* Gson keeps a key's last value */
                ManyanValue *k = json_string(j);
                json_expect(j, ':');
                size_t i = 0;
                while (i < keys.n && manyan_compare(keys.v[i], k)) i++;
                if (i == keys.n) add(&keys, k), add(&values, NULL);
                values.v[i] = json_value(j);
            } else {
                add(&values, json_value(j));
            }
            json_space(j);
            if (j->p < j->end && *j->p == ',') { j->p++; continue; }
            json_expect(j, object ? '}' : ']');
            break;
        }
        ManyanValue *v = object ? manyan_record(keys.n, keys.v, values.v) : manyan_tuple(values.n, values.v);
        free(keys.v), free(values.v);
        return v;
    }
    const char *word = j->p;
    while (j->p < j->end && !strchr(" \t\r\n,]}", *j->p)) j->p++;
    size_t n = (size_t)(j->p - word);
    if (n == 4 && !strncmp(word, "true", 4)) return manyan_bool(1);
    if (n == 5 && !strncmp(word, "false", 5)) return manyan_bool(0);
    if (n == 4 && !strncmp(word, "null", 4))
        manyan_throw(j->call, "java.io.IOException: Cannot convert value: unsupported JSON value null");
    char number[64], *end;
    if (n == 0 || n >= sizeof number) json_bad(j);
    memcpy(number, word, n), number[n] = 0;
    errno = 0;
    long long i = strtoll(number, &end, 10);   /* getAsInt: an int's low bits, or a decimal's truncated */
    if (*end || errno) {
        double d = strtod(number, &end);
        if (*end) { j->p = word; json_bad(j); }
        i = d >= 9.2e18 || d <= -9.2e18 ? 0 : (long long)d;
    }
    return manyan_int((int32_t)(uint32_t)(unsigned long long)i);
}

/* The file at path, or TLC's error that it cannot be read. */
static char *json_file(ManyanCall *call, ManyanValue *path, size_t *n) {
    const char *name = manyan_string_value(path, NULL);
    FILE *f = fopen(name, "rb");
    if (!f) manyan_throw(call, "%s (%s)", name, strerror(errno));
    Text t = {0};
    put(&t, "", 0);
    char chunk[1 << 16];
    for (size_t got; (got = fread(chunk, 1, sizeof chunk, f)) > 0;) put(&t, chunk, got);
    fclose(f);
    *n = t.n;
    return t.s;
}

static ManyanValue *json_deserialize(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    size_t n;
    char *text = json_file(call, a[0], &n);
    Json j = {call, text, text + n};
    ManyanValue *v = json_value(&j);
    json_space(&j);
    if (j.p != j.end) json_bad(&j);
    free(text);
    return v;
}

/* Each line not blank a value: ndJSON. */
static ManyanValue *nd_json_deserialize(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    size_t n;
    char *text = json_file(call, a[0], &n);
    Values lines = {0};
    for (const char *p = text, *end = text + n; p < end;) {
        const char *eol = memchr(p, '\n', (size_t)(end - p));
        Json j = {call, p, eol ? eol : end};
        json_space(&j);
        if (j.p < j.end) {
            add(&lines, json_value(&j));
            json_space(&j);
            if (j.p != j.end) json_bad(&j);
        }
        p = eol ? eol + 1 : end;
    }
    ManyanValue *v = manyan_tuple(lines.n, lines.v);
    free(lines.v), free(text);
    return v;
}

/* A value as Json's getNode writes it, with Gson: a record an object, a
   tuple, a set or a function on 1..n an array, another function an object
   keyed by its keys, strings themselves and the others as TLC prints
   them; a model value its name. */
static void json_node(ManyanCall *call, Text *t, ManyanValue *v);

static _Noreturn void json_unsupported(ManyanCall *call, ManyanValue *v) {
    manyan_throw(call, "Cannot convert value: unsupported value type tlc2.value.impl.%s", manyan_class(v));
}

static void json_quote(Text *t, const char *s, size_t n) {
    put(t, "\"", 1);
    for (size_t i = 0; i < n; i++) {
        unsigned char c = (unsigned char)s[i];
        const char *e = c == '"' ? "\\\"" : c == '\\' ? "\\\\" : c == '\t' ? "\\t" : c == '\b' ? "\\b"
                      : c == '\n' ? "\\n" : c == '\r' ? "\\r" : c == '\f' ? "\\f" : NULL;
        char u[8];
        if (!e && c < 0x20) snprintf(u, sizeof u, "\\u%04x", c), e = u;
        if (!e && c == 0xe2 && i + 2 < n && (unsigned char)s[i + 1] == 0x80 && ((unsigned char)s[i + 2] | 1) == 0xa9)   /* U+2028, U+2029 */
            snprintf(u, sizeof u, "\\u%04x", 0x2000 + ((unsigned char)s[i + 2] & 0x3f)), e = u, i += 2;
        if (e) puts_(t, e);
        else put(t, (const char *)&c, 1);
    }
    put(t, "\"", 1);
}

static int json_sequence(ManyanValue *f) {   /* isValidSequence: its domain 1..n */
    for (size_t i = 0; i < manyan_size(f); i++)
        if (manyan_kind(manyan_key(f, i)) != MANYAN_INT || manyan_int_value(manyan_key(f, i)) != (int64_t)i + 1) return 0;
    return 1;
}

static int is_class(ManyanValue *v, const char *c) { return !strcmp(manyan_class(v), c); }
static int is_fcn(ManyanValue *v) { return is_class(v, "FcnRcdValue") || is_class(v, "FcnLambdaValue"); }

static void json_values(ManyanCall *call, Text *t, ManyanValue *v, int set) {
    ManyanValue *elems = set ? manyan_elements(v) : v;
    size_t n = manyan_size(elems);
    put(t, "[", 1);
    for (size_t i = 0; i < n; i++) {
        if (i) put(t, ",", 1);
        json_node(call, t, set ? manyan_element(elems, i) : manyan_value(v, i));
    }
    put(t, "]", 1);
}

/* An object of v's keys, the key i of a tuple's element i (Gson keeps a
   key's place and its last value). */
static void json_fields(ManyanCall *call, Text *t, ManyanValue *v) {
    size_t n = manyan_size(v), m = 0;
    Text *keys = xcalloc(n + 1, sizeof *keys), *values = xcalloc(n + 1, sizeof *values);
    for (size_t i = 0; i < n; i++) {
        Text key = {0}, value = {0};
        size_t at = manyan_kept(v, i);
        ManyanValue *k = manyan_kind(v) == MANYAN_TUPLE ? NULL : manyan_key(v, at);
        size_t len;
        char index[24];
        snprintf(index, sizeof index, "%zu", i);
        const char *name = !k ? index : manyan_kind(k) == MANYAN_STRING ? manyan_string_value(k, &len) : manyan_to_string(k);
        json_quote(&key, name, k && manyan_kind(k) == MANYAN_STRING ? len : strlen(name));
        json_node(call, &value, manyan_value(v, at));
        size_t j = 0;
        while (j < m && strcmp(keys[j].s, key.s)) j++;
        if (j < m) free(key.s), free(values[j].s), values[j] = value;
        else keys[m] = key, values[m++] = value;
    }
    put(t, "{", 1);
    for (size_t j = 0; j < m; j++) {
        if (j) put(t, ",", 1);
        put(t, keys[j].s, keys[j].n), put(t, ":", 1), put(t, values[j].s, values[j].n);
        free(keys[j].s), free(values[j].s);
    }
    put(t, "}", 1);
    free(keys), free(values);
}

static void json_fcn(ManyanCall *call, Text *t, ManyanValue *v) {   /* getObjectNode(FcnRcdValue) */
    if (json_sequence(v)) json_values(call, t, v, 0);
    else json_fields(call, t, v);
}

static void json_node(ManyanCall *call, Text *t, ManyanValue *v) {
    size_t len;
    const char *s;
    char number[24];
    if (is_class(v, "RecordValue")) json_fields(call, t, v);
    else if (is_class(v, "TupleValue")) json_values(call, t, v, 0);
    else if (manyan_kind(v) == MANYAN_STRING) s = manyan_string_value(v, &len), json_quote(t, s, len);
    else if (manyan_kind(v) == MANYAN_MODEL) json_quote(t, manyan_print(v), strlen(manyan_print(v)));
    else if (manyan_kind(v) == MANYAN_INT) snprintf(number, sizeof number, "%lld", (long long)manyan_int_value(v)), puts_(t, number);
    else if (manyan_kind(v) == MANYAN_BOOL) puts_(t, manyan_is_true(v) ? "true" : "false");
    else if (is_fcn(v)) json_fcn(call, t, v);
    else if (manyan_elements(v)) json_values(call, t, v, 1);
    else json_unsupported(call, v);
}

static ManyanValue *json_result(Text *t) {
    ManyanValue *v = manyan_string(t->s ? t->s : "", t->n);
    free(t->s);
    return v;
}

static ManyanValue *to_json(ManyanCall *call, ManyanValue **a) {
    Text t = {0};
    json_node(call, &t, a[0]);
    return json_result(&t);
}

static ManyanValue *to_json_array(ManyanCall *call, ManyanValue **a) {   /* getArrayNode */
    Text t = {0};
    ManyanValue *v = a[0];
    if (is_class(v, "TupleValue")) json_values(call, &t, v, 0);
    else if (is_fcn(v)) json_sequence(v) ? json_values(call, &t, v, 0) : json_fields(call, &t, v);
    else if (manyan_kind(v) == MANYAN_SET && manyan_elements(v)) json_values(call, &t, v, 1);
    else json_unsupported(call, v);
    return json_result(&t);
}

static ManyanValue *to_json_object(ManyanCall *call, ManyanValue **a) {   /* getObjectNode */
    Text t = {0};
    ManyanValue *v = a[0];
    if (is_class(v, "RecordValue") || is_class(v, "TupleValue")) json_fields(call, &t, v);
    else if (is_fcn(v)) json_fcn(call, &t, v);
    else json_unsupported(call, v);
    return json_result(&t);
}

/* Writes text to the file at path, its directories made. */
static void json_write(ManyanCall *call, ManyanValue *path, Text *t) {
    const char *name = manyan_string_value(path, NULL);
    char *dir = strdup(name);
    for (char *p = strchr(dir + 1, '/'), *last = strrchr(dir, '/'); p && p <= last; p = strchr(p + 1, '/')) {
        *p = 0;
        mkdir(dir, 0777);
        *p = '/';
    }
    free(dir);
    FILE *f = fopen(name, "w");
    if (!f) manyan_throw(call, "%s (%s)", name, strerror(errno));
    fwrite(t->s ? t->s : "", 1, t->n, f);
    fclose(f);
    free(t->s);
}

static ManyanValue *json_serialize(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    if (!to_tuple(a[1]) && !is_record(a[1]))
        manyan_fail(call, "The second argument of JsonSerialize should be a sequence or record, but instead it is:\n%s", manyan_print(a[1]));
    Text t = {0};
    json_node(call, &t, a[1]);
    json_write(call, a[0], &t);
    return manyan_bool(1);
}

static ManyanValue *nd_json_serialize(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    ManyanValue *v = to_tuple(a[1]);
    if (!v) manyan_fail(call, "The second argument of ndJsonSerialize should be a sequence, but instead it is:\n%s", manyan_print(a[1]));
    Text t = {0};
    for (size_t i = 0; i < manyan_size(v); i++) json_node(call, &t, manyan_value(v, i)), put(&t, "\n", 1);
    json_write(call, a[0], &t);
    return manyan_bool(1);
}

/* ---------------------------------------------------------------- Graphs, UndirectedGraphs */

static ManyanValue *graph_set(ManyanValue *g, const char *field) {
    ManyanValue *v = manyan_field(g, field);
    return v ? manyan_elements(v) : NULL;
}

/* G's nodes and edges, enumerated, if G is a graph record; else the error
   TLC gives for argument POS of OP, a KIND. */
static void to_graph(ManyanCall *call, const char *op, const char *pos, const char *kind, ManyanValue *g,
                     ManyanValue **nodes, ManyanValue **edges) {
    const char *bad = !is_record(g) ? "record with a node and an edge field"
                    : !(*nodes = graph_set(g, "node")) ? "record whose node field is a set"
                    : !(*edges = graph_set(g, "edge")) ? "record whose edge field is a set" : NULL;
    if (bad) manyan_fail(call, "The %s argument of %s should be a %s %s, but instead it is:\n%s", pos, op, kind, bad, manyan_print(g));
}

static long position(ManyanValue *set, ManyanValue *v) {
    for (long lo = 0, hi = (long)manyan_size(set) - 1; lo <= hi;) {
        long m = (lo + hi) / 2;
        int c = manyan_compare(manyan_element(set, (size_t)m), v);
        if (!c) return m;
        if (c < 0) lo = m + 1; else hi = m - 1;
    }
    return -1;
}

static size_t root(size_t *parent, size_t i) {
    while (parent[i] != i) i = parent[i] = parent[parent[i]];
    return i;
}

/* The components as TLC's union-find finds them: an edge is a set of one
   or two nodes, and other edges, or those leaving the nodes, join nothing. */
static ManyanValue *connected_components(ManyanCall *call, ManyanValue **a) {
    ManyanValue *nodes, *edges;
    to_graph(call, "ConnectedComponents", "first", "undirected graph", a[0], &nodes, &edges);
    size_t n = manyan_size(nodes), *parent = xmalloc(sizeof(size_t) * (n + 1));
    for (size_t i = 0; i < n; i++) parent[i] = i;
    for (size_t k = 0; k < manyan_size(edges); k++) {
        ManyanValue *e = manyan_elements(manyan_element(edges, k));
        if (!e || manyan_size(e) == 0 || manyan_size(e) > 2) continue;
        long i = position(nodes, manyan_element(e, 0)), j = position(nodes, manyan_element(e, manyan_size(e) - 1));
        if (i >= 0 && j >= 0) parent[root(parent, (size_t)j)] = root(parent, (size_t)i);
    }
    Values *members = xcalloc(n + 1, sizeof(Values)), out = {0};
    for (size_t i = 0; i < n; i++) add(&members[root(parent, i)], manyan_element(nodes, i));
    for (size_t i = 0; i < n; i++)
        if (members[i].n) add(&out, manyan_set(members[i].n, members[i].v)), free(members[i].v);
    ManyanValue *r = manyan_set(out.n, out.v);
    free(out.v), free(members), free(parent);
    return r;
}

/* A directed graph's arcs, by the positions of its nodes: those of node i
   go to to[start[i]] .. to[start[i + 1] - 1]. An edge is a pair of nodes;
   another, or one leaving the nodes, is none, as in Graphs' definitions. */
typedef struct { size_t n, *start, *to; } Arcs;

static Arcs arcs_of(ManyanValue *nodes, ManyanValue *edges, int transpose) {
    size_t n = manyan_size(nodes), m = manyan_size(edges), k = 0;
    long *from = xmalloc(sizeof(long) * (m + 1)), *to = xmalloc(sizeof(long) * (m + 1));
    Arcs a = {n, xcalloc(n + 2, sizeof(size_t)), xmalloc(sizeof(size_t) * (m + 1))};
    for (size_t i = 0; i < m; i++) {
        ManyanValue *e = manyan_element(edges, i);
        if (manyan_kind(e) != MANYAN_TUPLE || manyan_size(e) != 2) continue;
        from[k] = position(nodes, manyan_value(e, transpose)), to[k] = position(nodes, manyan_value(e, !transpose));
        if (from[k] >= 0 && to[k] >= 0) a.start[from[k] + 2]++, k++;
    }
    for (size_t i = 2; i <= n + 1; i++) a.start[i] += a.start[i - 1];
    for (size_t i = 0; i < k; i++) a.to[a.start[from[i] + 1]++] = (size_t)to[i];   /* start[f + 1]: f's next arc */
    free(from), free(to);
    return a;
}

static void arcs_free(Arcs a) { free(a.start), free(a.to); }

/* How many nodes are reachable from node s, each marked in seen. */
static size_t reach(Arcs a, size_t s, char *seen) {
    size_t *queue = xmalloc(sizeof(size_t) * (a.n + 1)), head = 0, tail = 0;
    seen[s] = 1, queue[tail++] = s;
    while (head < tail)
        for (size_t i = queue[head++], k = a.start[i]; k < a.start[i + 1]; k++)
            if (!seen[a.to[k]]) seen[a.to[k]] = 1, queue[tail++] = a.to[k];
    free(queue);
    return tail;
}

static ManyanValue *are_connected_in(ManyanCall *call, ManyanValue **a) {
    ManyanValue *nodes, *edges;
    to_graph(call, "AreConnectedIn", "third", "graph", a[2], &nodes, &edges);
    long m = position(nodes, a[0]), n = position(nodes, a[1]);
    if (m < 0 || n < 0) return manyan_bool(0);
    if (m == n) return manyan_bool(1);
    Arcs arcs = arcs_of(nodes, edges, 0);
    char *seen = xcalloc(arcs.n, 1);
    reach(arcs, (size_t)m, seen);
    int r = seen[n];
    free(seen), arcs_free(arcs);
    return manyan_bool(r);
}

/* Every node reaches the first, and the first every node. */
static ManyanValue *is_strongly_connected(ManyanCall *call, ManyanValue **a) {
    ManyanValue *nodes, *edges;
    to_graph(call, "IsStronglyConnected", "first", "graph", a[0], &nodes, &edges);
    int r = 1;
    for (int transpose = 0; transpose < 2 && r && manyan_size(nodes); transpose++) {
        Arcs arcs = arcs_of(nodes, edges, transpose);
        char *seen = xcalloc(arcs.n, 1);
        r = reach(arcs, 0, seen) == arcs.n;
        free(seen), arcs_free(arcs);
    }
    return manyan_bool(r);
}

/* Each simple path that path, of n nodes, starts. */
static void simple_paths(Arcs a, size_t *path, size_t n, char *on, ManyanValue *nodes, Values *out) {
    ManyanValue **elems = xmalloc(sizeof(ManyanValue *) * n);
    for (size_t i = 0; i < n; i++) elems[i] = manyan_element(nodes, path[i]);
    add(out, manyan_tuple(n, elems));
    free(elems);
    for (size_t k = a.start[path[n - 1]]; k < a.start[path[n - 1] + 1]; k++)
        if (!on[a.to[k]]) {
            on[path[n] = a.to[k]] = 1;
            simple_paths(a, path, n + 1, on, nodes, out);
            on[a.to[k]] = 0;
        }
}

static ManyanValue *simple_path(ManyanCall *call, ManyanValue **a) {
    ManyanValue *nodes, *edges;
    to_graph(call, "SimplePath", "first", "graph", a[0], &nodes, &edges);
    Arcs arcs = arcs_of(nodes, edges, 0);
    size_t *path = xmalloc(sizeof(size_t) * (arcs.n + 1));
    char *on = xcalloc(arcs.n + 1, 1);
    Values out = {0};
    for (size_t s = 0; s < arcs.n; s++) on[path[0] = s] = 1, simple_paths(arcs, path, 1, on, nodes, &out), on[s] = 0;
    ManyanValue *r = manyan_set(out.n, out.v);
    free(out.v), free(on), free(path), arcs_free(arcs);
    return r;
}

/* ---------------------------------------------------------------- CSV */

/* Appends text and a line to the file, as Files.write with CREATE and APPEND. */
static void append_line(ManyanCall *call, ManyanValue *file, const char *text) {
    const char *path = manyan_string_value(file, NULL);
    FILE *f = fopen(path, "a");
    if (!f || fprintf(f, "%s\n", text) < 0) manyan_throw(call, "%s", path);
    fclose(f);
}

/* CSVWrite(template, val, file): val's elements, as TLC writes them,
   put in the template by Java's String.format. */
static ManyanValue *csv_write(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    ManyanValue *vals = to_tuple(a[1]);
    if (!vals) manyan_fail(call, "The argument of CSVWrite should be a sequence, but instead it is:\n%s", manyan_print(a[1]));
    size_t n = manyan_size(vals);
    const char **args = manyan_alloc(sizeof *args * (n + 1));
    for (size_t i = 0; i < n; i++) args[i] = manyan_to_string(manyan_value(vals, i));
    ManyanValue *line = manyan_format(call, manyan_string_value(a[0], NULL), n, args);
    append_line(call, a[2], manyan_string_value(line, NULL));
    return manyan_bool(1);
}

/* A line of the record's names, or of its values as TLC writes them, between delimiters. */
static void write_fields(ManyanCall *call, ManyanValue *file, ManyanValue *r, int names, const char *delim) {
    Text t = {0};
    put(&t, "", 0);
    for (size_t i = 0; i < manyan_size(r); i++) {
        if (i) puts_(&t, delim);
        puts_(&t, names ? manyan_string_value(manyan_key(r, i), NULL) : manyan_to_string(manyan_value(r, i)));
    }
    append_line(call, file, t.s);
    free(t.s);
}

/* CSVWriteRecord(record, delimiter, headers, file): its fields in order,
   after a line of their names if headers. */
static ManyanValue *csv_write_record(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    if (!is_record(a[0])) manyan_fail(call, "The argument of CSVWriteRecord should be a record, but instead it is:\n%s", manyan_print(a[0]));
    if (manyan_is_true(a[2])) write_fields(call, a[3], a[0], 1, manyan_string_value(a[1], NULL));
    write_fields(call, a[3], a[0], 0, manyan_string_value(a[1], NULL));
    return manyan_bool(1);
}

/* The file's lines, as Files.readAllLines: NULL if it does not exist. */
static char **lines_of(ManyanCall *call, ManyanValue *file, size_t *n) {
    const char *path = manyan_string_value(file, NULL);
    FILE *f = fopen(path, "rb");
    if (!f) {
        if (errno == ENOENT) return NULL;
        manyan_throw(call, "%s", path);
    }
    Text t = {0};
    put(&t, "", 0);
    char chunk[1 << 16];
    for (size_t got; (got = fread(chunk, 1, sizeof chunk, f)) > 0;) put(&t, chunk, got);
    fclose(f);
    char **lines = xmalloc(sizeof(char *) * (t.n + 2));
    *n = 0;
    for (char *p = t.s, *end = t.s + t.n; p < end;) {
        char *eol = p + strcspn(p, "\r\n");
        lines[(*n)++] = p;
        p = eol + (eol < end && *eol == '\r' && eol[1] == '\n') + 1;
        *eol = 0;
    }
    lines[*n] = t.s;   /* the text, to free */
    return lines;
}

static ManyanValue *csv_records(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    size_t n = 0;
    char **lines = lines_of(call, a[0], &n);
    if (lines) free(lines[n]), free(lines);
    return manyan_int((int64_t)n);
}

static size_t length(ManyanValue *s) {
    size_t n;
    manyan_string_value(s, &n);
    return n;
}

/* Java's line.split(delimiter), a regular expression: its trailing empty
   fields dropped. */
static void split(ManyanCall *call, const char *line, const char *delimiter, Values *fields) {
    regex_t re;
    if (regcomp(&re, delimiter, REG_EXTENDED)) manyan_throw(call, "%s", delimiter);
    regmatch_t m;
    const char *p = line, *from = line;
    int matched = 0;
    while (!regexec(&re, p, 1, &m, p > line ? REG_NOTBOL : 0)) {
        const char *start = p + m.rm_so, *end = p + m.rm_eo;
        matched = 1;
        if (end > line) add(fields, manyan_string(from, (size_t)(start - from))), from = end;   /* none before an empty match at 0 */
        if (end > start) p = end;
        else if (*end) p = end + 1;
        else break;
    }
    regfree(&re);
    add(fields, str(from));
    while (matched && fields->n && !length(fields->v[fields->n - 1])) fields->n--;
}

/* CSVRead(columns, delimiter, file): a record of each line, its fields
   named by columns. */
static ManyanValue *csv_read(ManyanCall *call, ManyanValue **a) {
    manyan_effect(call);
    ManyanValue *columns = to_tuple(a[0]);
    if (!columns) manyan_fail(call, "The argument of CSVRead should be a sequence, but instead it is:\n%s", manyan_print(a[0]));
    size_t n = 0, ncols = manyan_size(columns);
    char **lines = lines_of(call, a[2], &n);
    if (!lines) return manyan_tuple(0, NULL);
    ManyanValue **names = xcalloc(ncols + 1, sizeof *names);
    for (size_t i = 0; i < ncols; i++) {
        names[i] = manyan_value(columns, i);
        if (manyan_kind(names[i]) != MANYAN_STRING)
            manyan_throw(call, "class tlc2.value.impl.%s cannot be cast to class tlc2.value.impl.StringValue (tlc2.value.impl.%s and "
                            "tlc2.value.impl.StringValue are in unnamed module of loader 'app')", manyan_class(names[i]), manyan_class(names[i]));
    }
    Values records = {0};
    for (size_t i = 0; i < n; i++) {
        Values fields = {0};
        split(call, lines[i], manyan_string_value(a[1], NULL), &fields);
        if (fields.n < ncols) manyan_throw(call, "Index %zu out of bounds for length %zu", fields.n, fields.n);
        add(&records, manyan_record(ncols, names, fields.v));
        free(fields.v);
    }
    free(lines[n]), free(lines);
    ManyanValue *r = manyan_tuple(records.n, records.v);
    free(records.v), free(names);
    return r;
}

/* ---------------------------------------------------------------- Statistics */

/* A number as Java's MessageFormat gives it: #,##0.### */
static const char *java_number(double d) {
    static char out[64];
    char digits[48];
    snprintf(digits, sizeof digits, "%.3f", d);
    char *dot = strchr(digits, '.'), *e = digits + strlen(digits);
    while (e > dot + 1 && e[-1] == '0') *--e = 0;
    if (e == dot + 1) *dot = 0;
    if (!strcmp(digits, "-0")) strcpy(digits, "0");
    const char *p = digits, *end = strchr(digits, '.');
    size_t ints = (end ? (size_t)(end - digits) : strlen(digits)) - (*p == '-'), k = 0;
    if (*p == '-') out[k++] = *p++;
    for (size_t i = 0; i < ints; i++) {
        if (i && (ints - i) % 3 == 0) out[k++] = ',';
        out[k++] = *p++;
    }
    strcpy(out + k, p);
    return out;
}

/* Commons Math's regularized gamma functions, P(a, x) and Q(a, x). */
static double gamma_q(double a, double x);

static double gamma_p(double a, double x) {
    if (x == 0) return 0;
    if (x >= a + 1) return 1 - gamma_q(a, x);
    double an = 1 / a, sum = an;
    for (double n = 1; fabs(an / sum) > 1e-14 && sum < INFINITY; n++) an *= x / (a + n), sum += an;
    return exp(-x + a * log(x) - lgamma(a)) * sum;
}

static double gamma_q(double a, double x) {   /* x >= a + 1: its continued fraction, by Lentz */
    if (x < a + 1) return 1 - gamma_p(a, x);
    double h = 1 - a + x, small = 1e-50, d = 0, c;
    if (fabs(h) <= small) h = small;
    c = h;
    for (double n = 1;; n++) {
        double an = 2 * n + 1 - a + x, bn = n * (a - n);
        d = an + bn * d;
        if (fabs(d) <= small) d = small;
        c = an + bn / c;
        if (fabs(c) <= small) c = small;
        d = 1 / d;
        double delta = c * d;
        h *= delta;
        if (fabs(delta - 1) < 1e-14) break;
    }
    return exp(-x + a * log(x) - lgamma(a)) / h;
}

/* A function's values, each an integer, in order, as TLC casts them. */
static double *counts(ManyanCall *call, ManyanValue *f) {
    double *v = manyan_alloc(sizeof *v * (manyan_size(f) + 1));
    for (size_t i = 0; i < manyan_size(f); i++) {
        ManyanValue *x = manyan_value(f, i);
        if (manyan_kind(x) != MANYAN_INT)
            manyan_throw(call, "class tlc2.value.impl.%s cannot be cast to class tlc2.value.impl.IntValue (tlc2.value.impl.%s and "
                            "tlc2.value.impl.IntValue are in unnamed module of loader 'app')", manyan_class(x), manyan_class(x));
        v[i] = (double)manyan_int_value(x);
    }
    return v;
}

/* ChiSquare(expected, actual, alpha): whether Commons Math's chi-square
   test keeps that actual is distributed as expected, at the significance
   level alpha, a string. */
static ManyanValue *chi_square(ManyanCall *call, ManyanValue **a) {
    for (int i = 0; i < 2; i++)   /* TLC's error that it is not a function fails itself */
        if (manyan_kind(a[i]) != MANYAN_FUNCTION && manyan_kind(a[i]) != MANYAN_TUPLE)
            manyan_throw(call, "Cannot invoke \"tlc2.value.impl.Value.toString()\" because \"<local%d>\" is null", i);
    if (manyan_kind(a[2]) != MANYAN_STRING)
        manyan_fail(call, "The third argument of ChiSquare should be a StringValue representing a double in (0, .5], but instead it is:\n%s",
                 manyan_print(a[2]));
    double *e = counts(call, a[0]), *o = counts(call, a[1]);
    size_t n = manyan_size(a[0]), m = manyan_size(a[1]);
    const char *s = manyan_string_value(a[2], NULL);   /* Double.valueOf */
    while (*s && (unsigned char)*s <= ' ') s++;
    size_t len = strlen(s);
    while (len && (unsigned char)s[len - 1] <= ' ') len--;
    char *text = manyan_alloc(len + 1), *end;
    memcpy(text, s, len);
    double alpha = strtod(text, &end);
    if (end > text && strchr("fFdD", *end) && *end) end++;
    int number = end > text && !*end && (isdigit((unsigned char)*text) || strchr("+-.", *text) || !strncmp(text, "NaN", 3) || !strncmp(text, "Infinity", 8));
    if (!number) manyan_throw(call, len ? "For input string: \"%s\"" : "empty String", text);
    if (alpha <= 0 || alpha > 0.5) manyan_throw(call, "out of bounds significance level %s, must be between 0 and 0.5", java_number(alpha));
    double shape = ((double)n - 1) / 2;
    if (shape <= 0) manyan_throw(call, "shape (%s)", java_number(shape));
    if (n != m) manyan_throw(call, "%zu != %zu", n, m);
    for (size_t i = 0; i < n; i++)
        if (e[i] <= 0) manyan_throw(call, "%s is smaller than, or equal to, the minimum (0)", java_number(e[i]));
    for (size_t i = 0; i < n; i++)
        if (o[i] < 0) manyan_throw(call, "%s is smaller than the minimum (0)", java_number(o[i]));
    double sum_e = 0, sum_o = 0, ratio = 1, chi = 0;
    for (size_t i = 0; i < n; i++) sum_e += e[i], sum_o += o[i];
    if (fabs(sum_e - sum_o) > 1e-5) ratio = sum_o / sum_e;
    for (size_t i = 0; i < n; i++) chi += (o[i] - ratio * e[i]) * (o[i] - ratio * e[i]) / (ratio * e[i]);
    double p = 1 - (chi <= 0 ? 0 : gamma_p(shape, chi / 2));
    return manyan_bool(!(p < alpha));
}

/* ---------------------------------------------------------------- Apalache */

/* Apalache's module, its operators as TLC evaluates them from it with
   apalache.jar on its class path. */
static const char apalache[] =
    "---- MODULE Apalache ----\n"
    "__x := __e == __x = __e\n"
    "Gen(__size) == {}\n"
    "Guess(__S) == CHOOSE __x \\in __S: TRUE\n"
    "SetAsFun(__S) ==\n"
    "    LET __Dom == { __x: <<__x, __y>> \\in __S }\n"
    "        __Rng == { __y: <<__x, __y>> \\in __S }\n"
    "    IN [ __x \\in __Dom |-> CHOOSE __y \\in __Rng: <<__x, __y>> \\in __S ]\n"
    "LOCAL INSTANCE Integers\n"
    "MkSeq(__N, __F(_)) == [ __i \\in (1..__N) |-> __F(__i) ]\n"
    "LOCAL INSTANCE Sequences\n"
    "FunAsSeq(__fn, __len, __capacity) ==\n"
    "    LET __FunAsSeq_elem_ctor(__i) == __fn[__i] IN\n"
    "    SubSeq(MkSeq(__capacity, __FunAsSeq_elem_ctor), 1, __len)\n"
    "Skolem(__e) == __e\n"
    "Expand(__S) == __S\n"
    "ConstCardinality(__cardExpr) == __cardExpr\n"
    "RECURSIVE ApaFoldSet(_, _, _)\n"
    "ApaFoldSet(__Op(_,_), __v, __S) ==\n"
    "    IF __S = {} THEN __v\n"
    "    ELSE LET __w == CHOOSE __x \\in __S: TRUE IN\n"
    "         ApaFoldSet(__Op, __Op(__v, __w), __S \\ {__w})\n"
    "RECURSIVE ApaFoldSeqLeft(_, _, _)\n"
    "ApaFoldSeqLeft(__Op(_,_), __v, __seq) ==\n"
    "    IF __seq = <<>> THEN __v\n"
    "    ELSE ApaFoldSeqLeft(__Op, __Op(__v, Head(__seq)), Tail(__seq))\n"
    "RECURSIVE Repeat(_, _, _)\n"
    "Repeat(__F(_,_), __N, __x) ==\n"
    "    IF __N <= 0 THEN __x ELSE __F(Repeat(__F, __N - 1, __x), __N)\n"
    "====\n";

/* Apalache's internal modules, which its rewirings of the community
   modules use, with the meanings Apalache gives their operators. */
static const char apalache_folds[] =
    "---- MODULE __apalache_folds ----\n"
    "LOCAL INSTANCE Integers\n"
    "LOCAL INSTANCE Sequences\n"
    "RECURSIVE __ApalacheFoldSet(_, _, _)\n"
    "__ApalacheFoldSet(__Op(_,_), __v, __S) ==\n"
    "    IF __S = {} THEN __v\n"
    "    ELSE LET __w == CHOOSE __x \\in __S: TRUE IN\n"
    "         __ApalacheFoldSet(__Op, __Op(__v, __w), __S \\ {__w})\n"
    "RECURSIVE __ApalacheFoldSeq(_, _, _)\n"
    "__ApalacheFoldSeq(__Op(_,_), __v, __seq) ==\n"
    "    IF __seq = <<>> THEN __v\n"
    "    ELSE __ApalacheFoldSeq(__Op, __Op(__v, Head(__seq)), Tail(__seq))\n"
    "__ApalacheMkSeq(__N, __F(_)) == [ __i \\in (1..__N) |-> __F(__i) ]\n"
    "====\n";

static const char apalache_internal[] =
    "---- MODULE __apalache_internal ----\n"
    "LOCAL INSTANCE Sequences\n"
    "LOCAL INSTANCE TLC\n"
    "__ApalacheSeqCapacity(__seq) == Len(__seq)\n"
    "__NotSupportedByModelChecker(__msg) == Assert(FALSE, __msg)\n"
    "====\n";

/* ---------------------------------------------------------------- the table */

#define OVERRIDE(module, method) "public static " J_V " tlc2.overrides." module "." method

int manyan_std_init(void) {
    static const struct { const char *module, *name; int arity; ManyanNative fn; const char *java; } natives[] = {
        {"IOUtils", "IOEnv", 0, io_env, OVERRIDE("IOUtils", "ioEnv()")},
        {"IOUtils", "atoi", 1, atoi_, OVERRIDE("IOUtils", "atoi(" J_V ")")},
        {"IOUtils", "IOExec", 1, io_exec, OVERRIDE("IOUtils", "ioExec(" J_V ")")},
        {"IOUtils", "IOEnvExec", 2, io_env_exec, OVERRIDE("IOUtils", "ioEnvExec(" J_V "," J_V ")")},
        {"IOUtils", "Serialize", MANYAN_LAZY, serialize,
         "public static synchronized " J_V " tlc2.overrides.IOUtils.textSerialize(" J_EVAL ")"},
        {"SequencesExt", "SetToSeq", 1, set_to_seq, OVERRIDE("SequencesExt", "SetToSeq(" J_V ")")},
        {"SequencesExt", "FoldSeq", 3, fold_function, OVERRIDE("SequencesExt", "foldSeq(" J_OP "," J_V "," J_V ")")},
        {"SequencesExt", "SelectInSeq", 2, select_in_seq, OVERRIDE("SequencesExt", "selectInSeq(" J_V "," J_OP ")")},
        {"SequencesExt", "SelectInSubSeq", 4, select_in_sub_seq,
         OVERRIDE("SequencesExt", "SelectInSubSeq(" J_V "," J_V "," J_V "," J_OP ")")},
        {"SequencesExt", "SelectLastInSeq", 2, select_last_in_seq, OVERRIDE("SequencesExt", "selectLastInSeq(" J_V "," J_OP ")")},
        {"SequencesExt", "SelectLastInSubSeq", 4, select_last_in_sub_seq,
         OVERRIDE("SequencesExt", "SelectLastInSubSeq(" J_V "," J_V "," J_V "," J_OP ")")},
        {"SequencesExt", "IsPrefix", 2, is_prefix, OVERRIDE("SequencesExt", "isPrefix(" J_V "," J_V ")")},
        {"BagsExt", "FoldBag", 3, fold_bag, OVERRIDE("BagsExt", "foldBag(" J_OP "," J_V "," J_V ")")},
        {"Functions", "FoldFunction", 3, fold_function, OVERRIDE("Functions", "foldFunction(" J_OP "," J_V "," J_V ")")},
        {"Functions", "FoldFunctionOnSet", 4, fold_function_on_set,
         OVERRIDE("Functions", "foldFunctionOnSet(" J_OP "," J_V "," J_V "," J_V ")")},
        {"SVG", "SVGElemToString", 1, svg_elem_to_string, OVERRIDE("SVG", "SVGElemToString(" J_V ")")},
        {"SVG", "NodeOfRingNetwork", 5, ring_network, OVERRIDE("SVG", "ringNetwork(" J_I "," J_I "," J_I "," J_I "," J_I ")")},
        {"Json", "JsonDeserialize", 1, json_deserialize,
         "public static tlc2.value.IValue tlc2.overrides.Json.deserialize(tlc2.value.impl.StringValue) throws java.io.IOException"},
        {"Json", "ndJsonDeserialize", 1, nd_json_deserialize,
         "public static tlc2.value.IValue tlc2.overrides.Json.ndDeserialize(tlc2.value.impl.StringValue) throws java.io.IOException"},
        {"Json", "ToJson", 1, to_json, "public static " J_S " tlc2.overrides.Json.toJson(tlc2.value.IValue) throws java.io.IOException"},
        {"Json", "ToJsonArray", 1, to_json_array, "public static " J_S " tlc2.overrides.Json.toJsonArray(tlc2.value.IValue) throws java.io.IOException"},
        {"Json", "ToJsonObject", 1, to_json_object, "public static " J_S " tlc2.overrides.Json.toJsonObject(tlc2.value.IValue) throws java.io.IOException"},
        {"Json", "JsonSerialize", 2, json_serialize,
         "public static synchronized tlc2.value.impl.BoolValue tlc2.overrides.Json.serialize(tlc2.value.impl.StringValue," J_V ") throws java.io.IOException"},
        {"Json", "ndJsonSerialize", 2, nd_json_serialize,
         "public static synchronized tlc2.value.impl.BoolValue tlc2.overrides.Json.ndSerialize(tlc2.value.impl.StringValue," J_V ") throws java.io.IOException"},
        {"Graphs", "SimplePath", 1, simple_path, OVERRIDE("Graphs", "simplePath(" J_V ")")},
        {"Graphs", "AreConnectedIn", 3, are_connected_in, OVERRIDE("Graphs", "areConnectedIn(" J_V "," J_V "," J_V ")")},
        {"Graphs", "IsStronglyConnected", 1, is_strongly_connected, OVERRIDE("Graphs", "isStronglyConnected(" J_V ")")},
        {"CSV", "CSVWrite", 3, csv_write,
         "public static " J_V " tlc2.overrides.CSV.write(" J_S "," J_V "," J_S ") throws java.io.IOException"},
        {"CSV", "CSVWriteRecord", 4, csv_write_record,
         "public static " J_V " tlc2.overrides.CSV.writeRecord(" J_V "," J_S ",tlc2.value.impl.BoolValue," J_S ") throws java.io.IOException"},
        {"CSV", "CSVRead", 3, csv_read,
         "public static " J_V " tlc2.overrides.CSV.read(" J_V "," J_S "," J_S ") throws java.io.IOException"},
        {"CSV", "CSVRecords", 1, csv_records, "public static " J_V " tlc2.overrides.CSV.records(" J_S ") throws java.io.IOException"},
        {"Statistics", "ChiSquare", 3, chi_square, OVERRIDE("Statistics", "chiSquare(" J_V "," J_V "," J_V ")")},
        {"UndirectedGraphs", "ConnectedComponents", 1, connected_components,
         OVERRIDE("UndirectedGraphs", "connectedComponents(" J_V ")")},
    };
    for (size_t i = 0; i < sizeof natives / sizeof *natives; i++)
        if (manyan_define(natives[i].module, natives[i].name, natives[i].arity, natives[i].fn, natives[i].java)) return -1;
    if (manyan_module("__apalache_folds", apalache_folds) || manyan_module("__apalache_internal", apalache_internal)) return -1;
    return manyan_module("Apalache", apalache);
}
