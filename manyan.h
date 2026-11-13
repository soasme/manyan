/* manyan: a TLA+ model checker. See docs/manual.md. */
#ifndef MANYAN_H
#define MANYAN_H

#include <stddef.h>
#include <stdint.h>

#define MANYAN_VERSION "0.11.0"

/* Exit statuses, as TLC reports them (docs/standards/tla2.md, 11.3). */
enum {
    MANYAN_OK = 0,
    MANYAN_VIOLATION_ASSUMPTION = 10,
    MANYAN_VIOLATION_DEADLOCK = 11,
    MANYAN_VIOLATION_SAFETY = 12,
    MANYAN_VIOLATION_LIVENESS = 13,
    MANYAN_VIOLATION_ASSERT = 14,
    MANYAN_FAILURE_EVAL = 75,
    MANYAN_FAILURE_SAFETY_EVAL = 76,
    MANYAN_FAILURE_LIVENESS_EVAL = 77,
    MANYAN_ERROR_PARSE = 150,
    MANYAN_ERROR_CONFIG = 151,
    MANYAN_ERROR = 255
};

typedef struct {
    const char *spec;    /* path of the root module, with or without .tla */
    const char *config;  /* path of the model configuration; NULL for SPEC.cfg */
    int check_deadlock;  /* 0 turns deadlock checking off, as -deadlock does */
    const char *dump;    /* write the state graph in dot format to this file, or NULL */
    int dump_actions;    /* label the dump's steps with their actions (-dump dot,actionlabels) */
    int nowarning;       /* TLC's warnings off, as -nowarning */
    int difftrace;       /* print only what each step of a trace changes, as -difftrace */
    int view;            /* a trace shows each state as the VIEW's value, as -view */
    int keep_going;      /* report each violated invariant and action property, and go on (-continue) */
    int stack;           /* expressions nest and calls go at most this deep, then TLC's StackOverflowError; 0 for calls 5000 deep (-stack) */
    const char *user_file;   /* write Print's output to this file instead, or NULL (-userFile) */
    int workers;         /* processes expanding states; 0 or 1 for one */
    int simulate;        /* random behaviors instead of the state graph, as -simulate */
    int generate;        /* simulation: each successor built by random choices, as -generate */
    long traces;         /* simulation: behaviors to make, 0 for no end (-simulate num=N) */
    long depth;          /* simulation: states in a behavior, 0 for 100 (-depth) */
    long long seed;      /* the seed, when seed_given (-seed): a simulation's, and model checking's for RandomElement */
    int seed_given;
    long long aril;      /* simulation: draws to skip after seeding (-aril) */
    const char *trace_file;  /* simulation: write behavior N to FILE_0_N, or NULL (-simulate file=FILE) */
    const char *const *properties;  /* Java system properties, "k=v" each, NULL-terminated (-Dk=v) */
    int symbolic;        /* check behaviors of up to length steps with a solver, as Apalache does (-symbolic) */
    long length;         /* symbolic checking: the steps in a behavior, 0 for 10 (-length) */
    const char *cinit;   /* symbolic checking: the operator that chooses the constants the configuration leaves, as Apalache's --cinit (-cinit) */
    long max_error;      /* symbolic checking: the invariant violations to find, 0 for 1, which the configuration's VIEW tells apart, as Apalache's --max-error (-max-error) */
    const char *run_dir; /* symbolic checking: the directory each counterexample is written to in ITF, as Apalache's --run-dir (-run-dir) */
    int typecheck;       /* type the specification as Apalache's type checker does, and check nothing else (-typecheck) */
} ManyanOptions;

/* Check the model and print TLC's report to standard output. Returns an
   exit status. */
int manyan_check(const ManyanOptions *options);

/* == Native operators ==
   TLC computes some operators of its modules in Java instead of from
   their definitions. A native operator is that Java in C: manyan_define
   binds it to the operator NAME of every module named MODULE that a spec
   loads, by name, as TLC binds its Java, and only when the definition
   takes ARITY arguments. JAVA is the method as TLC names it in an error
   in it. ARITY MANYAN_LAZY makes it take its arguments unevaluated, as TLC's
   evaluation methods do, with manyan_arg; it may then give NULL, which
   leaves the call to the definition. manyan-std.c defines TLC's own modules
   and CommunityModules' with these (docs/std.md). Define before
   manyan_check; returns 0, or -1 when out of memory. */
typedef struct ManyanValue ManyanValue;
typedef struct ManyanCall ManyanCall;   /* the call being evaluated */
typedef ManyanValue *(*ManyanNative)(ManyanCall *call, ManyanValue **args);
#define MANYAN_LAZY (-1)
int manyan_define(const char *module, const char *name, int arity, ManyanNative fn, const char *java);

/* == Modules ==
   manyan_module gives the text of the module NAME, which a spec loads when
   no file beside it has that name, as TLC loads one from its class path.
   manyan-std.c gives Apalache's (docs/std.md). Give before manyan_check;
   returns 0, or -1 when out of memory. */
int manyan_module(const char *name, const char *text);

/* Values live until the evaluation that made them ends; a native's
   arguments, as they are given, and what it makes. Sets and functions are
   given in TLC's order: sorted. */
typedef enum { MANYAN_BOOL, MANYAN_INT, MANYAN_STRING, MANYAN_MODEL, MANYAN_TUPLE, MANYAN_FUNCTION, MANYAN_SET, MANYAN_OTHER } ManyanKind;
ManyanKind manyan_kind(ManyanValue *);   /* a record is a function, from strings; a tuple a function on 1..n */
ManyanValue *manyan_bool(int);
ManyanValue *manyan_int(int64_t);
ManyanValue *manyan_string(const char *, size_t);
ManyanValue *manyan_tuple(size_t n, ManyanValue *const *elems);
ManyanValue *manyan_function(size_t n, ManyanValue *const *keys, ManyanValue *const *values);   /* keys distinct, any order */
ManyanValue *manyan_record(size_t n, ManyanValue *const *names, ManyanValue *const *values);   /* names strings, as manyan_function's keys */
ManyanValue *manyan_set(size_t n, ManyanValue *const *elems);   /* any order, duplicates too */
int manyan_is_true(ManyanValue *);
int64_t manyan_int_value(ManyanValue *);
const char *manyan_string_value(ManyanValue *, size_t *len);
/* A tuple's or function's size, keys and values; a set's elements, which
   manyan_elements gives it. */
size_t manyan_size(ManyanValue *);
ManyanValue *manyan_key(ManyanValue *, size_t);
ManyanValue *manyan_value(ManyanValue *, size_t);
ManyanValue *manyan_field(ManyanValue *record, const char *name);   /* NULL when it has none */
ManyanValue *manyan_elements(ManyanValue *set);   /* enumerated, as TLC's toSetEnum; NULL for a set it cannot enumerate, or another value */
ManyanValue *manyan_element(ManyanValue *elements, size_t);
int manyan_compare(ManyanValue *, ManyanValue *);   /* TLC's order of values: <0, 0 or >0 */
const char *manyan_print(ManyanValue *);         /* as TLC prints it */
const char *manyan_to_string(ManyanValue *);     /* as TLC's toString gives it: on one line */
const char *manyan_class(ManyanValue *);         /* the Java class TLC keeps it in, as "IntValue" */
size_t manyan_kept(ManyanValue *record, size_t i);   /* the index of field i as TLC's Java sees a record it has not normalized: as written */
void *manyan_alloc(size_t);   /* zeroed memory that lives as values do: never freed, so a failing native loses none */
/* Java's String.format(fmt, args...), each arg a string; its exception
   the native's, as manyan_throw. */
ManyanValue *manyan_format(ManyanCall *, const char *fmt, size_t n, const char *const *args);
ManyanValue *manyan_arg(ManyanCall *, int i);       /* a MANYAN_LAZY native's argument i, evaluated */
/* An error in the native: manyan_fail one TLC reports as its own, as an
   EvalException; manyan_throw another exception of its Java, which TLC
   reports with the method that threw it. */
#if defined(__GNUC__)
__attribute__((noreturn, format(printf, 2, 3)))
#endif
void manyan_fail(ManyanCall *, const char *fmt, ...);
#if defined(__GNUC__)
__attribute__((noreturn, format(printf, 2, 3)))
#endif
void manyan_throw(ManyanCall *, const char *fmt, ...);

#endif
