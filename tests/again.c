/* The executable, checking twice in one process: the first check's output
   is discarded, its files written in a copy of the directory, and the
   second, given the same standard input, prints what a first would. Between them,
   every global of the program is as it started, but for what manyan_define
   and manyan_module registered; one that is not is told on standard error,
   with exit status 98. The engine of `make test-again`. */
#define main manyan_main
#include "../manyan.c"
#undef main

#ifdef __APPLE__
#include <mach-o/getsect.h>
#include <mach-o/ldsyms.h>
#include <mach-o/dyld.h>
#endif

typedef struct { uint8_t *p; size_t n; } Range;

/* The program's writable globals. */
static int globals(Range *r) {
#ifdef __APPLE__
    const char *names[] = {"__data", "__bss", "__common"};
    int n = 0;
    for (int i = 0; i < 3; i++) {
        unsigned long size;
        uint8_t *p = getsectiondata(&_mh_execute_header, "__DATA", names[i], &size);
        if (p) r[n].p = p, r[n++].n = size;
    }
    return n;
#else
    extern char __data_start[], _end[];
    r[0].p = (uint8_t *)__data_start, r[0].n = (size_t)(_end - __data_start);
    return 1;
#endif
}

/* Whether p is in what a check keeps: the registrations, the result the
   executable writes, and stdio's. */
static int registered(const uint8_t *p) {
    const struct { const void *p; size_t n; } k[] = {
        {&library, sizeof library}, {&nlibrary, sizeof nlibrary}, {&defined, sizeof defined}, {&ndefined, sizeof ndefined},
        {&main_result, sizeof main_result}, {&result_file, sizeof result_file},
        {&stdout, sizeof stdout}, {&stderr, sizeof stderr}, {&stdin, sizeof stdin}};
    for (size_t i = 0; i < sizeof k / sizeof *k; i++)
        if (p >= (const uint8_t *)k[i].p && p < (const uint8_t *)k[i].p + k[i].n) return 1;
    return 0;
}

int main(int argc, char **argv) {
    if (manyan_std_init()) return MANYAN_ERROR;
    Range r[3];
    int n = globals(r);
    uint8_t *start[3];
    for (int i = 0; i < n; i++) start[i] = memcpy(malloc(r[i].n), r[i].p, r[i].n);
    char chunk[65536], dir[] = "/tmp/manyan-again-XXXXXX", here[4096], copy[4200], input[4200];
    snprintf(input, sizeof input, "%s.in", mkdtemp(dir));
    FILE *in = fopen(input, "w");
    for (size_t k; (k = fread(chunk, 1, sizeof chunk, stdin)) > 0; ) fwrite(chunk, 1, k, in);
    fclose(in);
    snprintf(copy, sizeof copy, "cp -R . %s", dir);
    if (!getcwd(here, sizeof here) || system(copy) || chdir(dir)) return MANYAN_ERROR;
    if (!freopen(input, "r", stdin)) return MANYAN_ERROR;
    fflush(stdout);
    int out = dup(1), null = open("/dev/null", O_WRONLY);
    dup2(null, 1);
    char **args = malloc(sizeof(char *) * (size_t)(argc + 1));   /* main's strtok cuts its arguments */
    for (int i = 0; i <= argc; i++) args[i] = argv[i] ? strdup(argv[i]) : NULL;
    manyan_main(argc, args);
    fflush(stdout);
    dup2(out, 1);
    if (chdir(here)) return MANYAN_ERROR;
    snprintf(copy, sizeof copy, "rm -rf %s", dir);
    if (system(copy) || !freopen(input, "r", stdin)) return MANYAN_ERROR;
    remove(input);
    reset_check();
    int bad = 0;
    for (int i = 0; i < n; i++)
        for (size_t j = 0; j < r[i].n; j++)
            if (r[i].p[j] != start[i][j] && !registered(r[i].p + j)) {
#ifdef __APPLE__
                fprintf(stderr, "again: the global at %#lx is not reset\n", (unsigned long)(r[i].p + j - _dyld_get_image_vmaddr_slide(0)));
#else
                fprintf(stderr, "again: the global at %p is not reset\n", (void *)(r[i].p + j));
#endif
                bad = 1;
                while (j + 1 < r[i].n && r[i].p[j + 1] != start[i][j + 1]) j++;
            }
    if (bad) return 98;
    return manyan_main(argc, argv);
}
