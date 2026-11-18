/* The executable, checking what it found (ManyanOptions.result) against
   what it printed: the first counterexample's states, actions and loop,
   the names it gives as violated, and the counts it reports last. It
   prints what the executable does; a mismatch it tells on standard error,
   with exit status 99. The engine of `make test-result`. */
#define main manyan_main
#include "../manyan.c"
#undef main

static int saved_fd, out_fd, bad;
static pid_t parent;

static void mismatch(const char *fmt, ...) {
    va_list ap;
    va_start(ap, fmt);
    fputs("result: ", stderr);
    vfprintf(stderr, fmt, ap);
    fputs("\n", stderr);
    va_end(ap);
    bad = 1;
}

/* The first line at or after from that begins with prefix, before end; NULL if none. */
static const char *line_at(const char *text, const char *from, const char *end, const char *prefix) {
    for (const char *p = from; p && *p && (!end || p < end); p = strchr(p, '\n'), p = p ? p + 1 : NULL)
        if ((p == text || p[-1] == '\n') && !strncmp(p, prefix, strlen(prefix))) return p;
    return NULL;
}

static const char *action_name(ManyanValue *action) {
    return manyan_string_value(manyan_field(action, "name"), NULL);
}

/* The step at p, "<Name ...", is the action's. */
static void check_action(const char *p, ManyanValue *action, size_t i) {
    const char *name = action_name(action);
    if (*p != '<' || strncmp(p + 1, name, strlen(name)))
        mismatch("the step into state %zu is %s, but %.40s is printed", i + 1, name, p);
}

static void check_states(const char *t, const ManyanResult *r) {
    const char *first = line_at(t, t, NULL, "State 1: ");
    if (!r->length) {   /* none, or one cut short by an error rebuilding it */
        if (first && !line_at(t, first, NULL, "Error: ")) mismatch("no counterexample, but one is printed");
        return;
    }
    const char *initial = strstr(t, " is violated by the initial state:\n");
    if (initial && (!first || initial < first)) first = NULL;   /* printed as no State 1 */
    if (!first && r->length > 1) { mismatch("%zu states, but none is printed", r->length); return; }
    const char *p = first ? first : initial ? initial : t, *end = first ? line_at(t, strchr(first, '\n'), NULL, "State 1: ") : NULL;
    for (size_t i = 0; i < r->length; i++) {
        if (first) {
            char head[32];
            snprintf(head, sizeof head, "State %zu: ", i + 1);
            const char *h = line_at(t, p, end, head);
            if (!h) { mismatch("state %zu of %zu is not printed", i + 1, r->length); return; }
            check_action(h + strlen(head), r->actions[i], i);
            p = h;
        }
        if (alias_name || view_trace || diff_trace) continue;   /* printed as other values */
        Value **st = NEWN(Value *, nvars);
        for (int v = 0; v < nvars; v++) st[v] = manyan_field(r->states[i], S(vars[v]->name));
        Buf b = {0};
        state_text(&b, st);
        const char *q = strstr(p, b.s ? b.s : "");
        if (!q || (end && q >= end)) mismatch("state %zu is not printed as\n%s", i + 1, b.s);
        else p = q + b.n;
        free(b.s);
    }
    char stutter[48];
    snprintf(stutter, sizeof stutter, "State %zu: Stuttering", r->length + 1);
    const char *s = first ? line_at(t, p, end, stutter) : NULL, *back = first ? line_at(t, p, end, "Back to state ") : NULL;
    if (s && r->loop != r->length) mismatch("the last state stutters, but the loop is to %zu", r->loop);
    else if (back && (size_t)atol(back + 14) != r->loop) mismatch("%.20s, but the loop is to %zu", back, r->loop);
    else if (back) check_action(strchr(back, ':') + 2, r->actions[r->length], r->length);
    else if (!s && r->loop) mismatch("a loop to %zu, but none is printed", r->loop);
}

/* The first violation or deadlock printed names what the result does as violated. */
static void check_violated(const char *t, const ManyanResult *r) {
    const char *e = NULL;
    for (const char *p = t; !e && (p = line_at(t, p, NULL, "Error: ")); p++)
        if ((strstr(p, " violated") && strstr(p, " violated") < strchr(p, '\n')) || !strncmp(p, "Error: Deadlock reached.", 24)) e = p;
    size_t n = 0;
    for (; r->violated[n]; n++)
        if (!e || !strstr(e, r->violated[n]) || strstr(e, r->violated[n]) > strchr(e, '\n'))
            mismatch("%s is violated, but not printed so", r->violated[n]);
    if (e && !n && strncmp(e, "Error: Temporal properties were violated.", 41) && strncmp(e, "Error: Deadlock reached.", 24))
        mismatch("nothing is violated, but %.60s", e);
}

static void check_counts(const char *t, const ManyanResult *r) {
    long long g = -1, d = -1, l = -1, depth = -1;
    const char *search = NULL, *sim = NULL;
    for (const char *p = t; (p = strstr(p, " states generated, ")); p++) search = p;
    for (const char *p = t; (p = line_at(t, p, NULL, "The number of states generated: ")); p++) sim = p;
    if (search && (!sim || search > sim)) {
        while (search > t && search[-1] != '\n') search--;
        sscanf(search, "%lld states generated, %lld distinct states found, %lld states left on queue.\n"
                       "The depth of the complete state graph search is %lld.", &g, &d, &l, &depth);
    } else if (sim) sscanf(sim, "The number of states generated: %lld", &g);
    if (g != r->generated || d != r->distinct || l != r->left || depth != r->depth)
        mismatch("counts %lld %lld %lld %lld, but %lld %lld %lld %lld are printed",
                 (long long)r->generated, (long long)r->distinct, (long long)r->left, (long long)r->depth, g, d, l, depth);
}

static void check_result(void) {
    if (getpid() != parent) return;   /* a process the check started */
    fflush(stdout);
    Buf t = {0};
    char chunk[65536];
    ssize_t k;
    lseek(out_fd, 0, SEEK_SET);
    while ((k = read(out_fd, chunk, sizeof chunk)) > 0) buf_add(&t, chunk, (size_t)k);
    for (size_t w = 0; w < t.n; ) {
        ssize_t n = write(saved_fd, t.s + w, t.n - w);
        if (n <= 0) break;
        w += (size_t)n;
    }
    const char *text = t.s ? t.s : "";
    if (!main_result.violated) return;   /* no check began */
    check_states(text, &main_result);
    check_violated(text, &main_result);
    check_counts(text, &main_result);
    if (bad) _exit(99);
}

int main(int argc, char **argv) {
    parent = getpid();
    FILE *out = tmpfile();
    if (!out || (saved_fd = dup(1)) < 0) { perror("result"); return MANYAN_ERROR; }
    out_fd = fileno(out);
    dup2(out_fd, 1);
    atexit(check_result);
    return manyan_main(argc, argv);
}
