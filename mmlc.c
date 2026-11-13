/*
 * mmlc - 汎用 SFC(SNES) SPC 用 MML コンパイラ
 *
 *   ドライバ固有のバイト列表現は全て「ドライバ定義ファイル(.drv)」に記述する。
 *   コンパイラ本体はドライバに依存しない。
 *
 * build : cc -O2 -Wall -o mmlc mmlc.c
 * usage : mmlc [-d driver.drv] [-o out.spc] [-v] song.mml
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>
#include <stdarg.h>
#include <stdint.h>
#include <time.h>

#define MAXCH   16
#define RAMSZ   0x10000
#define SPCSZ   0x10200

/* ------------------------------------------------------------------ */
/* utility                                                             */
/* ------------------------------------------------------------------ */
static char g_where[1200];

static void die(const char *fmt, ...)
{
    va_list ap;
    fprintf(stderr, "error: ");
    if (g_where[0]) fprintf(stderr, "%s: ", g_where);
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
    exit(1);
}

static void warn(const char *fmt, ...)
{
    va_list ap;
    fprintf(stderr, "warning: ");
    if (g_where[0]) fprintf(stderr, "%s: ", g_where);
    va_start(ap, fmt);
    vfprintf(stderr, fmt, ap);
    va_end(ap);
    fputc('\n', stderr);
}

static void *xrealloc(void *p, size_t n)
{
    p = realloc(p, n);
    if (!p) die("out of memory");
    return p;
}

static char *xstrdup(const char *s)
{
    char *p = xrealloc(NULL, strlen(s) + 1);
    strcpy(p, s);
    return p;
}

static char *trim(char *s)
{
    char *e;
    while (isspace((unsigned char)*s)) s++;
    e = s + strlen(s);
    while (e > s && isspace((unsigned char)e[-1])) *--e = 0;
    return s;
}

static void unquote(char *s)
{
    size_t n = strlen(s);
    if (n >= 2 && (s[0] == '"' || s[0] == '\'') && s[n - 1] == s[0]) {
        memmove(s, s + 1, n - 2);
        s[n - 2] = 0;
    }
}

static long parse_number(const char *s)
{
    int neg = 0;
    long v;
    char *e;
    while (isspace((unsigned char)*s)) s++;
    if (*s == '-') { neg = 1; s++; } else if (*s == '+') s++;
    if (s[0] == '0' && (s[1] == 'x' || s[1] == 'X')) v = strtol(s + 2, &e, 16);
    else if (s[0] == '0' && (s[1] == 'b' || s[1] == 'B')) v = strtol(s + 2, &e, 2);
    else v = strtol(s, &e, 10);
    return neg ? -v : v;
}

static char *read_file(const char *path, long *len)
{
    FILE *f = fopen(path, "rb");
    char *buf;
    long n;
    if (!f) die("cannot open '%s'", path);
    fseek(f, 0, SEEK_END);
    n = ftell(f);
    fseek(f, 0, SEEK_SET);
    buf = xrealloc(NULL, n + 1);
    if (fread(buf, 1, n, f) != (size_t)n) die("read error '%s'", path);
    buf[n] = 0;
    fclose(f);
    if (len) *len = n;
    return buf;
}

static void dir_of(const char *path, char *dir, size_t n)
{
    const char *p = strrchr(path, '/');
    const char *q = strrchr(path, '\\');
    if (q > p) p = q;
    if (!p) { dir[0] = 0; return; }
    snprintf(dir, n, "%.*s", (int)(p - path + 1), path);
}

static void join_path(char *out, size_t n, const char *dir, const char *p)
{
    if (!dir[0] || p[0] == '/' || p[0] == '\\' ||
        (isalpha((unsigned char)p[0]) && p[1] == ':'))
        snprintf(out, n, "%s", p);
    else
        snprintf(out, n, "%s%s", dir, p);
}

static int floordiv(int a, int b)
{
    int q = a / b;
    if ((a % b) && ((a < 0) != (b < 0))) q--;
    return q;
}

/* ------------------------------------------------------------------ */
/* labels & expression evaluator                                       */
/* ------------------------------------------------------------------ */
typedef struct { char name[48]; long val; } Label;
static Label labels[1024];
static int nlabels;

static void set_label(const char *n, long v)
{
    int i;
    for (i = 0; i < nlabels; i++)
        if (!strcmp(labels[i].name, n)) { labels[i].val = v; return; }
    if (nlabels >= 1024) die("too many labels");
    snprintf(labels[nlabels].name, sizeof labels[0].name, "%s", n);
    labels[nlabels++].val = v;
}

static int get_label(const char *n, long *v)
{
    int i;
    for (i = 0; i < nlabels; i++)
        if (!strcmp(labels[i].name, n)) { *v = labels[i].val; return 1; }
    return 0;
}

typedef struct { char name[16]; long val; } Var;
typedef struct { Var v[16]; int n; } Vars;

static void vinit(Vars *v) { v->n = 0; }
static void vset(Vars *v, const char *name, long val)
{
    int i;
    for (i = 0; i < v->n; i++)
        if (!strcmp(v->v[i].name, name)) { v->v[i].val = val; return; }
    if (v->n >= 16) die("too many variables");
    snprintf(v->v[v->n].name, 16, "%s", name);
    v->v[v->n++].val = val;
}

static const char *ep;
static Vars *evars;
static long e_bor(void);

static void e_ws(void) { while (isspace((unsigned char)*ep)) ep++; }

static void e_ident(char *buf, int cap)
{
    int n = 0;
    while (isalnum((unsigned char)*ep) || *ep == '_') {
        if (n < cap - 1) buf[n++] = *ep;
        ep++;
    }
    buf[n] = 0;
}

static long e_prim(void)
{
    long v;
    e_ws();
    if (*ep == '(') {
        ep++;
        v = e_bor();
        e_ws();
        if (*ep != ')') die("')' expected in expression");
        ep++;
        return v;
    }
    if (*ep == '$') {
        char id[48];
        int i;
        ep++;
        e_ident(id, sizeof id);
        for (i = 0; evars && i < evars->n; i++)
            if (!strcmp(evars->v[i].name, id)) return evars->v[i].val;
        die("unknown variable '$%s'", id);
    }
    if (*ep == '@') {
        char id[48];
        ep++;
        e_ident(id, sizeof id);
        if (!get_label(id, &v)) die("undefined label '@%s'", id);
        return v;
    }
    if (isdigit((unsigned char)*ep)) {
        char *e;
        if (ep[0] == '0' && (ep[1] == 'x' || ep[1] == 'X')) v = strtol(ep + 2, &e, 16);
        else if (ep[0] == '0' && (ep[1] == 'b' || ep[1] == 'B')) v = strtol(ep + 2, &e, 2);
        else v = strtol(ep, &e, 10);
        ep = e;
        return v;
    }
    die("bad expression near '%s'", ep);
    return 0;
}

static long e_un(void)
{
    e_ws();
    if (*ep == '-') { ep++; return -e_un(); }
    if (*ep == '+') { ep++; return e_un(); }
    if (*ep == '~') { ep++; return ~e_un(); }
    return e_prim();
}

static long e_mul(void)
{
    long a = e_un(), b;
    for (;;) {
        e_ws();
        if (*ep == '*') { ep++; a *= e_un(); }
        else if (*ep == '/') { ep++; b = e_un(); if (!b) die("division by zero"); a /= b; }
        else if (*ep == '%') { ep++; b = e_un(); if (!b) die("division by zero"); a %= b; }
        else return a;
    }
}

static long e_add(void)
{
    long a = e_mul();
    for (;;) {
        e_ws();
        if (*ep == '+') { ep++; a += e_mul(); }
        else if (*ep == '-') { ep++; a -= e_mul(); }
        else return a;
    }
}

static long e_shift(void)
{
    long a = e_add();
    for (;;) {
        e_ws();
        if (ep[0] == '<' && ep[1] == '<') { ep += 2; a <<= e_add(); }
        else if (ep[0] == '>' && ep[1] == '>') { ep += 2; a >>= e_add(); }
        else return a;
    }
}

static long e_band(void)
{
    long a = e_shift();
    for (;;) {
        e_ws();
        if (*ep == '&') { ep++; a &= e_shift(); } else return a;
    }
}

static long e_bxor(void)
{
    long a = e_band();
    for (;;) {
        e_ws();
        if (*ep == '^') { ep++; a ^= e_band(); } else return a;
    }
}

static long e_bor(void)
{
    long a = e_bxor();
    for (;;) {
        e_ws();
        if (*ep == '|') { ep++; a |= e_bxor(); } else return a;
    }
}

static long eval_str(const char *s, Vars *v)
{
    long r;
    ep = s;
    evars = v;
    r = e_bor();
    e_ws();
    if (*ep) die("unexpected '%s' in expression '%s'", ep, s);
    return r;
}

/* ------------------------------------------------------------------ */
/* driver definition (INI-like) storage                                */
/* ------------------------------------------------------------------ */
typedef struct { char sec[24], key[48]; char *val; } Ent;
static Ent *ents;
static int nents, capents;
static char drv_dir[512];

static void cfg_add(const char *sec, const char *key, const char *val)
{
    if (nents >= capents) {
        capents = capents ? capents * 2 : 64;
        ents = xrealloc(ents, capents * sizeof *ents);
    }
    snprintf(ents[nents].sec, sizeof ents[0].sec, "%s", sec);
    snprintf(ents[nents].key, sizeof ents[0].key, "%s", key);
    ents[nents].val = xstrdup(val);
    nents++;
}

static const char *cfg_get(const char *sec, const char *key)
{
    int i;
    for (i = 0; i < nents; i++)
        if (!strcmp(ents[i].sec, sec) && !strcmp(ents[i].key, key)) return ents[i].val;
    return NULL;
}

static long cfg_int(const char *sec, const char *key, long def)
{
    const char *v = cfg_get(sec, key);
    return v ? parse_number(v) : def;
}

static void load_driver(const char *path)
{
    FILE *f = fopen(path, "r");
    char line[2048], sec[24] = "";
    int ln = 0;
    if (!f) die("cannot open driver definition '%s'", path);
    dir_of(path, drv_dir, sizeof drv_dir);
    while (fgets(line, sizeof line, f)) {
        char *p, *c;
        ln++;
        snprintf(g_where, sizeof g_where, "%s:%d", path, ln);
        if ((c = strchr(line, ';')) != NULL) *c = 0;
        p = trim(line);
        if (!*p) continue;
        if (*p == '[') {
            char *q = strchr(p, ']');
            int i;
            if (!q) die("']' expected");
            *q = 0;
            snprintf(sec, sizeof sec, "%s", trim(p + 1));
            for (i = 0; sec[i]; i++) sec[i] = tolower((unsigned char)sec[i]);
            continue;
        }
        if (!strcmp(sec, "layout")) {
            char *sp = p;
            while (*sp && !isspace((unsigned char)*sp)) sp++;
            if (*sp) *sp++ = 0;
            cfg_add(sec, p, trim(sp));
        } else {
            char *eq = strchr(p, '=');
            char *k, *v;
            int i;
            if (!eq) die("'key = value' expected");
            *eq = 0;
            k = trim(p);
            v = trim(eq + 1);
            for (i = 0; k[i]; i++) k[i] = tolower((unsigned char)k[i]);
            cfg_add(sec, k, v);
        }
    }
    g_where[0] = 0;
    fclose(f);
}

/* ------------------------------------------------------------------ */
/* driver parameters                                                   */
/* ------------------------------------------------------------------ */
enum { CMD_TEMPO, CMD_INSTR, CMD_VOL, CMD_PAN, CMD_GATE, CMD_VEL, NCMD };
static const char *cmd_name[NCMD] = {
    "tempo", "instrument", "volume", "pan", "gate", "velocity"
};

static struct {
    int tpq, oct_base, oct_default, oct_init;
    int len_max, len_min, lt[64], nlen;
    int loop_native, channels, unused_ptr;
    int def_gate, def_vel;
    int have_prange, pmin, pmax;
    int oct_cmd;
    long base, limit;
    const char *t_state, *t_note, *t_rest, *t_tie;
    const char *t_oct, *t_oct_up, *t_oct_dn;
    const char *t_lbegin, *t_lend, *t_lpoint, *t_lforever, *t_tstart, *t_tend;
    const char *t_cmd[NCMD];
} D;

static void init_driver(void)
{
    const char *s;
    int i;
    D.tpq = cfg_int("notes", "tpq", 48);
    D.oct_base = cfg_int("notes", "octave_base", 0);
    D.oct_default = cfg_int("notes", "octave_default", 4);
    D.oct_init = cfg_int("notes", "octave_init", D.oct_default);
    D.len_max = cfg_int("notes", "len_max", 255);
    D.len_min = cfg_int("notes", "len_min", 1);
    D.def_gate = cfg_int("notes", "default_gate", 0);
    D.def_vel = cfg_int("notes", "default_velocity", 0);
    if (cfg_get("notes", "pitch_min") || cfg_get("notes", "pitch_max")) {
        D.have_prange = 1;
        D.pmin = cfg_int("notes", "pitch_min", -9999);
        D.pmax = cfg_int("notes", "pitch_max", 9999);
    }
    if ((s = cfg_get("notes", "len_table")) != NULL) {
        char *c = xstrdup(s), *p = c;
        while (*p) {
            while (isspace((unsigned char)*p)) p++;
            if (!*p) break;
            if (D.nlen >= 64) die("len_table too long");
            D.lt[D.nlen++] = (int)parse_number(p);
            while (*p && !isspace((unsigned char)*p)) p++;
        }
        free(c);
    }
    s = cfg_get("notes", "loop_mode");
    D.loop_native = s && !strcmp(s, "native");
    D.channels = cfg_int("song", "channels", 8);
    if (D.channels < 1 || D.channels > MAXCH) die("channels must be 1..%d", MAXCH);
    D.unused_ptr = cfg_int("song", "unused_ptr", 0);
    D.base = cfg_int("song", "base", 0x2000);
    D.limit = cfg_int("song", "limit", 0xFFBF);

    D.t_state = cfg_get("commands", "state");
    D.t_note = cfg_get("commands", "note");
    D.t_rest = cfg_get("commands", "rest");
    D.t_tie = cfg_get("commands", "tie");
    D.t_oct = cfg_get("commands", "octave");
    D.t_oct_up = cfg_get("commands", "octave_up");
    D.t_oct_dn = cfg_get("commands", "octave_down");
    D.oct_cmd = D.t_oct || D.t_oct_up || D.t_oct_dn;
    D.t_lbegin = cfg_get("commands", "loop_begin");
    D.t_lend = cfg_get("commands", "loop_end");
    D.t_lpoint = cfg_get("commands", "loop_point");
    D.t_lforever = cfg_get("commands", "loop_forever");
    D.t_tstart = cfg_get("commands", "track_start");
    D.t_tend = cfg_get("commands", "track_end");
    for (i = 0; i < NCMD; i++) D.t_cmd[i] = cfg_get("commands", cmd_name[i]);
}

/* ------------------------------------------------------------------ */
/* template tokens  ("0xE7 $1*2 @label:w")                             */
/* ------------------------------------------------------------------ */
static int next_tok(const char **pp, char *out, int cap)
{
    const char *p = *pp;
    int n = 0;
    while (isspace((unsigned char)*p)) p++;
    if (!*p) return 0;
    while (*p && !isspace((unsigned char)*p)) {
        if (n < cap - 1) out[n++] = *p;
        p++;
    }
    out[n] = 0;
    *pp = p;
    return 1;
}

/* strip ':w' etc, return byte size */
static int tok_split(char *tok, int *be)
{
    int size = 1;
    char *c = strrchr(tok, ':');
    *be = 0;
    if (c) {
        switch (c[1]) {
        case 'b': size = 1; break;
        case 'w': size = 2; break;
        case 'W': size = 2; *be = 1; break;
        case 'l': size = 3; break;
        case 'L': size = 3; *be = 1; break;
        default: die("bad size suffix in '%s' (use :b :w :W :l :L)", tok);
        }
        if (c[2]) die("bad size suffix in '%s'", tok);
        *c = 0;
    }
    return size;
}

static int tokens_size(const char *tpl)
{
    char tok[160];
    const char *p = tpl;
    int total = 0, be;
    while (next_tok(&p, tok, sizeof tok)) total += tok_split(tok, &be);
    return total;
}

static int encode_tokens(const char *tpl, Vars *v, long here, uint8_t *out, int cap)
{
    char tok[160];
    const char *p = tpl;
    int total = tokens_size(tpl), pos = 0;
    if (total > cap) die("template too long: '%s'", tpl);
    set_label("here", here);
    set_label("next", here + total);
    while (next_tok(&p, tok, sizeof tok)) {
        int be, sz = tok_split(tok, &be), k;
        long val = eval_str(tok, v);
        long lo = -(1L << (8 * sz - 1)), hi = (1L << (8 * sz)) - 1;
        if (val < lo || val > hi)
            die("value %ld out of range for %d-byte field in '%s'", val, sz, tpl);
        for (k = 0; k < sz; k++)
            out[pos++] = (val >> (8 * (be ? sz - 1 - k : k))) & 0xFF;
    }
    return pos;
}

/* ------------------------------------------------------------------ */
/* song buffer / fixups                                                */
/* ------------------------------------------------------------------ */
static uint8_t song[0x10000];
static int song_len;

static long cur_addr(void) { return D.base + song_len; }

static void put_byte(int b)
{
    if (song_len >= 0x10000) die("song data too large");
    song[song_len++] = (uint8_t)b;
}

static void emit_now(const char *tpl, Vars *v)
{
    uint8_t buf[256];
    int n, i;
    if (!tpl) return;
    n = encode_tokens(tpl, v, cur_addr(), buf, sizeof buf);
    for (i = 0; i < n; i++) put_byte(buf[i]);
}

typedef struct { int off; char tpl[512]; long here; } Fixup;
static Fixup *fixups;
static int nfix, capfix;

static void fix_add(const char *tpl)
{
    int n = tokens_size(tpl), i;
    if (nfix >= capfix) {
        capfix = capfix ? capfix * 2 : 64;
        fixups = xrealloc(fixups, capfix * sizeof *fixups);
    }
    if (strlen(tpl) >= sizeof fixups[0].tpl) die("layout line too long");
    strcpy(fixups[nfix].tpl, tpl);
    fixups[nfix].off = song_len;
    fixups[nfix].here = cur_addr();
    nfix++;
    for (i = 0; i < n; i++) put_byte(0);
}

static void fix_resolve(void)
{
    int i;
    Vars v;
    vinit(&v);
    for (i = 0; i < nfix; i++) {
        uint8_t buf[256];
        int n = encode_tokens(fixups[i].tpl, &v, fixups[i].here, buf, sizeof buf);
        memcpy(song + fixups[i].off, buf, n);
    }
}

/* ------------------------------------------------------------------ */
/* MML parsing                                                         */
/* ------------------------------------------------------------------ */
enum { EV_NOTE, EV_REST, EV_CMD, EV_LBEGIN, EV_LEND, EV_LPOINT };
typedef struct { int type, pitch, len, cmd, arg, match, line; } Ev;

typedef struct {
    Ev *ev;
    int n, cap;
    int used;
    int oct, deflen, depth;
    int stack[32];
} Track;
static Track tracks[MAXCH];

static void ev_push(Track *t, Ev e)
{
    if (t->n >= t->cap) {
        t->cap = t->cap ? t->cap * 2 : 256;
        t->ev = xrealloc(t->ev, t->cap * sizeof(Ev));
    }
    t->ev[t->n++] = e;
}

static int parse_int(const char **ps)
{
    const char *s = *ps;
    int neg = 0, v = 0;
    if (*s == '-') { neg = 1; s++; }
    if (!isdigit((unsigned char)*s)) die("number expected");
    while (isdigit((unsigned char)*s)) v = v * 10 + (*s++ - '0');
    *ps = s;
    return neg ? -v : v;
}

/* length: "8", "4.", "%24", or default */
static int parse_len(const char **ps, int dflt, int need)
{
    const char *s = *ps;
    int ticks, add;
    if (*s == '%') {
        s++;
        ticks = parse_int(&s);
    } else if (isdigit((unsigned char)*s)) {
        int n = parse_int(&s);
        if (n <= 0 || (D.tpq * 4) % n)
            die("length 1/%d is not an integer number of ticks (tpq=%d)", n, D.tpq);
        ticks = D.tpq * 4 / n;
    } else {
        if (need) die("length expected");
        ticks = dflt;
    }
    add = ticks;
    while (*s == '.') {
        if (add % 2) die("dotted length is not an integer number of ticks");
        add /= 2;
        ticks += add;
        s++;
    }
    if (ticks <= 0) die("length must be positive");
    *ps = s;
    return ticks;
}

static const int semi_tbl[7] = { 9, 11, 0, 2, 4, 5, 7 }; /* a b c d e f g */

static void parse_chunk(int ch, const char *s, int line)
{
    Track *t = &tracks[ch];
    snprintf(g_where, sizeof g_where, "line %d (track %c)", line, 'A' + ch);
    while (*s) {
        char c = *s++;
        Ev e;
        memset(&e, 0, sizeof e);
        e.line = line;
        if (isspace((unsigned char)c)) continue;
        if (c >= 'a' && c <= 'g') {
            int semi = semi_tbl[c - 'a'];
            for (;;) {
                if (*s == '+' || *s == '#') { semi++; s++; }
                else if (*s == '-') { semi--; s++; }
                else break;
            }
            e.type = EV_NOTE;
            e.pitch = t->oct * 12 + semi;
            e.len = parse_len(&s, t->deflen, 0);
            ev_push(t, e);
        } else if (c == 'r') {
            e.type = EV_REST;
            e.len = parse_len(&s, t->deflen, 0);
            ev_push(t, e);
        } else if (c == '^') {
            int l = parse_len(&s, t->deflen, 0);
            if (!t->n || (t->ev[t->n - 1].type != EV_NOTE && t->ev[t->n - 1].type != EV_REST))
                die("'^' must follow a note or rest");
            t->ev[t->n - 1].len += l;
        } else if (c == 'l') {
            t->deflen = parse_len(&s, 0, 1);
        } else if (c == 'o') {
            t->oct = parse_int(&s);
        } else if (c == '<') {
            t->oct--;
        } else if (c == '>') {
            t->oct++;
        } else if (c == '[') {
            if (t->depth >= 32) die("loops nested too deeply");
            e.type = EV_LBEGIN;
            t->stack[t->depth++] = t->n;
            ev_push(t, e);
        } else if (c == ']') {
            int b, cnt = 2;
            if (!t->depth) die("']' without '['");
            if (isdigit((unsigned char)*s)) cnt = parse_int(&s);
            if (cnt < 1) die("loop count must be >= 1");
            b = t->stack[--t->depth];
            e.type = EV_LEND;
            e.arg = cnt;
            e.match = b;
            t->ev[b].match = t->n;
            ev_push(t, e);
        } else if (c == 'L') {
            if (t->depth) die("'L' inside a loop");
            e.type = EV_LPOINT;
            ev_push(t, e);
        } else if (c == 't' || c == '@' || c == 'v' || c == 'p' || c == 'q' || c == 'u') {
            e.type = EV_CMD;
            e.cmd = c == 't' ? CMD_TEMPO : c == '@' ? CMD_INSTR : c == 'v' ? CMD_VOL :
                    c == 'p' ? CMD_PAN : c == 'q' ? CMD_GATE : CMD_VEL;
            e.arg = parse_int(&s);
            ev_push(t, e);
        } else {
            die("unknown command '%c'", c);
        }
    }
    g_where[0] = 0;
}

/* ------------------------------------------------------------------ */
/* track encoder                                                       */
/* ------------------------------------------------------------------ */
static struct {
    int len_last, gate_last, vel_last, oct_last;
    int gate, vel;
    long lstart[32], lbody[32];
    int ld, ch;
    int warned[NCMD];
} E;

static void inv_state(void)
{
    E.len_last = E.gate_last = E.vel_last = -1;
    if (D.t_oct) E.oct_last = -1000;
}

static int split_len(int len, int *out)
{
    int n = 0, rem = len, i;
    if (D.nlen) {
        while (rem > 0) {
            int best = 0;
            for (i = 0; i < D.nlen; i++)
                if (D.lt[i] <= rem && D.lt[i] > best) best = D.lt[i];
            if (!best) die("length %d cannot be expressed with the driver's len_table", len);
            if (n >= 64) die("length %d needs too many ties", len);
            out[n++] = best;
            rem -= best;
        }
    } else {
        while (rem > 0) {
            int c = rem > D.len_max ? D.len_max : rem;
            if (rem - c > 0 && rem - c < D.len_min) c = rem - D.len_min;
            if (c < D.len_min) die("length %d is shorter than the driver minimum (%d)", len, D.len_min);
            if (n >= 64) die("length %d needs too many ties", len);
            out[n++] = c;
            rem -= c;
        }
    }
    return n;
}

static int len_index(int c)
{
    int i;
    if (!D.nlen) return c;
    for (i = 0; i < D.nlen; i++) if (D.lt[i] == c) return i;
    return 0;
}

static void ensure_octave(int pitch)
{
    int target;
    Vars v;
    if (!D.oct_cmd) return;
    vinit(&v);
    target = floordiv(pitch, 12);
    if (target == E.oct_last) return;
    if (D.t_oct) {
        vset(&v, "1", target - D.oct_base);
        emit_now(D.t_oct, &v);
        E.oct_last = target;
    } else {
        while (E.oct_last < target) {
            if (!D.t_oct_up) die("driver has no 'octave_up' command");
            emit_now(D.t_oct_up, &v);
            E.oct_last++;
        }
        while (E.oct_last > target) {
            if (!D.t_oct_dn) die("driver has no 'octave_down' command");
            emit_now(D.t_oct_dn, &v);
            E.oct_last--;
        }
    }
}

/* kind: 0 note / 1 rest / 2 tie */
static void emit_unit(int kind, int pitch, int c)
{
    static const char *kn[3] = { "note", "rest", "tie" };
    const char *tpl = kind == 0 ? D.t_note : kind == 1 ? D.t_rest : D.t_tie;
    int oct = floordiv(pitch, 12), semi = pitch - oct * 12;
    Vars v;
    vinit(&v);
    vset(&v, "len", c);
    vset(&v, "lenidx", len_index(c));
    vset(&v, "gate", E.gate);
    vset(&v, "vel", E.vel);
    if (D.t_state && (c != E.len_last || E.gate != E.gate_last || E.vel != E.vel_last)) {
        emit_now(D.t_state, &v);
        E.len_last = c;
        E.gate_last = E.gate;
        E.vel_last = E.vel;
    }
    if (!tpl) die("driver defines no '%s' template", kn[kind]);
    vset(&v, "pitch", D.oct_cmd ? semi : pitch - D.oct_base * 12);
    vset(&v, "semi", semi);
    vset(&v, "oct", oct - D.oct_base);
    emit_now(tpl, &v);
}

static void encode_range(Track *t, int a, int b)
{
    int i;
    for (i = a; i < b; i++) {
        Ev *e = &t->ev[i];
        snprintf(g_where, sizeof g_where, "line %d (track %c)", e->line, 'A' + E.ch);
        switch (e->type) {
        case EV_NOTE:
        case EV_REST: {
            int ch[64], n = split_len(e->len, ch), k;
            if (e->type == EV_NOTE) {
                if (D.have_prange) {
                    int p = e->pitch - D.oct_base * 12;
                    if (p < D.pmin || p > D.pmax) die("note out of driver range");
                }
                ensure_octave(e->pitch);
            }
            for (k = 0; k < n; k++) {
                int kind = e->type == EV_NOTE ? (k ? 2 : 0) : 1;
                emit_unit(kind, e->pitch, ch[k]);
            }
            break;
        }
        case EV_CMD: {
            const char *tpl = D.t_cmd[e->cmd];
            if (tpl) {
                Vars v;
                vinit(&v);
                vset(&v, "1", e->arg);
                emit_now(tpl, &v);
            } else if (e->cmd == CMD_GATE) {
                E.gate = e->arg;
            } else if (e->cmd == CMD_VEL) {
                E.vel = e->arg;
            } else if (!E.warned[e->cmd]) {
                E.warned[e->cmd] = 1;
                warn("driver has no '%s' command; ignored", cmd_name[e->cmd]);
            }
            break;
        }
        case EV_LBEGIN: {
            int j = e->match, cnt = t->ev[j].arg, k;
            if (!D.loop_native) {
                for (k = 0; k < cnt; k++) encode_range(t, i + 1, j);
            } else {
                Vars v;
                if (cnt == 1) { encode_range(t, i + 1, j); }
                else {
                    if (E.ld >= 32) die("loops nested too deeply");
                    if (!D.t_lbegin || !D.t_lend)
                        die("loop_mode=native needs 'loop_begin' and 'loop_end'");
                    vinit(&v);
                    E.lstart[E.ld] = cur_addr();
                    set_label("loop", E.lstart[E.ld]);
                    emit_now(D.t_lbegin, &v);
                    E.lbody[E.ld] = cur_addr();
                    E.ld++;
                    inv_state();
                    encode_range(t, i + 1, j);
                    E.ld--;
                    set_label("loop", E.lstart[E.ld]);
                    set_label("loop_body", E.lbody[E.ld]);
                    vset(&v, "1", cnt);
                    vset(&v, "count", cnt);
                    snprintf(g_where, sizeof g_where, "line %d (track %c)", t->ev[j].line, 'A' + E.ch);
                    emit_now(D.t_lend, &v);
                }
            }
            i = j;
            break;
        }
        case EV_LEND:
            break;
        case EV_LPOINT: {
            char nm[48];
            Vars v;
            vinit(&v);
            snprintf(nm, sizeof nm, "track_%d_loop", E.ch);
            set_label(nm, cur_addr());
            set_label("loop_point", cur_addr());
            emit_now(D.t_lpoint, &v);
            inv_state();
            break;
        }
        }
    }
}

static int track_has_loop(Track *t)
{
    int i;
    for (i = 0; i < t->n; i++) if (t->ev[i].type == EV_LPOINT) return 1;
    return 0;
}

static void emit_track(int ch)
{
    Track *t = &tracks[ch];
    char nm[48];
    Vars v;
    long start = cur_addr();
    vinit(&v);
    if (!t->used) return;
    snprintf(nm, sizeof nm, "track_%d", ch);
    set_label(nm, start);
    snprintf(nm, sizeof nm, "track_%d_loop", ch);
    set_label(nm, start);
    memset(&E, 0, sizeof E);
    E.ch = ch;
    E.gate = D.def_gate;
    E.vel = D.def_vel;
    E.oct_last = D.t_oct ? -1000 : D.oct_init;
    inv_state();
    emit_now(D.t_tstart, &v);
    encode_range(t, 0, t->n);
    g_where[0] = 0;
    if (track_has_loop(t)) {
        if (!D.t_lforever) die("track %c uses 'L' but the driver defines no 'loop_forever'", 'A' + ch);
        emit_now(D.t_lforever, &v);
    } else {
        emit_now(D.t_tend, &v);
    }
    snprintf(nm, sizeof nm, "track_%d_end", ch);
    set_label(nm, cur_addr());
}

/* ------------------------------------------------------------------ */
/* layout                                                              */
/* ------------------------------------------------------------------ */
static char *bin_files[32];
static int nbins;
static char mml_dir[512];

/* MML 側から指定するサンプル(BRR等)と DSP 初期値 */
typedef struct { char *file; long addr; } Sample;
static Sample samples[64];
static int nsamples;
typedef struct { int reg; int val; } DspSet;
static DspSet dspsets[128];
static int ndspsets;

static void replace_ch(char *dst, size_t n, const char *src, int ch)
{
    size_t o = 0;
    while (*src && o + 8 < n) {
        if (!strncmp(src, "$ch", 3) && !isalnum((unsigned char)src[3])) {
            o += snprintf(dst + o, n - o, "%d", ch);
            src += 3;
        } else dst[o++] = *src++;
    }
    dst[o] = 0;
}

static void layout_line(const char *item, const char *args)
{
    int i;
    if (!strcmp(item, "label")) {
        set_label(args, cur_addr());
    } else if (!strcmp(item, "data")) {
        fix_add(args);
    } else if (!strcmp(item, "track")) {
        Vars v;
        vinit(&v);
        emit_track((int)eval_str(args, &v));
    } else if (!strcmp(item, "tracks")) {
        for (i = 0; i < D.channels; i++) emit_track(i);
    } else if (!strcmp(item, "foreach_track")) {
        char sub[512], item2[64], *sp;
        for (i = 0; i < D.channels; i++) {
            replace_ch(sub, sizeof sub, args, i);
            sp = sub;
            while (*sp && !isspace((unsigned char)*sp)) sp++;
            snprintf(item2, sizeof item2, "%.*s", (int)(sp - sub), sub);
            while (isspace((unsigned char)*sp)) sp++;
            layout_line(item2, sp);
        }
    } else if (!strcmp(item, "incbin") || !strcmp(item, "bins")) {
        int k;
        if (!strcmp(item, "incbin")) {
            char path[1024], *q = xstrdup(args);
            long n;
            char *d;
            unquote(q);
            join_path(path, sizeof path, drv_dir, q);
            d = read_file(path, &n);
            for (k = 0; k < n; k++) put_byte((uint8_t)d[k]);
            free(d);
            free(q);
        } else {
            for (i = 0; i < nbins; i++) {
                char path[1024], nm[48];
                long n;
                char *d;
                snprintf(nm, sizeof nm, "bin_%d", i);
                set_label(nm, cur_addr());
                join_path(path, sizeof path, mml_dir, bin_files[i]);
                d = read_file(path, &n);
                for (k = 0; k < n; k++) put_byte((uint8_t)d[k]);
                free(d);
            }
        }
    } else if (!strcmp(item, "align")) {
        Vars v;
        long n;
        vinit(&v);
        n = eval_str(args, &v);
        if (n < 1) die("align must be >= 1");
        while (cur_addr() % n) put_byte(0);
    } else {
        die("unknown layout item '%s'", item);
    }
}

static void build_song(void)
{
    int i, mask = 0;
    char nm[48];
    set_label("base", D.base);
    for (i = 0; i < MAXCH; i++) {
        int used = i < D.channels && tracks[i].used;
        if (used) mask |= 1 << i;
        snprintf(nm, sizeof nm, "used_%d", i);
        set_label(nm, used);
        snprintf(nm, sizeof nm, "track_%d", i);
        set_label(nm, D.unused_ptr);
        snprintf(nm, sizeof nm, "track_%d_loop", i);
        set_label(nm, D.unused_ptr);
    }
    set_label("used_mask", mask);
    for (i = 0; i < nents; i++)
        if (!strcmp(ents[i].sec, "layout")) {
            snprintf(g_where, sizeof g_where, "layout '%s'", ents[i].key);
            layout_line(ents[i].key, ents[i].val);
        }
    g_where[0] = 0;
    set_label("end", cur_addr());
    set_label("size", song_len);
    fix_resolve();
    if (D.base + song_len - 1 > D.limit)
        die("song data (%d bytes at $%04lX) exceeds limit $%04lX", song_len, D.base, D.limit);
}

/* ------------------------------------------------------------------ */
/* SPC image                                                           */
/* ------------------------------------------------------------------ */
static uint8_t ram[RAMSZ], dsp[128], xram[64], hdr[0x100];

static void set_text(int off, int n, const char *s)
{
    memset(hdr + off, 0, n);
    memcpy(hdr + off, s, strlen(s) < (size_t)n ? strlen(s) : (size_t)n);
}

static void init_spc(void)
{
    int i;
    {
        time_t now = time(NULL);
        char date[16];
        memset(hdr, 0, sizeof hdr);
        memcpy(hdr, "SNES-SPC700 Sound File Data v0.30", 33);
        hdr[0x21] = hdr[0x22] = hdr[0x23] = 26;
        hdr[0x24] = 30;
        strftime(date, sizeof date, "%m/%d/%Y", localtime(&now));
        set_text(0x9E, 11, date);
        set_text(0xA9, 3, "180");
        set_text(0xAC, 5, "10000");
        dsp[0x6C] = 0x20;
    }
    for (i = 0; i < nents; i++) {
        if (strcmp(ents[i].sec, "spc")) continue;
        if (!strcmp(ents[i].key, "load")) {
            char *q = xstrdup(ents[i].val), *a, *d;
            char path[1024];
            long n, addr;
            a = strrchr(q, ' ');
            if (!a) a = strrchr(q, '\t');
            if (!a) die("load = <file> <addr>");
            *a++ = 0;
            addr = parse_number(a);
            q = trim(q);
            unquote(q);
            join_path(path, sizeof path, drv_dir, q);
            d = read_file(path, &n);
            if (addr + n > RAMSZ) die("'%s' does not fit in RAM at $%04lX", path, addr);
            memcpy(ram + addr, d, n);
            free(d);
        } else if (!strcmp(ents[i].key, "dsp_file")) {
            char path[1024], *q = xstrdup(ents[i].val), *d;
            long n;
            unquote(q);
            join_path(path, sizeof path, drv_dir, q);
            d = read_file(path, &n);
            memcpy(dsp, d, n < 128 ? n : 128);
            free(d);
        }
    }
    for (i = 0; i < nents; i++) {
        char *sp;
        char tmp[256];
        if (strcmp(ents[i].sec, "spc")) continue;
        if (!strcmp(ents[i].key, "dsp") || !strcmp(ents[i].key, "poke")) {
            long a, v;
            snprintf(tmp, sizeof tmp, "%s", ents[i].val);
            sp = tmp;
            while (*sp && !isspace((unsigned char)*sp)) sp++;
            if (!*sp) die("'%s = <addr> <value>' expected", ents[i].key);
            *sp++ = 0;
            a = parse_number(tmp);
            v = parse_number(sp);
            if (ents[i].key[0] == 'd') {
                if (a < 0 || a > 127) die("DSP register out of range");
                dsp[a] = (uint8_t)v;
            } else {
                if (a < 0 || a > 0xFFFF) die("poke address out of range");
                ram[a] = (uint8_t)v;
            }
        }
    }
    {
        static const struct { const char *k; int off; } regs[] = {
            { "a", 0x27 }, { "x", 0x28 }, { "y", 0x29 }, { "psw", 0x2A }, { "sp", 0x2B }
        };
        size_t k;
        const char *pc = cfg_get("spc", "pc");
        if (pc) {
            long v = parse_number(pc);
            hdr[0x25] = v & 0xFF;
            hdr[0x26] = (v >> 8) & 0xFF;
        } else die("[spc] pc is required");
        for (k = 0; k < sizeof regs / sizeof regs[0]; k++) {
            const char *v = cfg_get("spc", regs[k].k);
            if (v) hdr[regs[k].off] = (uint8_t)parse_number(v);
        }
    }
}

static void apply_song_and_patches(void)
{
    int i;
    for (i = 0; i < nsamples; i++) {
        char path[1024];
        long n;
        char *d;
        snprintf(g_where, sizeof g_where, "#sample '%s'", samples[i].file);
        join_path(path, sizeof path, mml_dir, samples[i].file);
        d = read_file(path, &n);
        if (samples[i].addr < 0 || samples[i].addr + n > RAMSZ)
            die("'%s' does not fit in RAM at $%04lX", path, samples[i].addr);
        memcpy(ram + samples[i].addr, d, n);
        free(d);
        g_where[0] = 0;
    }
    for (i = 0; i < ndspsets; i++) dsp[dspsets[i].reg] = (uint8_t)dspsets[i].val;
    if (D.base + song_len > RAMSZ) die("song overflows RAM");
    memcpy(ram + D.base, song, song_len);
    for (i = 0; i < nents; i++) {
        if (!strcmp(ents[i].sec, "song") && !strcmp(ents[i].key, "patch")) {
            char tmp[512], *sp;
            uint8_t buf[256];
            Vars v;
            long addr;
            int n;
            vinit(&v);
            snprintf(g_where, sizeof g_where, "patch '%s'", ents[i].val);
            snprintf(tmp, sizeof tmp, "%s", ents[i].val);
            sp = tmp;
            while (*sp && !isspace((unsigned char)*sp)) sp++;
            if (!*sp) die("patch = <addr> <tokens...>");
            *sp++ = 0;
            addr = eval_str(tmp, &v);
            n = encode_tokens(sp, &v, addr, buf, sizeof buf);
            if (addr < 0 || addr + n > RAMSZ) die("patch address out of range");
            memcpy(ram + addr, buf, n);
            g_where[0] = 0;
        }
    }
}

static void write_spc(const char *path)
{
    FILE *f = fopen(path, "wb");
    uint8_t pad[64];
    if (!f) die("cannot write '%s'", path);
    memset(pad, 0, sizeof pad);
    fwrite(hdr, 1, 0x100, f);
    fwrite(ram, 1, RAMSZ, f);
    fwrite(dsp, 1, 128, f);
    fwrite(pad, 1, 64, f);
    fwrite(xram, 1, 64, f);
    fclose(f);
}

/* ------------------------------------------------------------------ */
/* MML file                                                            */
/* ------------------------------------------------------------------ */
static char **lines;
static int nlines;

static void split_lines(char *buf)
{
    char *p = buf;
    int cap = 0;
    while (p) {
        char *nl = strchr(p, '\n');
        if (nl) *nl = 0;
        if (nlines >= cap) {
            cap = cap ? cap * 2 : 256;
            lines = xrealloc(lines, cap * sizeof *lines);
        }
        lines[nlines++] = p;
        p = nl ? nl + 1 : NULL;
    }
}

static void strip_comment(char *s)
{
    int q = 0;
    for (; *s; s++) {
        if (*s == '"') q = !q;
        if (!q && *s == ';') { *s = 0; return; }
        if (!q && s[0] == '/' && s[1] == '/') { *s = 0; return; }
        if (*s == '\r') *s = ' ';
    }
}

static void tag_directive(const char *name, char *arg)
{
    unquote(arg);
    if (!strcmp(name, "title")) set_text(0x2E, 32, arg);
    else if (!strcmp(name, "game")) set_text(0x4E, 32, arg);
    else if (!strcmp(name, "dumper")) set_text(0x6E, 16, arg);
    else if (!strcmp(name, "comment")) set_text(0x7E, 32, arg);
    else if (!strcmp(name, "artist")) set_text(0xB1, 32, arg);
    else if (!strcmp(name, "length")) set_text(0xA9, 3, arg);
    else if (!strcmp(name, "fade")) set_text(0xAC, 5, arg);
    else if (!strcmp(name, "bin")) {
        if (nbins >= 32) die("too many #bin");
        bin_files[nbins++] = xstrdup(arg);
    } else if (!strcmp(name, "sample")) {
        /* #sample "file.brr" 0x4000 */
        char *a = strrchr(arg, ' ');
        if (!a) a = strrchr(arg, '\t');
        if (!a) die("#sample \"file\" <addr>");
        *a++ = 0;
        if (nsamples >= 64) die("too many #sample");
        samples[nsamples].addr = parse_number(a);
        arg = trim(arg);
        unquote(arg);
        samples[nsamples++].file = xstrdup(arg);
    } else if (!strcmp(name, "dsp")) {
        /* #dsp <reg> <val> */
        char *a = arg;
        long r, v;
        while (*a && !isspace((unsigned char)*a)) a++;
        if (!*a) die("#dsp <reg> <val>");
        *a++ = 0;
        r = parse_number(arg);
        v = parse_number(trim(a));
        if (r < 0 || r > 127) die("DSP register out of range");
        if (ndspsets >= 128) die("too many #dsp");
        dspsets[ndspsets].reg = (int)r;
        dspsets[ndspsets++].val = (int)v;
    } else if (!strcmp(name, "driver")) {
        /* handled in pre-scan */
    } else die("unknown directive '#%s'", name);
}

static void parse_mml(void)
{
    int i, cur[MAXCH], ncur = 0, k;
    for (k = 0; k < MAXCH; k++) {
        tracks[k].oct = D.oct_default;
        tracks[k].deflen = D.tpq;
    }
    for (i = 0; i < nlines; i++) {
        char *p;
        strip_comment(lines[i]);
        p = trim(lines[i]);
        if (!*p) continue;
        snprintf(g_where, sizeof g_where, "line %d", i + 1);
        if (*p == '#') {
            char *sp = p + 1;
            char name[32];
            while (*sp && !isspace((unsigned char)*sp)) sp++;
            snprintf(name, sizeof name, "%.*s", (int)(sp - p - 1), p + 1);
            tag_directive(name, trim(sp));
            continue;
        }
        if (p[0] >= 'A' && p[0] <= 'H') {
            char *q = p;
            int n = 0;
            while (*q >= 'A' && *q <= 'H') {
                if (n < MAXCH) cur[n++] = *q - 'A';
                q++;
            }
            if (isspace((unsigned char)*q) || !*q) {
                ncur = n;
                for (k = 0; k < ncur; k++)
                    if (cur[k] >= D.channels) die("channel %c exceeds driver channel count", 'A' + cur[k]);
                p = q;
            }
        }
        if (!ncur) die("no channel selected (start the line with A-H)");
        for (k = 0; k < ncur; k++) parse_chunk(cur[k], p, i + 1);
    }
    g_where[0] = 0;
    for (k = 0; k < MAXCH; k++) {
        if (tracks[k].depth) {
            snprintf(g_where, sizeof g_where, "track %c", 'A' + k);
            die("unterminated '['");
        }
        tracks[k].used = tracks[k].n > 0;
    }
}

int main(int argc, char **argv)
{
    const char *in = NULL, *out = NULL, *drv = NULL;
    char outbuf[1024];
    int verbose = 0, i;
    char *text;

    for (i = 1; i < argc; i++) {
        if (!strcmp(argv[i], "-d") && i + 1 < argc) drv = argv[++i];
        else if (!strcmp(argv[i], "-o") && i + 1 < argc) out = argv[++i];
        else if (!strcmp(argv[i], "-v")) verbose = 1;
        else if (argv[i][0] == '-') die("unknown option '%s'", argv[i]);
        else in = argv[i];
    }
    if (!in) {
        fprintf(stderr, "usage: %s [-d driver.drv] [-o out.spc] [-v] song.mml\n", argv[0]);
        return 1;
    }
    dir_of(in, mml_dir, sizeof mml_dir);
    text = read_file(in, NULL);
    split_lines(text);

    /* pre-scan for #driver */
    if (!drv) {
        static char dpath[1024];
        for (i = 0; i < nlines; i++) {
            char tmp[1024], *p;
            snprintf(tmp, sizeof tmp, "%s", lines[i]);
            strip_comment(tmp);
            p = trim(tmp);
            if (!strncmp(p, "#driver", 7) && isspace((unsigned char)p[7])) {
                char *a = trim(p + 7);
                unquote(a);
                join_path(dpath, sizeof dpath, mml_dir, a);
                drv = dpath;
            }
        }
    }
    if (!drv) die("no driver given (use -d or '#driver \"x.drv\"')");

    load_driver(drv);
    init_driver();
    init_spc();
    parse_mml();
    build_song();
    apply_song_and_patches();

    if (!out) {
        char *dot;
        snprintf(outbuf, sizeof outbuf, "%s", in);
        dot = strrchr(outbuf, '.');
        if (dot && !strchr(dot, '/') && !strchr(dot, '\\')) *dot = 0;
        strncat(outbuf, ".spc", sizeof outbuf - strlen(outbuf) - 1);
        out = outbuf;
    }
    write_spc(out);

    if (verbose) {
        printf("song data: $%04lX - $%04lX (%d bytes)\n", D.base, D.base + song_len - 1, song_len);
        for (i = 0; i < D.channels; i++) {
            long a, b;
            char nm[48];
            if (!tracks[i].used) continue;
            snprintf(nm, sizeof nm, "track_%d", i);
            get_label(nm, &a);
            snprintf(nm, sizeof nm, "track_%d_end", i);
            get_label(nm, &b);
            printf("  track %c: $%04lX - $%04lX (%ld bytes)\n", 'A' + i, a, b - 1, b - a);
        }
    }
    printf("wrote %s\n", out);
    return 0;
}
