/*
 * SilverSky v0.3.1 - emulador de SNES con netplay 1 vs 1 y 2 vs 2 para PS3
 *   PSL1GHT + nucleo libretro Snes9x 2010
 *
 * Se construye sobre la estructura de red de NesNet (copia: NesNet no se toca):
 *   - Lockstep con retraso fijo (delay) sobre TCP, sin servidor, conexion directa host <-> cliente.
 *   - El host crea la sala y recibe un CODIGO NUMERICO de 10 digitos (su IP publica; el puerto sale de config.txt).
 *   - 2 vs 2: cada PS3 aporta 2 mandos locales; el host = jugadores 1 y 2, el que se une = jugadores 3 y 4.
 *     El nucleo recibe un multitap en el puerto 2 (Super Bomberman 3, etc.).
 *   - Los juegos con chip Super FX no se cargan en esta version.
 *
 * Se compila de 2 formas:
 *   -DNESNET_PS3   -> aplicacion real para PS3
 *   -DNESNET_HOST  -> version de pruebas para PC (sin video, mando simulado)
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <unistd.h>
#include <errno.h>
#include <dirent.h>
#include <sys/stat.h>
#include <ctype.h>

#include "libretro.h"

#ifdef NESNET_PS3
#include <ppu-types.h>
#include <malloc.h>
#include <sys/process.h>
#include <sys/systime.h>
#include <io/pad.h>
#include <rsx/rsx.h>
#include <sysutil/sysutil.h>
#include <sysutil/video.h>
#include <audio/audio.h>
#include <sys/socket.h>
#include <arpa/inet.h>
#include <net/net.h>
#include <net/netdb.h>
#include <net/netctl.h>
#include <sysmodule/sysmodule.h>
#include <netinet/in.h>
SYS_PROCESS_PARAM(1001, 0x100000);
int closesocket(int s);      /* definida en libnet, pero sin prototipo en las cabeceras */
#else
#include <time.h>
#include <signal.h>
#include <poll.h>
#include <fcntl.h>
#include <netdb.h>
#include <sys/socket.h>
#include <netinet/in.h>
#include <netinet/tcp.h>
#include <arpa/inet.h>
#define closesocket close
#endif

#ifndef TCP_NODELAY
#define TCP_NODELAY 1
#endif

/* ------------------------------------------------------------------ */
/* Constantes                                                          */
/* ------------------------------------------------------------------ */
#define DEFAULT_PORT   7778        /* NesNet usa 7777: asi pueden convivir en la misma red */
#define SCR_W          256
#define SCR_H          240
#define RING           64
#define MSG_SIZE       20
#define NO_FRAME       0xFFFFFFFFu

/* Modos de juego (el menu y config.txt devuelven siempre estos valores) */
#define MODE_SOLO      0
#define MODE_HOST      1
#define MODE_JOIN      2
#define MODE_ROM       3      /* v1.7: opcion "ELEGIR ROM" del menu (no es un modo de juego) */
#define MODE_OPT       5      /* v1.8.2: opcion "OPCIONES" del menu (pantalla y mandos; no es un modo de juego) */
#define MODE_HOST1     6      /* v0.2: CREAR SALA 1 VS 1 (host = mando 1) */
#define MODE_JOIN1     7      /* v0.2: UNIRSE A SALA 1 VS 1 (el que se une = mando 2) */

/* Version del protocolo de SilverSky. NesNet usa 3 y 4: si alguien mezcla programas, el saludo se rechaza. */
/* v0.2.7: suben a 0x5311 / 0x5312 porque aparece el mensaje M_STATE (estado guardado del host + bloque de datos): una v0.2.6 y una
 * v0.2.7 se rechazan en el saludo en vez de desincronizarse. */
#define PROTO_VER4     0x5311
#define PROTO_VER2     0x5312   /* v0.2: 1 vs 1 (un 2 vs 2 y un 1 vs 1 se rechazan entre si en el saludo) */

/* v1.7: selector de ROMs. Las ROMs van en USRDIR/roms/ y se reconocen por su cabecera, no por el nombre */
#define ROM_MAX        256
#define ROM_NAMELEN    96

/* Botones SNES: el bit n es el id n de libretro (B=0, Y=1, SELECT=2, START=3, ARRIBA=4, ABAJO=5, IZQ=6, DER=7, A=8, X=9, L=10, R=11) */
#define NB_B      0x001
#define NB_Y      0x002
#define NB_SEL    0x004
#define NB_START  0x008
#define NB_UP     0x010
#define NB_DOWN   0x020
#define NB_LEFT   0x040
#define NB_RIGHT  0x080
#define NB_A      0x100
#define NB_X      0x200
#define NB_L      0x400
#define NB_R      0x800

#define SNES_DEV_MULTITAP RETRO_DEVICE_SUBCLASS(RETRO_DEVICE_JOYPAD, 0)

/* Botones de la interfaz (menus) */
#define UI_UP     0x01
#define UI_DOWN   0x02
#define UI_LEFT   0x04
#define UI_RIGHT  0x08
#define UI_OK     0x10
#define UI_CANCEL 0x20
#define UI_START  0x40

/* ------------------------------------------------------------------ */
/* Estado global                                                       */
/* ------------------------------------------------------------------ */
typedef struct {
    char     rom[420];        /* v1.7: ruta de la ROM elegida en el selector (ya no sale de config.txt) */
    char     mode[16];        /* "", "host", "client", "local" */
    char     code[32];
    char     public_ip[32];
    int      delay;           /* 0 = automatico */
    int      port;
    int      res;             /* 0 = la de la TV, 720 = forzar 720p */
    int      render;          /* 0 = GPU (escalado), 1 = CPU directo (sin transferencia GPU) */
    int      zoom;            /* 0 = automatico */
    int      audio;           /* 1 = con sonido (por defecto), 0 = sin sonido */
    int      upnp;            /* v1.6: 1 = el host abre el puerto por UPnP (por defecto), 0 = no */
} Config;

static Config   g_cfg;
static char     g_dir[256] = "/dev_hdd0/game/SILV00001/USRDIR";
static FILE    *g_log;
static int      g_running = 1;
static const char *g_err = "";

static uint8_t *g_rom;                    /* NULL = ninguna ROM elegida (stand-by) */
static size_t   g_romsz;
static uint32_t g_romcrc;
static char     g_rom_name[ROM_NAMELEN];  /* v1.7: nombre del archivo de la ROM elegida */
static const char *g_rom_why = "";        /* por que no se pudo cargar la ROM (si hay motivo especial) */
static int      g_menu_sel;               /* v1.7: opcion marcada del menu principal */

static uint32_t g_fb[SCR_W * SCR_H];      /* lienzo ARGB */
static uint16_t g_pad[5];                 /* entrada SNES que ve el nucleo (puerto 0 + hasta 4 del multitap) */
static int      g_one;                    /* v0.2: 1 = partida ONLINE 1 vs 1 (1 mando por consola, 2 mandos normales) */
static int      g_proto = PROTO_VER4;     /* protocolo del saludo: PROTO_VER4 (2 vs 2) o PROTO_VER2 (1 vs 1) */
static int      g_four;                   /* 1 = partida 2 vs 2 (multitap en el puerto 2), 0 = SOLO con 2 mandos normales */
static unsigned g_pixfmt = RETRO_PIXEL_FORMAT_RGB565;
static uint32_t g_frame_crc;
/* v0.2.2: la suma de control de cada imagen solo sirve para detectar desincronia ONLINE; en SOLO se omite (costaba ~2,9 ms/cuadro) */
static int g_hash_on = 1;
static int      g_core_loaded;

static int      g_net = -1;               /* socket de la partida */
static uint8_t  g_rx[512];
static int      g_rxlen;

/* ------------------------------------------------------------------ */
/* Utilidades                                                          */
/* ------------------------------------------------------------------ */
static uint32_t now_ms(void)
{
#ifdef NESNET_PS3
    u64 s, n;
    sysGetCurrentTime(&s, &n);
    return (uint32_t)(s * 1000ULL + n / 1000000ULL);
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (uint32_t)(ts.tv_sec * 1000ULL + ts.tv_nsec / 1000000ULL);
#endif
}

/* v0.2.1: reloj en microsegundos (mismo reloj que now_ms) para el medidor de rendimiento */
static unsigned long long now_us(void)
{
#ifdef NESNET_PS3
    u64 s, n;
    sysGetCurrentTime(&s, &n);
    return (unsigned long long)s * 1000000ULL + (unsigned long long)(n / 1000ULL);
#else
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (unsigned long long)ts.tv_sec * 1000000ULL + (unsigned long long)(ts.tv_nsec / 1000);
#endif
}

static void sleep_ms(int ms) { usleep((useconds_t)ms * 1000); }

static void logf_(const char *fmt, ...)
{
    char buf[256];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, sizeof buf, fmt, ap);
    va_end(ap);
    if (g_log) { fprintf(g_log, "[%u] %s\n", (unsigned)now_ms(), buf); fflush(g_log); }
#ifdef NESNET_HOST
    fprintf(stderr, "%s\n", buf);
#endif
}

/* ------------------------------------------------------------------ */
/* v0.2.1: medidor de rendimiento. Cada ~2 s escribe en silversky.log una linea "rend:" con el tiempo medio por   */
/* cuadro (en ms) de cada parte. Un cuadro de 60 fps dura 16,67 ms: si "trabajo" pasa de eso, la consola no llega. */
/*   nucleo = emulacion pura (CPU/PPU/audio del SNES)   video = convertir la imagen del nucleo a 32 bits            */
/*   hash   = suma de control de la imagen (solo sirve para detectar desincronia online)                           */
/*   dibujo = copiar/escalar a la pantalla (sin contar la espera del vsync)   audio = remuestreo y envio al anillo  */
/*   red    = tiempo esperando al otro jugador (solo online)   espera = tiempo libre esperando el vsync           */
/*   max    = el cuadro mas pesado de la ventana   lentos = cuadros con trabajo > 16,7 ms (de los medidos)         */
/* ------------------------------------------------------------------ */
static unsigned long long pf_run_cur, pf_vcb_cur, pf_hash_cur, pf_draw_cur, pf_wait_cur, pf_pump_cur, pf_net_cur;
static unsigned long long pf_run_s, pf_vcb_s, pf_hash_s, pf_draw_s, pf_wait_s, pf_pump_s, pf_net_s, pf_work_s, pf_max, pf_t0;
static unsigned pf_n, pf_slow, pf_skip;

/* ------------------------------------------------------------------ */
/* v0.2.5: salto de dibujo cuando va atrasado (SOLO y online).                                                      */
/* Si el cuadro actual (emulacion + lo que ya se llevaba) mas el dibujo estimado haria pasar el atraso acumulado de  */
/* SK_TOL, este cuadro NO se dibuja ni se manda a pantalla (la imagen anterior se queda un cuadro mas); el juego, el */
/* audio, los mandos y la red siguen exactamente igual. Nunca se saltan mas de SK_MAX_RUN cuadros seguidos. Solo     */
/* depende de tiempos: no toca el estado de la emulacion ni los mensajes de red.                                    */
/* ------------------------------------------------------------------ */
#define SK_FRAME_US  16667ULL      /* un cuadro a 60 Hz */
#define SK_TOL_US    3000ULL       /* atraso tolerado antes de empezar a saltar dibujos */
#define SK_LAG_MAX   20000ULL      /* tope del atraso acumulado (si la emulacion sola no llega, no crece sin fin) */
#define SK_MAX_RUN   2             /* como maximo 2 cuadros seguidos sin dibujar */
/* sk_lag = atraso acumulado respecto a un cuadro cada 16,67 ms (negativo = adelantado, hasta -SK_TOL_US) */
static long long sk_lag;
static unsigned long long sk_draw_est = 4000;
static unsigned sk_run;
static int sk_on = 1;              /* 0 = nunca saltar (solo pruebas de PC: NESNET_NOSKIP) */

static void sk_reset(void) { sk_lag = 0; sk_run = 0; }

/* partial = tiempo de trabajo de este cuadro hasta ahora (emulacion, hash, audio), sin esperas de red ni de vsync */
static int sk_should_skip(unsigned long long partial)
{
    if (!sk_on || sk_run >= SK_MAX_RUN) return 0;
    return sk_lag + (long long)partial + (long long)sk_draw_est > (long long)(SK_FRAME_US + SK_TOL_US);
}

/* work = trabajo total del cuadro (sin esperas); drew = tiempo medido del dibujo (0 si se salto) */
static void sk_account(unsigned long long work, unsigned long long drew, int skipped)
{
    long long lag = sk_lag + (long long)work - (long long)SK_FRAME_US;
    if (lag < -(long long)SK_TOL_US) lag = -(long long)SK_TOL_US;
    if (lag > (long long)SK_LAG_MAX) lag = (long long)SK_LAG_MAX;
    sk_lag = lag;
    if (skipped) { sk_run++; pf_skip++; }
    else { sk_run = 0; sk_draw_est = (sk_draw_est * 3 + drew) / 4; }
}

static void pf_cur_reset(void)
{
    pf_run_cur = pf_vcb_cur = pf_hash_cur = pf_draw_cur = pf_wait_cur = pf_pump_cur = pf_net_cur = 0;
}

static void pf_window_reset(void)
{
    pf_run_s = pf_vcb_s = pf_hash_s = pf_draw_s = pf_wait_s = pf_pump_s = pf_net_s = pf_work_s = pf_max = 0;
    pf_n = pf_slow = pf_skip = 0;
    pf_t0 = now_us();
    pf_cur_reset();
}

#define PF_MS(x)  (unsigned)((x) / 1000ULL), (unsigned)(((x) % 1000ULL) / 10ULL)

/* tf0 = now_us() al empezar el cuadro (antes de pump()); se llama justo despues de present() */
static void pf_frame_end(unsigned long long tf0)
{
    unsigned long long tf1 = now_us(), tot = tf1 - tf0, idle = pf_wait_cur + pf_net_cur, work, core, draw;
    work = tot > idle ? tot - idle : 0;
    core = pf_run_cur > pf_vcb_cur + pf_hash_cur ? pf_run_cur - pf_vcb_cur - pf_hash_cur : 0;
    draw = pf_draw_cur > pf_wait_cur ? pf_draw_cur - pf_wait_cur : 0;
    (void)core;
    pf_run_s += pf_run_cur; pf_vcb_s += pf_vcb_cur; pf_hash_s += pf_hash_cur;
    pf_draw_s += draw; pf_wait_s += pf_wait_cur; pf_pump_s += pf_pump_cur; pf_net_s += pf_net_cur;
    pf_work_s += work;
    if (work > pf_max) pf_max = work;
    if (work > 16700ULL) pf_slow++;
    pf_n++;
    pf_cur_reset();
    if (!pf_t0) pf_t0 = tf0;
    if (tf1 - pf_t0 >= 2000000ULL && pf_n > 0) {
        unsigned long long n = pf_n, el = tf1 - pf_t0;
        unsigned long long a_run = pf_run_s / n, a_vcb = pf_vcb_s / n, a_hash = pf_hash_s / n;
        unsigned long long a_core = a_run > a_vcb + a_hash ? a_run - a_vcb - a_hash : 0;
        unsigned long long a_draw = pf_draw_s / n, a_pump = pf_pump_s / n, a_wait = pf_wait_s / n, a_net = pf_net_s / n;
        unsigned long long a_work = pf_work_s / n;
        logf_("rend: fps=%u trabajo=%u.%02u [nucleo=%u.%02u video=%u.%02u hash=%u.%02u dibujo=%u.%02u audio=%u.%02u] red=%u.%02u espera=%u.%02u max=%u.%02u lentos=%u/%u saltos=%u",
              (unsigned)((n * 1000000ULL + el / 2) / el),
              PF_MS(a_work), PF_MS(a_core), PF_MS(a_vcb), PF_MS(a_hash), PF_MS(a_draw), PF_MS(a_pump),
              PF_MS(a_net), PF_MS(a_wait), PF_MS(pf_max), pf_slow, (unsigned)n, pf_skip);
        pf_window_reset();
    }
}

static uint32_t crc32_buf(const uint8_t *d, size_t n)
{
    uint32_t c = 0xFFFFFFFFu;
    size_t i;
    int k;
    for (i = 0; i < n; i++) {
        c ^= d[i];
        for (k = 0; k < 8; k++) c = (c >> 1) ^ (0xEDB88320u & (0u - (c & 1u)));
    }
    return ~c;
}

static uint32_t fnv_u32(uint32_t h, uint32_t v)
{
    int i;
    for (i = 0; i < 4; i++) { h ^= (v >> (i * 8)) & 0xFF; h *= 16777619u; }
    return h;
}

static void pump(void);   /* atiende al sistema (boton PS, etc.) */

/* Latido: cada ~2 s escribe en silversky.log en que fase esta el programa. Si la consola se
 * cuelga, la ultima linea del log dice cuando y en que fase paso. */
static const char *g_stage = "inicio";
static uint32_t    g_hb;
static void heartbeat(void)
{
    if (++g_hb % 120 == 0) logf_("latido %u fase=%s", (unsigned)g_hb, g_stage);
}

/* ------------------------------------------------------------------ */
/* Configuracion (config.txt: clave=valor)                             */
/* ------------------------------------------------------------------ */
static void cfg_defaults(void)
{
    memset(&g_cfg, 0, sizeof g_cfg);
    g_cfg.port = DEFAULT_PORT;
    g_cfg.res = 720;                      /* v1.3: por defecto 720p (probado en la PS3) */
    g_cfg.audio = 1;                      /* v1.5: sonido activado por defecto (audio=off o R2 al abrir lo apaga) */
    g_cfg.render = 1;                     /* v1.3: por defecto dibujo por CPU, sin la GPU (la ruta GPU se colgo 3 veces) */
    g_cfg.upnp = 1;                       /* v1.6: abrir el puerto por UPnP (upnp=off en config.txt lo apaga) */
}

static void cfg_load(void)
{
    char path[300], line[300];
    FILE *f;
    cfg_defaults();
    snprintf(path, sizeof path, "%s/config.txt", g_dir);
    f = fopen(path, "r");
    if (!f) { logf_("sin config.txt (%s), uso valores por defecto", path); return; }
    while (fgets(line, sizeof line, f)) {
        char *k = line, *v, *e;
        while (*k == ' ' || *k == '\t') k++;
        if (*k == '#' || *k == ';' || *k == '\n' || *k == '\r' || !*k) continue;
        v = strchr(k, '=');
        if (!v) continue;
        *v++ = 0;
        e = k + strlen(k);
        while (e > k && (e[-1] == ' ' || e[-1] == '\t')) *--e = 0;
        while (*v == ' ' || *v == '\t') v++;
        e = v + strlen(v);
        while (e > v && (e[-1] == '\n' || e[-1] == '\r' || e[-1] == ' ' || e[-1] == '\t')) *--e = 0;
        if (!strcmp(k, "rom")) { /* v1.7: la ROM ya no se lee de aqui, se elige en el menu (carpeta roms) */ }
        else if (!strcmp(k, "mode"))      snprintf(g_cfg.mode, sizeof g_cfg.mode, "%s", v);
        else if (!strcmp(k, "code"))      snprintf(g_cfg.code, sizeof g_cfg.code, "%s", v);
        else if (!strcmp(k, "public_ip")) snprintf(g_cfg.public_ip, sizeof g_cfg.public_ip, "%s", v);
        else if (!strcmp(k, "delay"))     g_cfg.delay = atoi(v);
        else if (!strcmp(k, "port"))      g_cfg.port = atoi(v);
        else if (!strcmp(k, "res"))       { if (!strcmp(v, "auto")) g_cfg.res = 0; else if (!strcmp(v, "720")) g_cfg.res = 720; }
        else if (!strcmp(k, "render"))    { if (!strcmp(v, "gpu")) g_cfg.render = 0; else if (!strcmp(v, "cpu")) g_cfg.render = 1; }
        else if (!strcmp(k, "zoom"))      g_cfg.zoom = atoi(v);
        else if (!strcmp(k, "audio"))     { if (!strcmp(v, "off")) g_cfg.audio = 0; else if (!strcmp(v, "on")) g_cfg.audio = 1; }
        else if (!strcmp(k, "upnp"))      { if (!strcmp(v, "off")) g_cfg.upnp = 0; else if (!strcmp(v, "on")) g_cfg.upnp = 1; }
    }
    fclose(f);
    if (g_cfg.port <= 0 || g_cfg.port > 65535) g_cfg.port = DEFAULT_PORT;
}

/* ------------------------------------------------------------------ */
/* Fuente 5x7 (ASCII 32..90) y dibujo de texto en el lienzo            */
/* ------------------------------------------------------------------ */
static const uint8_t font5x7[59][5] = {
    {0x00,0x00,0x00,0x00,0x00},{0x00,0x00,0x5F,0x00,0x00},{0x00,0x07,0x00,0x07,0x00},
    {0x14,0x7F,0x14,0x7F,0x14},{0x24,0x2A,0x7F,0x2A,0x12},{0x23,0x13,0x08,0x64,0x62},
    {0x36,0x49,0x55,0x22,0x50},{0x00,0x05,0x03,0x00,0x00},{0x00,0x1C,0x22,0x41,0x00},
    {0x00,0x41,0x22,0x1C,0x00},{0x14,0x08,0x3E,0x08,0x14},{0x08,0x08,0x3E,0x08,0x08},
    {0x00,0x50,0x30,0x00,0x00},{0x08,0x08,0x08,0x08,0x08},{0x00,0x60,0x60,0x00,0x00},
    {0x20,0x10,0x08,0x04,0x02},
    {0x3E,0x51,0x49,0x45,0x3E},{0x00,0x42,0x7F,0x40,0x00},{0x42,0x61,0x51,0x49,0x46},
    {0x21,0x41,0x45,0x4B,0x31},{0x18,0x14,0x12,0x7F,0x10},{0x27,0x45,0x45,0x45,0x39},
    {0x3C,0x4A,0x49,0x49,0x30},{0x01,0x71,0x09,0x05,0x03},{0x36,0x49,0x49,0x49,0x36},
    {0x06,0x49,0x49,0x29,0x1E},
    {0x00,0x36,0x36,0x00,0x00},{0x00,0x56,0x36,0x00,0x00},{0x08,0x14,0x22,0x41,0x00},
    {0x14,0x14,0x14,0x14,0x14},{0x00,0x41,0x22,0x14,0x08},{0x02,0x01,0x51,0x09,0x06},
    {0x32,0x49,0x79,0x41,0x3E},
    {0x7E,0x11,0x11,0x11,0x7E},{0x7F,0x49,0x49,0x49,0x36},{0x3E,0x41,0x41,0x41,0x22},
    {0x7F,0x41,0x41,0x22,0x1C},{0x7F,0x49,0x49,0x49,0x41},{0x7F,0x09,0x09,0x09,0x01},
    {0x3E,0x41,0x49,0x49,0x7A},{0x7F,0x08,0x08,0x08,0x7F},{0x00,0x41,0x7F,0x41,0x00},
    {0x20,0x40,0x41,0x3F,0x01},{0x7F,0x08,0x14,0x22,0x41},{0x7F,0x40,0x40,0x40,0x40},
    {0x7F,0x02,0x0C,0x02,0x7F},{0x7F,0x04,0x08,0x10,0x7F},{0x3E,0x41,0x41,0x41,0x3E},
    {0x7F,0x09,0x09,0x09,0x06},{0x3E,0x41,0x51,0x21,0x5E},{0x7F,0x09,0x19,0x29,0x46},
    {0x46,0x49,0x49,0x49,0x31},{0x01,0x01,0x7F,0x01,0x01},{0x3F,0x40,0x40,0x40,0x3F},
    {0x1F,0x20,0x40,0x20,0x1F},{0x3F,0x40,0x38,0x40,0x3F},{0x63,0x14,0x08,0x14,0x63},
    {0x07,0x08,0x70,0x08,0x07},{0x61,0x51,0x49,0x45,0x43}
};

static void ui_text(int x, int y, const char *s, int sc, uint32_t col)
{
    for (; *s; s++, x += 6 * sc) {
        int c = (unsigned char)*s, cx, cy, i, j;
        if (c >= 'a' && c <= 'z') c -= 32;
        if (c == '_') c = '-';                /* v1.7: la fuente no trae _ ni [ ]: nombres de ROM mas legibles */
        else if (c == '[') c = '(';
        else if (c == ']') c = ')';
        if (c < 32 || c > 90) c = '?';
        for (cx = 0; cx < 5; cx++) {
            uint8_t colbits = font5x7[c - 32][cx];
            for (cy = 0; cy < 7; cy++) {
                if (!(colbits & (1 << cy))) continue;
                for (j = 0; j < sc; j++)
                    for (i = 0; i < sc; i++) {
                        int px = x + cx * sc + i, py = y + cy * sc + j;
                        if (px >= 0 && px < SCR_W && py >= 0 && py < SCR_H)
                            g_fb[py * SCR_W + px] = col;
                    }
            }
        }
    }
}

static void ui_center(int y, const char *s, int sc, uint32_t col)
{
    int w = (int)strlen(s) * 6 * sc - sc;
    ui_text((SCR_W - w) / 2, y, s, sc, col);
}

static void ui_clear(void)
{
    int i;
    for (i = 0; i < SCR_W * SCR_H; i++) g_fb[i] = 0xFF101838;
}

/* ------------------------------------------------------------------ */
/* v0.3.0: capa de menus a 1280x720 (solo dibujo; no toca la red ni el juego)                                       */
/* Los menus se dibujan en g_hr (1280x720, ARGB) con fuentes ya rasterizadas (Orbitron y Montserrat, embebidas en     */
/* base64) y un fondo de cielo/aurora. present() muestra g_hr en lugar del lienzo 256x240 cuando g_hr_on = 1.        */
/* Solo con render=cpu y pantalla de 640x360 o mas (hr_usable); si no, los menus se dibujan como en la v0.2.9.        */
/* ------------------------------------------------------------------ */

#define HR_W 1280
#define HR_H 720
static uint32_t g_hr[HR_W * HR_H];        /* lo que se esta dibujando */
static uint32_t g_hr_sky[HR_W * HR_H];    /* fondo (cielo, aurora, estrellas, montanas), se arma una sola vez */
static uint32_t g_hr_alt[HR_W * HR_H];    /* fondo del menu en partida: juego atenuado sobre el cielo */
static int      g_hr_on;                  /* 1 = el proximo present() muestra g_hr */
static int      g_hr_ready, g_hr_fail;

#define HC_SIL   0xFFCDD6EEu
#define HC_CY    0xFF5AE1FFu
#define HC_DIM   0xFF96A5D7u
#define HC_LINE  0xFF7887C8u
#define HC_CARD  0xFF0A0E2Cu
#define HC_SEL   0xFF0E3446u
#define HC_WHITE 0xFFFFFFFFu
#define HC_TXT   0xFFE1E8FAu
#define HC_WARN  0xFFFFC040u
#define HC_BX    0xFF286EDCu
#define HC_BO    0xFFD23246u
#define HC_LOCK  0xFF505068u
#define HC_LOCKS 0xFFA0A0B0u
#define HC_EMPTY 0xFF1E285Au

enum { HF_LOGO, HF_H1, HF_CODE, HF_OB15, HF_OB17, HF_OB19, HF_OM13, HF_OM14, HF_OM16, HF_OM18, HF_BTN,
       HF_MS13, HF_MS14, HF_MS15, HF_MS17, HF_MS17B, HF_MS18, HF_COUNT };

typedef struct { uint16_t cp; uint8_t adv; int8_t xo, yo; uint8_t w, h; uint32_t off; } HrGlyph;
typedef struct { int mid, asc, n; HrGlyph *g; const uint8_t *bm; size_t bmlen; } HrFace;
static HrFace  g_hf[HF_COUNT];
static uint8_t *g_hf_blob;

/* ---- datos embebidos (generados con Pillow a partir de Orbitron y Montserrat; 4 bits de transparencia por pixel) ---- */
static const char *const hr_faces_b64[] = {
"EQwmCQA8FQAAUwApANwpJAAAAABJAAsA3Ask4gIAAEwAJwDcJySoAwAAVgAyANwyJGYGAABFACYA3CYk6gkAAFIAKQDcKSSWDAAASwAoANwoJHgPAABZACgA3CokSBIAACAAEAAAEAA8FQAAAAAAKN//////////",
"/////9ggAAAAAAB///////////////////+AAAAAAI////////////////////+QAAAAT/////////////////////9QAAAN//////////////////////4AAAL///////////////////////MAAF//////////",
"/////////////3AAB///////////////////////+AAAf////0AAAAAAAAAAAABP////gAAH////9AAAAAAAAAAAAAT////4AAB/////QAAAAAAAAAAAAE////+AAAf////0AAAAAAAAAAAAAAAAAAAAAH////9A",
"AAAAAAAAAAAAAAAAAAAAB/////QAAAAAAAAAAAAAAAAAAAAAf///////////////////2SAAAAAF/////////////////////4AAAAAv/////////////////////6AAAADf/////////////////////2AAAAX/",
"/////////////////////gAAAAn/////////////////////9AAAAAf/////////////////////cAAAAAKd///////////////////4AAAAAAAAAAAAAAAAAAAAAE////+AAAAAAAAAAAAAAAAAAAAABP////gA",
"AAAAAAAAAAAAAAAAAAAAT////4AAB/////QAAAAAAAAAAAAE////+AAAf////0AAAAAAAAAAAABP////gAAH////9AAAAAAAAAAAAAT////4AAB///////////////////////+AAAX/////////////////////",
"//cAAC///////////////////////0AAAM//////////////////////4AAABP/////////////////////2AAAACP////////////////////oAAAAAB///////////////////+AAAAAAAAp3/////////////",
"//2SAAAAAC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL///",
"/6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+gAv////oAL////6AC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAA",
"AAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAA",
"AC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC//",
"//+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+Q",
"AAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC////+QAAAA",
"AAAAAAAAAAAAAAAC////+QAAAAAAAAAAAAAAAAAAAC///////////////////////9AC///////////////////////9AC///////////////////////9AC///////////////////////9AC//////////////",
"/////////9AC///////////////////////9AC///////////////////////9AC///////////////////////9AO/////xAAAAAAAAAAAAAAAAAABf////+QBv////+QAAAAAAAAAAAAAAAAAA7/////EADP//",
"//8wAAAAAAAAAAAAAAAAB/////9wAAP/////wAAAAAAAAAAAAAAAAB/////9AAAAr/////UAAAAAAAAAAAAAAACv////9AAAAB/////+AAAAAAAAAAAAAAAD/////7AAAAAH/////4AAAAAAAAAAAAAADP////8g",
"AAAAAO/////xAAAAAAAAAAAAAG/////4AAAAAABf////+gAAAAAAAAAAAADv////4QAAAAAAC/////8wAAAAAAAAAAAI/////2AAAAAAAAL/////wAAAAAAAAAAAL/////wAAAAAAAAAn/////YAAAAAAAAAAL//",
"///zAAAAAAAAAB7////+AAAAAAAAAAT/////oAAAAAAAAAAG/////4AAAAAAAAAN/////xAAAAAAAAAAAN/////yAAAAAAAAb/////gAAAAAAAAAAABP////+wAAAAAAAe/////gAAAAAAAAAAAAC/////9AAAAA",
"AAn/////UAAAAAAAAAAAAAL/////0AAAAAAv/////AAAAAAAAAAAAAAAj/////YAAAAAv/////MAAAAAAAAAAAAAAA7////+EAAABf////+QAAAAAAAAAAAAAAAG/////5AAAA3/////EAAAAAAAAAAAAAAAAM//",
"///yAAB/////9wAAAAAAAAAAAAAAAAA/////+wAB/////9AAAAAAAAAAAAAAAAAACv////9ACv////9AAAAAAAAAAAAAAAAAAAH/////0D/////7AAAAAAAAAAAAAAAAAAAAf/////fP////8gAAAAAAAAAAAAAA",
"AAAAAA3//////////4AAAAAAAAAAAAAAAAAAAAAF//////////4AAAAAAAAAAAAAAAAAAAAAAL/////////2AAAAAAAAAAAAAAAAAAAAAAAv////////wAAAAAAAAAAAAAAAAAAAAAAACf///////zAAAAAAAAAA",
"AAAAAAAAAAAAAAHv//////oAAAAAAAAAAAAAAAAAAAAAAAAAb//////xAAAAAAAAAAAAAAAAAAAAAAAAAA3/////cAAAAAAAAAAAAAAAAAAAAAAAAAAE/////gAAAAAAAAAAAAAAAAAAAAAAAAAAAL////UAAAAA",
"AAAAAAAAAB//////////////////////IAAf/////////////////////yAAH/////////////////////8gAB//////////////////////IAAf/////////////////////yAAH/////////////////////8g",
"AB//////////////////////IAAf/////////////////////yAAH////8AAAAAAAAAAAAAAAAAAAB/////AAAAAAAAAAAAAAAAAAAAf////wAAAAAAAAAAAAAAAAAAAH////8AAAAAAAAAAAAAAAAAAAB/////A",
"AAAAAAAAAAAAAAAAAAAf////wAAAAAAAAAAAAAAAAAAAH//////////////////zAAAAAB//////////////////8wAAAAAf//////////////////MAAAAAH//////////////////zAAAAAB//////////////",
"////8wAAAAAf//////////////////MAAAAAH//////////////////zAAAAAB//////////////////8wAAAAAf////wAAAAAAAAAAAAAAAAAAAH////8AAAAAAAAAAAAAAAAAAAB/////AAAAAAAAAAAAAAAAA",
"AAAf////wAAAAAAAAAAAAAAAAAAAH////8AAAAAAAAAAAAAAAAAAAB/////AAAAAAAAAAAAAAAAAAAAf/////////////////////yAAH/////////////////////8gAB//////////////////////IAAf////",
"/////////////////yAAH/////////////////////8gAB//////////////////////IAAf/////////////////////yAAH/////////////////////8gAE///////////////////+owAAAABP//////////",
"//////////+gAAAAT//////////////////////AAAAE//////////////////////+AAABP//////////////////////8QAAT///////////////////////cAAE///////////////////////6AABP//////",
"////////////////+wAAT////4AAAAAAAAAAAAAf////wAAE////+AAAAAAAAAAAAAH////8AABP////gAAAAAAAAAAAAB/////AAAT////4AAAAAAAAAAAAAf////wAAE////+AAAAAAAAAAAAAH////8AABP//",
"//gAAAAAAAAAAAAB/////AAAT////4AAAAAAAAAAAAAf////wAAE////+AAAAAAAAAAAAAH////8AABP//////////////////////+wAAT///////////////////////oAAE///////////////////////3AA",
"BP//////////////////////8QAAT//////////////////////5AAAE//////////////////////wAAABP////////////////////+gAAAAT///////////////////6kAAAAAE////+AAAAAAAv/////9gAA",
"AAAABP////gAAAAAAB3/////9AAAAAAAT////4AAAAAAAC//////4gAAAAAE////+AAAAAAAAE//////0AAAAABP////gAAAAAAAAH//////sAAAAAT////4AAAAAAAAAJ//////kAAAAE////+AAAAAAAAAAM//",
"////YAAABP////gAAAAAAAAAAe//////QAAAT////4AAAAAAAAAAA//////+IAAE////+AAAAAAAAAAABf/////7AABP////gAAAAAAAAAAAB//////AAAT////4AAAAAAAAAAAACv////wAAC////+gAAAAAAAA",
"AAAd////+QAAL////6AAAAAAAAAAAL/////5AAAv////oAAAAAAAAAAJ//////gAAC////+gAAAAAAAAAH//////0QAAL////6AAAAAAAAAE//////4gAAAv////oAAAAAAAAC//////9AAAAC////+gAAAAAAAB",
"3/////9gAAAAL////6AAAAAAAAz/////+QAAAAAv////oAAAAAAAr/////+wAAAAAC////+gAAAAAAf//////QAAAAAAL////6AAAAAAX//////iAAAAAAAv////oAAAAAP//////zAAAAAAAC////+gAAAAHv//",
"///1AAAAAAAAL////6AAAADf/////4AAAAAAAAAv///////////////6AAAAAAAAAC///////////////8AAAAAAAAAAL//////////////+EAAAAAAAAAAv//////////////MAAAAAAAAAAC//////////////",
"8wAAAAAAAAAAL//////////////+EAAAAAAAAAAv///////////////AAAAAAAAAAC////////////////oAAAAAAAAAL////6AAAADf/////4AAAAAAAAAv////oAAAAB7/////9QAAAAAAAC////+gAAAAA///",
"////MAAAAAAAL////6AAAAAAX//////hAAAAAAAv////oAAAAAAI//////0AAAAAAC////+gAAAAAACv/////7AAAAAAL////6AAAAAAAAz/////+AAAAAAv////oAAAAAAAAe//////YAAAAC////+gAAAAAAAA",
"L//////0AAAAL////6AAAAAAAAAE//////4gAAAv////oAAAAAAAAAB//////9EAAC////+gAAAAAAAAAAn/////+AAAL////6AAAAAAAAAAAL/////5AAAv////oAAAAAAAAAAAHf////kADP////9wAAAAAAAA",
"AAAAAL/////6Ae/////0AAAAAAAAAAAACP/////QAF/////+IAAAAAAAAAAAX/////8gAAn/////0AAAAAAAAAAC//////YAAADf////+gAAAAAAAAAN/////6AAAAAv/////3AAAAAAAACv/////QAAAAAG////",
"//QAAAAAAAf/////8wAAAAAAr/////4gAAAAAE//////cAAAAAAAHv/////QAAAAAu/////7AAAAAAAAA//////6AAAADf/////hAAAAAAAAAH//////cAAAr/////8wAAAAAAAAAAv/////9AAH//////cAAAAA",
"AAAAAAHv/////hBP/////7AAAAAAAAAAAABP/////8Lv/////hAAAAAAAAAAAAAH////////////9AAAAAAAAAAAAAAAv///////////gAAAAAAAAAAAAAAAHv/////////8AAAAAAAAAAAAAAAABP/////////i",
"AAAAAAAAAAAAAAAAAI////////9QAAAAAAAAAAAAAAAAAAz///////kAAAAAAAAAAAAAAAAAAAHv/////9AAAAAAAAAAAAAAAAAAAABP/////yAAAAAAAAAAAAAAAAAAAAAJ////9gAAAAAAAAAAAAAAAAAAAAAI",
"////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAA",
"AAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAAAAAAAAAAAAAAAAAI////9AAAAAAA",
"AAAAAAAAAAAAAAAI////9AAAAAAAAAAACBo2ANU/AABBABwA5xwZAAAAAEIAHADnHBleAQAAQwAcAOccGbwCAABEABwA5xwZGgQAAEUAGgDnGhl4BQAARgAZAOcZGb0GAABHABwA5xwZ9gcAAEgAHQDnHRlUCQAA",
"SQAHAOcIGb8KAABKABsA5xsZIwsAAEsAGwDnGxl1DAAATAAaAOcbGccNAABNACAA5yAZGQ8AAE4AHADnHBmpEAAATwAcAOccGQcSAABQABsA5xsZZRMAAFEAHgDnHhm3FAAAUgAcAOccGS4WAABTABwA5xwZjBcA",
"AFQAGgDnGhnqGAAAVQAcAOccGS8aAABWACIA5yIZjRsAAFcAKADnKBk2HQAAWAAcAOccGSofAABZABsA5x0ZiCAAAFoAHADnHBnzIQAAMAAcAOccGVEjAAAxAA0A5w4ZryQAADIAHADnHBleJQAAMwAcAOccGbwm",
"AAA0ABkA5xkZGigAADUAHADnHBlTKQAANgAcAOccGbEqAAA3ABYA5xYZDywAADgAHADnHBkiLQAAOQAcAOccGYAuAAAgAAsAAAsA3i8AAC8AEgDnEhneLwAALQASAPMSDb8wAAAuAAgA+wgFNDEAADoACADsCBRI",
"MQAALAAIAPsICpgxAAAhAAcA5wgZwDEAAD8AFwDnFxkkMgAAKAAKAOcKGUQzAAApAAoA5woZwTMAACUAIQDnIRk+NAAAKwAPAO8PEds1AADBABwA3xwhWzYAAMkAGgDfGiEpOAAAzQAHAN8JIdY5AADTABwA3xwh",
"azoAANoAHADfHCE5PAAA0QAcAN8cIQc+AAAAAEv//////////9gAAAAI/////////////9EAAE//////////////+wAAz///////////////IAD///////////////9gAP//8wAAAAAAAA7//3AA///zAAAAAAAA",
"Dv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA////////////////cAD///////////////9wAP///////////////3AA////",
"////////////cAD///////////////9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7/",
"/3AA///zAAAAAAAADv//cAD////////////9gQAAAP/////////////9IAAA///////////////AAAD///////////////QAAP//////////////9wAA///0AAAAAAAAz//4AAD///QAAAAAAADP//gAAP//9AAA",
"AAAAAM//+AAA///0AAAAAAAAz//4AAD///QAAAAAAADP//gAAP//////////////9wAA///////////////2AAD///////////////0AAP///////////////0AA////////////////cAD///QAAAAAAAAN//9w",
"AP//9AAAAAAAAA3//3AA///0AAAAAAAADf//cAD///QAAAAAAAAN//9wAP//9AAAAAAAAA3//3AA////////////////YAD///////////////8wAP//////////////+wAA///////////////RAAD/////////",
"////2AAAAABc/////////////1AACf//////////////UABf//////////////9QAN///////////////1AA////////////////UAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAH/",
"//IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAA",
"AAAAAAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAD///////////////9QAN///////////////1AAX///////////////UAAJ//////////////9QAABc/////////////1AA////",
"/////////9gAAAD//////////////9EAAP//////////////+wAA////////////////IAD///////////////9gAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7/",
"/3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAA",
"AAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP///////////////2AA////////////////IAD///////////////sAAP//////////////0QAA/////////////9gAAAD//////////////5AA",
"//////////////+QAP//////////////kAD//////////////5AA//////////////+QAP//9QAAAAAAAAAAAAD///UAAAAAAAAAAAAA///1AAAAAAAAAAAAAP//9QAAAAAAAAAAAAD///UAAAAAAAAAAAAA////",
"////////8wAAAP////////////MAAAD////////////zAAAA////////////8wAAAP////////////MAAAD///UAAAAAAAAAAAAA///1AAAAAAAAAAAAAP//9QAAAAAAAAAAAAD///UAAAAAAAAAAAAA///1AAAA",
"AAAAAAAAAP//////////////kAD//////////////5AA//////////////+QAP//////////////kAD//////////////5AA//////////////+QD//////////////5AP//////////////kA//////////////",
"+QD//////////////5AP//9QAAAAAAAAAAAA///1AAAAAAAAAAAAD///UAAAAAAAAAAAAP//9QAAAAAAAAAAAA///1AAAAAAAAAAAAD////////////zAAAP////////////MAAA////////////8wAAD///////",
"/////zAAAP////////////MAAA///1AAAAAAAAAAAAD///UAAAAAAAAAAAAP//9QAAAAAAAAAAAA///1AAAAAAAAAAAAD///UAAAAAAAAAAAAP//9QAAAAAAAAAAAA///1AAAAAAAAAAAAD///UAAAAAAAAAAAAP",
"//9QAAAAAAAAAAAA///1AAAAAAAAAAAAAABc///////////YAAAACf/////////////RAABf//////////////sAAN///////////////yAA////////////////UAH///IAAAAAAAAP//9gAf//8gAAAAAAAA//",
"/2AB///yAAAAAAAAAAAAAAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAH///IAAAAE//////9gAf//8gAAAAT//////2AB///yAAAABP//////YAH///IAAAAE//////9gAf//8gAA",
"AAT//////2AB///yAAAAAAAAD///YAH///IAAAAAAAAP//9gAf//8gAAAAAAAA///2AB///yAAAAAAAAD///YAD///////////////9QAN///////////////yAAX//////////////7AAAJ/////////////9EA",
"AABc///////////YAAAB///zAAAAAAAABf//4AAf//8wAAAAAAAAX//+AAH///MAAAAAAAAF///gAB///zAAAAAAAABf//4AAf//8wAAAAAAAAX//+AAH///MAAAAAAAAF///gAB///zAAAAAAAABf//4AAf//8w",
"AAAAAAAAX//+AAH///MAAAAAAAAF///gAB///zAAAAAAAABf//4AAf///////////////+AAH////////////////gAB////////////////4AAf///////////////+AAH////////////////gAB///zAAAAAA",
"AABf//4AAf//8wAAAAAAAAX//+AAH///MAAAAAAAAF///gAB///zAAAAAAAABf//4AAf//8wAAAAAAAAX//+AAH///MAAAAAAAAF///gAB///zAAAAAAAABf//4AAf//8wAAAAAAAAX//+AAH///MAAAAAAAAF//",
"/gAB///zAAAAAAAABf//4AAB///zAf//8wH///MB///zAf//8wH///MB///zAf//8wH///MB///zAf//8wH///MB///zAf//8wH///MB///zAf//8wH///MB///zAf//8wH///MB///zAf//8wH///MB///zAAAA",
"AAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAA",
"AAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kAAAAAAAAAAAAAC///kA3//2AAAAAAAAC///kA",
"3//2AAAAAAAAC///kA3//2AAAAAAAAC///kA3///////////////gAr///////////////UAP//////////////9AAB//////////////iAAADvv/////////+kQAAAB///zAAAAAAAF///5AB///zAAAAAAAv//",
"/4AB///zAAAAAAHf///iAB///zAAAAAAv///8wAB///zAAAAAI////YAAB///zAAAABf///5AAAB///zAAAAL///+wAAAB///zAAAB3///0QAAAB///zAAAL////IAAAAB///zAACP///0AAAAAB//////////9w",
"AAAAAB//////////oAAAAAAB//////////EAAAAAAB//////////oAAAAAAB//////////9wAAAAAB///zAACf///0AAAAAB///zAAAL////IAAAAB///zAAAB7///0QAAAB///zAAAAP///+wAAAB///zAAAABf",
"///5AAAB///zAAAAAI////YAAB///zAAAAAAv///8wAB///zAAAAAAHf///iAB///zAAAAAAAv///4AB///zAAAAAAAF///5AAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAA",
"AAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MA",
"AAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///MAAAAAAAAAAAAAH///////////////9gH///",
"////////////9gH///////////////9gH///////////////9gH///////////////9gAf//+wAAAAAAAAAI///2AAH///+QAAAAAAAAX///9gAB////9wAAAAAAA/////YAAf////9AAAAAAB7////2AAH/////",
"8gAAAADP////9gAB//////0QAAAK//////YAAf//////wAAAj//////2AAH///////oABf//////9gAB///8////cD////z///YAAf//88////bv///h7//2AAH///Id////////MO//9gAB///yAv//////9QDv",
"//YAAf//8gBP/////4AA7//2AAH///IABv////oAAO//9gAB///yAACf///AAADv//YAAf//8gAAC//+EAAA7//2AAH///IAAADf8wAAAO//9gAB///yAAAAHlAAAADv//YAAf//8gAAAAEAAAAA7//2AAH///IA",
"AAAAAAAAAO//9gAB///yAAAAAAAAAADv//YAAf//8gAAAAAAAAAA7//2AAH///IAAAAAAAAAAO//9gAB///yAAAAAAAAAADv//YAAf//8gAAAAAAAAAA7//2AAH///sAAAAAAAAP//9gAf///5AAAAAAAA///2AB",
"////9gAAAAAAD///YAH/////MAAAAAAP//9gAf/////hAAAAAA///2AB//////0AAAAAD///YAH//////6AAAAAP//9gAf//////+AAAAA///2AB///8////UAAAD///YAH///PP///zAAAP//9gAf//8h7///4Q",
"AA///2AB///yA////8AAD///YAH///IAX///+QAP//9gAf//8gAI////cA///2AB///yAAC////0D///YAH///IAAA3///4v//9gAf//8gAAAu///9///2AB///yAAAAT///////YAH///IAAAAG//////9gAf//",
"8gAAAACf/////2AB///yAAAAAAv/////YAH///IAAAAAAd////9gAf//8gAAAAAAL////2AB///yAAAAAAAE////YAH///IAAAAAAAB///9gAABc///////////WAAAACv////////////+wAABv////////////",
"//kAAO///////////////wAB////////////////QAL///EAAAAAAAAP//9AAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EA",
"AAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///",
"QAH///////////////9AAO///////////////wAAb//////////////5AAAK/////////////8AAAABs///////////XAAAB/////////////9cAAB///////////////AAB///////////////5AB//////////",
"//////EB////////////////UB///yAAAAAAAAD///YB///yAAAAAAAAD///YB///yAAAAAAAAD///YB///yAAAAAAAAD///YB///yAAAAAAAAD///YB///yAAAAAAAAD///YB///yAAAAAAAAD///YB////////",
"////////QB////////////////EB///////////////5AB//////////////+wAB/////////////8cAAB///yAAAAAAAAAAAAAB///yAAAAAAAAAAAAAB///yAAAAAAAAAAAAAB///yAAAAAAAAAAAAAB///yAA",
"AAAAAAAAAAAB///yAAAAAAAAAAAAAB///yAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAAAXP//////////1gAAAAAK/////////////7AAAABv//////////////gAAADv//////////////8AAAH/////////////",
"//8wAAL///EAAAAAAAAP//9AAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP",
"//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAL///EAAAAAAAAP//9QAAH/////////////",
"////8QDv////////////////8QBv////////////////8QAK////////////////8QAAbP//////////////8QL/////////////1wAAAv//////////////sAAC///////////////4AAL///////////////8A",
"Av///////////////0AC///yAAAAAAAAD///UAL///IAAAAAAAAP//9QAv//8gAAAAAAAA///1AC///yAAAAAAAAD///UAL///IAAAAAAAAP//9QAv//8gAAAAAAAA///1AC///yAAAAAAAAD///UAL/////////",
"//////9AAv///////////////wAC///////////////4AAL//////////////7AAAv/////////////XAAAC///yAAAAb///9wAAAAL///IAAAAJ////UAAAAv//8gAAAAC////zAAAC///yAAAAAA3///4QAAL/",
"//IAAAAAAu///9AAAv//8gAAAAAAP///+wAC///yAAAAAAAF////UAL///IAAAAAAACP//9QAAB9///////////GAAAADP////////////+wAACP//////////////kAAP///////////////wAD////////////",
"////IAT///AAAAAAAAAv//8wBP//8AAAAAAAAC///zAE///wAAAAAAAAAAAAAAT///AAAAAAAAAAAAAABP//8AAAAAAAAAAAAAAD/////////////8YAAAD//////////////7AAAI//////////////+AAADP//",
"///////////+AAAAff////////////8gAAAAAAAAAAAAAC///zAAAAAAAAAAAAAAL///MAAAAAAAAAAAAAAv//8wBP//8AAAAAAAAC///zAE///wAAAAAAAAL///MAP///////////////8gAf//////////////",
"/gAAr//////////////4AAAc/////////////7AAAAB9///////////GAABf///////////////yX///////////////8l////////////////Jf///////////////yX///////////////8gAAAAAAv//5AAAA",
"AAAAAAAAAL//+QAAAAAAAAAAAAC///kAAAAAAAAAAAAAv//5AAAAAAAAAAAAAL//+QAAAAAAAAAAAAC///kAAAAAAAAAAAAAv//5AAAAAAAAAAAAAL//+QAAAAAAAAAAAAC///kAAAAAAAAAAAAAv//5AAAAAAAA",
"AAAAAL//+QAAAAAAAAAAAAC///kAAAAAAAAAAAAAv//5AAAAAAAAAAAAAL//+QAAAAAAAAAAAAC///kAAAAAAAAAAAAAv//5AAAAAAAAAAAAAL//+QAAAAAAAAAAAAC///kAAAAAAAAAAAAAv//5AAAAAAAAAAAA",
"AL//+QAAAAAAAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///",
"UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAA",
"AAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///QAH///////////////9AAO///////////////wAAb//////////////5AAAK/////////////8AAAABs///////////XAAAI",
"///5AAAAAAAAAAAAB///+gDv//8gAAAAAAAAAAAe///xAG///7AAAAAAAAAAAJ///4AADf//9AAAAAAAAAAC///+AAAE///9AAAAAAAAAAv///YAAAC///9gAAAAAAAAT///wAAAAC///+EAAAAAAADf//9AAAAA",
"CP//+AAAAAAABv//+gAAAAAB7///IAAAAAAO///yAAAAAABv//+gAAAAAI///4AAAAAAAA3///MAAAAC///+AAAAAAAABP///AAAAAr///YAAAAAAAAAv///YAAAP///0AAAAAAAAAAv///gAADP//9AAAAAAAAA",
"AAn///gABf//+wAAAAAAAAAAAf///xAO///yAAAAAAAAAAAAf///oH///5AAAAAAAAAAAAAN///0///+EAAAAAAAAAAAAAX///////YAAAAAAAAAAAAAAL//////0AAAAAAAAAAAAAAAP/////9AAAAAAAAAAAAA",
"AAAJ////+wAAAAAAAAAAAAAAAAH////yAAAAAAAAAAAAAAAAAH///5AAAAAAAAAAAAAAAAAADv//EAAAAAAAAAr///AAAAAAC///gAAAAAAv//9wBP//9QAAAAAf///gAAAAAH///xAA7//7AAAAAG////MAAAAA",
"3//7AACf//8QAAAAz///+QAAAAP///YAAD///2AAAAL////+AAAACf//8AAADf//wAAAB/////9QAAAO//+gAAAH///yAAAN/////6AAAE///0AAAAL///cAAD//////8QAAr//+AAAAAM///QAAn//////2AAD/",
"//kAAAAAb///MADv//vv//wABf//8wAAAAAf//+QBP//9Y///yAL///gAAAAAAv//+AK///wL///cB///4AAAAAABf//9A///5AN///Qb///IAAAAAAA///6X///QAf///PP//0AAAAAAACv///P//4AAf//+///",
"9wAAAAAAAE//////+AAAv//////xAAAAAAAADv/////yAABv/////7AAAAAAAAAJ/////9AAAA//////YAAAAAAAAAP/////cAAACv////8QAAAAAAAAAN////8QAAAE////+gAAAAAAAAAAj///+wAAAADv///1",
"AAAAAAAAAAAv///2AAAAAJ///+AAAAAAAAAAAAz///AAAAAAP///kAAAAAAAAAAAB///oAAAAAAN//9AAAAAAAAAAAAB//9QAAAAAAj//gAAAAAAB///9wAAAAAAAM///wAG////QAAAAAAK////AADf///zAAAA",
"AI////gAAC7///4QAAAF////oAAABP///8AAAD////0AAAAAb///+gAC7///4QAAAAAJ////gA3///8wAAAAAADP///2v///9gAAAAAAAB7///////+AAAAAAAAAA///////+wAAAAAAAAAAX//////RAAAAAAAA",
"AAAI/////iAAAAAAAAAAAADv///3AAAAAAAAAAAACP////4gAAAAAAAAAABf/////9EAAAAAAAAAA///////+wAAAAAAAAAe////////kAAAAAAAAM////XP///2AAAAAAAJ////cB3///8wAAAAAH////oAAu//",
"/+IAAAAE////wAAAT////QAAAC7///0QAAAG////sAAA3///8gAAAACP///4AAb///9AAAAAAAv///8AB///9wAAAAAAAN///wAv///0AAAAAAAAA////zBf///iAAAAAAAB7///cACv///QAAAAAADP//+wAADf",
"//+gAAAAAJ///+EAAAP///9wAAAAX///9AAAAAf///9AAAAv///5AAAAAAz///4QAB3///0AAAAAAC7///wAC////yAAAAAAAF////oI////YAAAAAAAAJ////r///+gAAAAAAAAAN///////+EAAAAAAAAAAv//",
"////8wAAAAAAAAAABv/////4AAAAAAAAAAAACv////wAAAAAAAAAAAAAHv///xAAAAAAAAAAAAAAT///UAAAAAAAAAAAAAAB///zAAAAAAAAAAAAAAAf//8wAAAAAAAAAAAAAAH///MAAAAAAAAAAAAAAB///zAA",
"AAAAAAAAAAAAAf//8wAAAAAAAAAAAAAAH///MAAAAAAAAAAAAAAB///zAAAAAAAAAAAAAAAf//8wAAAAAAAAAAAAAAH///MAAAAAAAAE////////////////MAT///////////////8wBP///////////////zAE",
"////////////////MAT///////////////8wAAAAAAAAAAAH/////yAAAAAAAAAAAJ/////0AAAAAAAAAAAL/////jAAAAAAAAAAAc/////RAAAAAAAAAAAt////+xAAAAAAAAAAA+////+gAAAAAAAAAABf////",
"+AAAAAAAAAAAB/////9gAAAAAAAAAACf////9AAAAAAAAAAACv////4wAAAAAAAAAAHP////0gAAAAAAAAAALf////wQAAAAAAAAAAPv////oAAAAAAAAAAAX/////gAAAAAAAAAAAP/////YAAAAAAAAAAABP//",
"/////////////zAE////////////////MAT///////////////8wBP///////////////zAE////////////////MAAATP//////////swAAAAj/////////////YAAAT//////////////zAADP////////////",
"//oAAP///////////////gAA///yAAAAAAn/////AAH///IAAAABv/////8AAf//8gAAAC3//////wAB///yAAAE7///////AAH///IAAG////////8AAf//8gAI/////m///wAB///yAL/////BP///AAH///Id",
"////+gA///8AAf//9e////9wAD///wAB////////9QAAP///AAH///////4wAAA///8AAf//////wQAAAD///wAB//////oAAAAAP///AAH/////gAAAAAA///8AAP///////////////wAA///////////////9",
"AAC///////////////kAAD//////////////8gAABv////////////9QAAAAO///////////swAAAAAACP//9AAAAG////QAAAP////0AAAe////9AAAz/////QACv/////0AH//////9AX///////Qv///7///0",
"aIiIgf//9AAAAAD///QAAAAA///0AAAAAP//9AAAAAD///QAAAAA///0AAAAAP//9AAAAAD///QAAAAA///0AAAAAP//9AAAAAD///QAAAAA///0AAAAAP//9AAAAAD///QAAAAA///0AAAAAP//9AAAXP//////",
"////tAAAAAr/////////////cAAAb//////////////zAADf//////////////oAAP///////////////gAB///yAAAAAAAAP///AAH///IAAAAAAAA///8AAAAAAAAAAAAAAD///wAAAAAAAAAAAAAAP///AAAA",
"AAAAAAAAAAA///8AAAAAAAAAAAAAAD///wAAAFz////////////+AAAK//////////////oAAG//////////////8wAA3/////////////9wAAD/////////////tAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAA",
"AAAAAAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB////////////////AAH///////////////8AAf///////////////wAB////////////////AAH///////////////8AAABs//////////tAAAAAC///",
"//////////cAAACP/////////////zAAAP//////////////oAAC///////////////QAAP///AAAAAAAAT//+AAA///8AAAAAAABP//4AAAAAAAAAAAAAAE///gAAAAAAAAAAAAAAT//+AAAAAAAAAAAAAABP//",
"4AAAAAP////////////QAAAAA////////////8AAAAAD////////////8wAAAAP////////////6AAAAA/////////////0AAAAAAAAAAAAAAF///QAAAAAAAAAAAAAAX//9AAAAAAAAAAAAAABf//0AA///8AAA",
"AAAAAF///QAD///wAAAAAAAAX//9AAL///////////////wAAO//////////////+QAAf//////////////yAAAL/////////////1AAAABs//////////+zAAAAAAAAAAAAPv//EAAAAAAAAAAAT///8QAAAAAA",
"AAAAT////xAAAAAAAAAAX/////EAAAAAAAAAb/////8QAAAAAAAAf//////xAAAAAAAAj///////EAAAAAAAn///////8QAAAAAAr////7///xAAAAAAv////4L///EAAAABz////3Av//8QAAAB3////2AC///x",
"AAAC3////1AAL///EAAC7////0AAAv//8QAAz//////////////1DP//////////////UM//////////////9Qz//////////////1DP//////////////UAAAAAAAAAAv//8QAAAAAAAAAAAC///xAAAAAAAAAA",
"AAL///EAAAAAAAAAAAAv//8QAAAAAAAAAAAC///xAAAAAAAAAAAAL///EAAAAf///////////////wAB////////////////AAH///////////////8AAf///////////////wAB////////////////AAH///IA",
"AAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB/////////////7QAAAH//////////////4AAAf//////////////9AAB///////////////7",
"AAH///////////////4AAAAAAAAAAAAAAD///wAAAAAAAAAAAAAAP///AAAAAAAAAAAAAAA///8AAf//8gAAAAAAAD///wAA///yAAAAAAAAP///AAD///////////////4AAM//////////////+wAAX///////",
"///////0AAAJ/////////////4AAAABc//////////+0AAAAAFz//////////0AAAAAJ////////////QAAAAF////////////9AAAAAz////////////0AAAAD/////////////QAAAAf//8gAAAAAAAAAAAAAB",
"///yAAAAAAAAAAAAAAH///IAAAAAAAAAAAAAAf//8gAAAAAAAAAAAAAB///yAAAAAAAAAAAAAAH/////////////tAAAAf//////////////gAAB///////////////0AAH///////////////sAAf//////////",
"/////gAB///yAAAAAAAAP///AAH///IAAAAAAAA///8AAf//8gAAAAAAAD///wAB///yAAAAAAAAP///AAH///IAAAAAAAA///8AAP///////////////gAAz//////////////7AABf//////////////QAAAn/",
"////////////gAAAAFz//////////7QAAO//////////2BAA7///////////0QDv///////////7AO////////////8g7////////////2AAAAAAAAAADP//YAAAAAAAAAAM//9wAAAAAAAAAAz//3AAAAAAAAAA",
"DP//cAAAAAAAAAAM//9wAAAAAAAAAAz//3AAAAAAAAAADP//cAAAAAAAAAAM//9wAAAAAAAAAAz//3AAAAAAAAAADP//cAAAAAAAAAAM//9wAAAAAAAAAAz//3AAAAAAAAAADP//cAAAAAAAAAAM//9wAAAAAAAA",
"AAz//3AAAAAAAAAADP//cAAAAAAAAAAM//9wAAAAAAAAAAz//3AAAAAAAAAADP//cAAAAAAAAAAM//9wAABc///////////EAAAACf////////////9wAABf//////////////UAAM///////////////AAA////",
"////////////AAH///IAAAAAAAA///8AAf//8gAAAAAAAD///wAB///yAAAAAAAAP///AAH///IAAAAAAAA///8AAP//8gAAAAAAAD///wAA///////////////+AADP//////////////oAAJ//////////////",
"9wAA7//////////////8AAD///////////////8AAf//8gAAAAAAAD///wAB///yAAAAAAAAP///AAH///IAAAAAAAA///8AAf//8gAAAAAAAD///wAB///yAAAAAAAAP///AAD///////////////4AAM//////",
"////////+wAAX//////////////0AAAJ/////////////3AAAABc//////////+0AAAAAGz//////////7MAAAAK/////////////2AAAH//////////////8gAA7//////////////5AAH///////////////0A",
"Av//8QAAAAAAAF///QAC///xAAAAAAAAX//+AAL///EAAAAAAABf//4AAv//8QAAAAAAAF///gAC///xAAAAAAAAX//+AAH///////////////4AAO///////////////gAAf//////////////+AAAK////////",
"//////4AAABs/////////////gAAAAAAAAAAAAAAX//+AAAAAAAAAAAAAABf//4AAAAAAAAAAAAAAF///gAAAAAAAAAAAAAAX//+AAAAAAAAAAAAAABf//0AAf///////////////QAAz//////////////5AAA/",
"//////////////IAAAf/////////////YAAAAEz//////////7MAAAAAAAAAAAAI/AAAAAAAAABf/AAAAAAAAAL//AAAAAAAAB3//AAAAAAAAL///AAAAAAACP//+QAAAAAAX///wAAAAAAC///+EAAAAAAN///z",
"AAAAAAC///9gAAAAAAj///oAAAAAAF///8AAAAAAAv///hAAAAAADf//9AAAAAAAv///cAAAAAAI///6AAAAAABP///QAAAAAAL///4gAAAAAA3///QAAAAAAK///3AAAAAAAM//+gAAAAAAAM//0AAAAAAAAM/+",
"IAAAAAAAAM/0AAAAAAAAAM9wAAAAAAAAAAD/////////MAD/////////MAD/////////MAD/////////MAD/////////MAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAL///AC///wAv//8AL///AC///wAv//8AL///AC///wAv//8AL///AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAv//8AL///AC///wAv//8AL/",
"//AC///wAv//8AL///AC///wAv//8AL//+AC//+QAv/+EAL/4gAC1wAAAP//8gD///IA///yAP//8gD///IA///yAP//8gD///IA///yAP//8gD///IA///yAP//8gD///IA///yAP//8gD///IAqqqhAAAAAAAA",
"AAAA///yAP//8gD///IA///yAP//8g///////////8YAAP////////////sAD/////////////cA/////////////+AP/////////////yAAAAAAAAAAAP//8wAAAAAAAAAAD///MAAAAAAAAAAA///zAAAAAAAA",
"AAAP//8wAAAAAAAAAAD///MAAAAAAAAAAA///zAAAAGe////////8gAAA+/////////+AAAA3/////////9wAABf/////////7AAAAn////////8YAAAAK//+QAAAAAAAAAACv//kAAAAAAAAAAAr//5AAAAAAAA",
"AAAAAAAAAAAAAAAAAACv//kAAAAAAAAAAAr//5AAAAAAAAAAAK//+QAAAAAAAAAACv//kAAAAAAAAAAAr//5AAAAAAAAAAAAff/wAAv///AAj///8AD////wAv////AD///1QAP///AAA///8AAD///wAAP///AA",
"A///8AAD///wAAP///AAA///8AAD///wAAP///AAA///8AAD///wAAP///AAA///9UAC////8AD////wAI////AAC///8AAAff/wAf/8UAAB///5AAH///9gAf///9AB////8ABW///xAAL///EAAv//8QAC///x",
"AAL///EAAv//8QAC///xAAL///EAAv//8QAC///xAAL///EAAv//8QAC///xAAL///EAVv//8QH////wAf///9AB////YAH///kAAf/8UAAAAq7//8UAAAAAAAAAr5AAAAP/////9wAAAAAAAc/5AAAA3//////y",
"AAAAAALf/5AAAD///////3AAAAAD7//5AAAF//4ACv/5AAAABf///5AAAG//4ACv/6AAAAb////2AAAG//4ACv/6AAAI////9gAAAF//4ACv/5AACv////QAAAAD///////3ABz////jAAAAAA3//////yAt////",
"0QAAAAAAP/////9wPv///7EAAAAAAAAq7//8QE////+gAAAAAAAAAAAAAABv////gAAAAAAAAAAAAAAAj////2CN///XAAAAAAAAAK////9B3/////sAAAAAAAHP///+MJ//////9gAAAAAB3////SAO///////A",
"AAAAA+////wQAP//MAX//gAAAAT////6AAAf//MAX//gAAAE////+AAAAf//MAX//gAAAH////YAAAAP//MAX//gAAAH///1AAAAAO//////+wAAAH//4wAAAAAI//////9gAAAH/9IAAAAAAA3/////sAAAAH/B",
"AAAAAAAACO///XAAAAAAD///MAAAAAD///MAAAAAD///MAAAAAD///MAAG/////////G/////////G/////////G/////////G/////////AAAD///MAAAAAD///MAAAAAD///MAAAAAD///MAAAAAD///MAAAAA",
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAD///QAAAAAAAAAAAAABP//8AAAAAAAAAAAAAAI///AAAAAAAAAAAAAAAz//4AAAAAAAAAAAAAAD///QAAAAAAAAAAAAABP//8QAAAAAAAAAAAAAI///AAAAAAAAA",
"AAAAAAAAAAAAAAAAAAAAS///////////2AAAAAj/////////////0QAAT//////////////7AADP//////////////8gAP///////////////2AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAA",
"AA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///////////////9wAP///////////////3AA////////////////cAD///////////////9wAP//",
"/////////////3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO//9wAP//8wAAAAAAAA7//3AA///zAAAAAAAADv//cAD///MAAAAAAAAO",
"//9wAAAAAAAA7//3AAAAAAAAAAAAAf//8wAAAAAAAAAAAAX///AAAAAAAAAAAAAJ//+wAAAAAAAAAAAADf//cAAAAAAAAAAAAB///zAAAAAAAAAAAABf//8AAAAAAAAAAAAAAAAAAAAAAAAA//////////////+Q",
"AP//////////////kAD//////////////5AA//////////////+QAP//////////////kAD///UAAAAAAAAAAAAA///1AAAAAAAAAAAAAP//9QAAAAAAAAAAAAD///UAAAAAAAAAAAAA///1AAAAAAAAAAAAAP//",
"//////////MAAAD////////////zAAAA////////////8wAAAP////////////MAAAD////////////zAAAA///1AAAAAAAAAAAAAP//9QAAAAAAAAAAAAD///UAAAAAAAAAAAAA///1AAAAAAAAAAAAAP//9QAA",
"AAAAAAAAAAD//////////////5AA//////////////+QAP//////////////kAD//////////////5AA//////////////+QAC///yAG///gAK//+gAO//9gAv//8gBv//4ACv//oAAAAAAACP//wACP//wACP//",
"wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wACP//wAAAAAAAAAAN//9wAAAAAAAAAAAA",
"AB///0AAAAAAAAAAAAAAX///AAAAAAAAAAAAAACf//wAAAAAAAAAAAAAAN//+AAAAAAAAAAAAAAB///0AAAAAAAAAAAAAAX///AAAAAAAAAAAAAAAAAAAAAAAAAAAABc///////////WAAAACv////////////+w",
"AABv//////////////kAAO///////////////wAB////////////////QAL///EAAAAAAAAP//9AAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAA",
"AAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC",
"///xAAAAAAAAD///QAH///////////////9AAO///////////////wAAb//////////////5AAAK/////////////8AAAABs///////////XAAAAAAAAAACP//0AAAAAAAAAAAAAAL//+QAAAAAAAAAAAAAA///1",
"AAAAAAAAAAAAAAP///EAAAAAAAAAAAAAB///0AAAAAAAAAAAAAAL//+QAAAAAAAAAAAAAA///1AAAAAAAAAAAAAAAAAAAAAAAAAAAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//",
"8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP",
"//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///UAL///EAAAAAAAAP//9QAv//8QAAAAAAAA///1AC///xAAAAAAAAD///QAH/////",
"//////////9AAO///////////////wAAb//////////////5AAAK/////////////8AAAABs///////////XAAAAAAABfP6jAAAAAAAAAAAAAAj////FADswAAAAAAAACP///////zAAAAAAAAAI////////MAAA",
"AAAAAAdxAX7///8wAAAAAAAAAAAAAGz/tgAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf//+wAAAAAAAA///2AB////kAAAAAAAD///YAH////2AAAAAAAP//9gAf////8wAAAAAA///2AB/////+EA",
"AAAAD///YAH//////QAAAAAP//9gAf//////oAAAAA///2AB///////4AAAAD///YAH///z///9QAAAP//9gAf//88////MAAA///2AB///yHv///hAAD///YAH///ID////wAAP//9gAf//8gBf///5AA///2AB",
"///yAAj///9wD///YAH///IAAL////QP//9gAf//8gAADf///i///2AB///yAAAC7///3///YAH///IAAABP//////9gAf//8gAAAAb//////2AB///yAAAAAJ//////YAH///IAAAAAC/////9gAf//8gAAAAAB",
"3////2AB///yAAAAAAAv////YAH///IAAAAAAAT///9gAf//8gAAAAAAAH///2AMIwwAOhcAADAAJgDfJiEAAAAAMQASAN8SIXMCAAAyACYA3yYhnAMAADMAJgDfJiEPBgAANAAiAN8iIYIIAAA1ACYA3yYhswoA",
"ADYAJgDfJiEmDQAANwAeAN8eIZkPAAA4ACYA3yYhiBEAADkAJgDfJiH7EwAALQAYAO8YEW4WAAAgAA8AAA8AOhcAAAAAAEvv/////////////pMAAAAAAAv/////////////////gAAAAAC/////////////////",
"//gAAAAH////////////////////MAAADv///////////////////7AAAD/////////////////////wAABf////////////////////8QAAb///+gAAAAAAAAT///////IAAG////oAAAAAAAB////////yAABv",
"///6AAAAAAAJ////////8gAAb///+gAAAAABz/////////IAAG////oAAAAALf/////////yAABv///6AAAABP//////////8gAAb///+gAAAG//////4+////IAAG////oAAAn//////RDv///yAABv///6AAC/",
"/////7AA7///8gAAb///+gAt//////gAAO////IAAG////oD7/////9gAADv///yAABv///6b//////jAAAA7///8gAAb////v/////9IAAAAO////IAAG//////////sQAAAADv///yAABv////////+QAAAAAA",
"7///8gAAb////////2AAAAAAAO////IAAG////////QAAAAAAADv///yAABv//////0gAAAAAAAA7///8gAAX/////////////////////IAAF/////////////////////xAAAv////////////////////4AAA",
"Df///////////////////5AAAAX///////////////////8gAAAAn//////////////////2AAAAAAn/////////////////YAAAAAAAOu/////////////9kgAAAAAAAAAAz////wAAAAAK/////wAAAAB/////",
"/wAAAAX//////wAAAD///////wAAAe///////wAADP///////wAAr////////wAI/////////wBv/////////wP//////////y7/////X////2mZmZmVH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAA",
"AAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAAAA",
"H////wAAAAAAH////wAAAAAAH////wAAAAAAH////wAAAEvv/////////////pMAAAAAAAv/////////////////gAAAAADP//////////////////kAAAAH////////////////////QAAADv//////////////",
"/////7AAAD/////////////////////wAABf////////////////////8QAAb///+gAAAAAAAAAAAO////IAAG////oAAAAAAAAAAADv///yAABv///6AAAAAAAAAAAA7///8gAAAAAAAAAAAAAAAAAAAO////IA",
"AAAAAAAAAAAAAAAAAADv///yAAAAAAAAAAAAAAAAAAAA7///8gAAAAAAAAAAAAAAAAAAAO////IAAAAAW+/////////////////xAAAAHP//////////////////8AAAAN///////////////////7AAAAn/////",
"//////////////8wAAAP///////////////////5AAAAT///////////////////gAAAAF/////////////////+owAAAABv///6AAAAAAAAAAAAAAAAAAAAb///+gAAAAAAAAAAAAAAAAAAAG////oAAAAAAAAA",
"AAAAAAAAAABv///6AAAAAAAAAAAAAAAAAAAAb///+gAAAAAAAAAAAAAAAAAAAG/////////////////////yAABv////////////////////8gAAb/////////////////////IAAG/////////////////////y",
"AABv////////////////////8gAAb/////////////////////IAAG/////////////////////yAAAAAGzv////////////xxAAAAAAAC3////////////////kAAAAAAHv/////////////////zAAAAAK////",
"///////////////QAAAAH///////////////////9QAAAG////////////////////kAAACP///////////////////7AAAAn///9wAAAAAAAAAAX///+wAAAJ////cAAAAAAAAAAF////sAAACf///3AAAAAAAA",
"AABf///7AAAAAAAAAAAAAAAAAAAAX///+wAAAAAAAAAAAAAAAAAAAF////sAAAAAAAAAAAAAAAAAAABf///7AAAAAAAC////////////////+wAAAAAAAv////////////////kAAAAAAAL////////////////5",
"AAAAAAAC/////////////////yAAAAAAAv////////////////+QAAAAAAL/////////////////0AAAAAAC//////////////////AAAAAAAAAAAAAAAAAAAAH////wAAAAAAAAAAAAAAAAAAAB////8AAAAAAA",
"AAAAAAAAAAAAAf////AAAAAAAAAAAAAAAAAAAAH////wAACf///3AAAAAAAAAAAB////8AAAn///9wAAAAAAAAAAAf////AAAI/////////////////////gAAB/////////////////////0AAAP///////////",
"/////////4AAAAz///////////////////8gAAAC7//////////////////2AAAAAD3/////////////////cAAAAAAAbP/////////////9kgAAAAAAAAAAAAAAAACv///yAAAAAAAAAAAAAAAAC/////IAAAAA",
"AAAAAAAAAAHP////8gAAAAAAAAAAAAAALf/////yAAAAAAAAAAAAAAPv//////IAAAAAAAAAAAAAT///////8gAAAAAAAAAAAAX////////yAAAAAAAAAAAAb/////////IAAAAAAAAAAAj/////////8gAAAAAA",
"AAAAn//////////yAAAAAAAAAAr///////////IAAAAAAAABz//////37///8gAAAAAAAB3//////1Dv///yAAAAAAAC3//////jAO////IAAAAAAD7//////BAA7///8gAAAAAE//////+gAADv///yAAAAAF//",
"////+AAAAO////IAAAAG//////9QAAAA7///8gAAAH////////////////////kAv///////////////////+QC////////////////////5AL////////////////////kAv///////////////////+QC/////",
"///////////////5AL////////////////////kAAAAAAAAAAAAAAO////IAAAAAAAAAAAAAAAAA7///8gAAAAAAAAAAAAAAAADv///yAAAAAAAAAAAAAAAAAO////IAAAAAAAAAAAAAAAAA7///8gAAAAAAAAAA",
"AAAAAADv///yAAAAAAAAAAAAAAAAAO////IAAAAAAAAAAAAAAAAA7///8gAAAABv////////////////////8gAAb/////////////////////IAAG/////////////////////yAABv////////////////////",
"8gAAb/////////////////////IAAG/////////////////////yAABv////////////////////8gAAb///+gAAAAAAAAAAAAAAAAAAAG////oAAAAAAAAAAAAAAAAAAABv///6AAAAAAAAAAAAAAAAAAAAb///",
"+gAAAAAAAAAAAAAAAAAAAG////oAAAAAAAAAAAAAAAAAAABv///6AAAAAAAAAAAAAAAAAAAAb/////////////////6jAAAAAG///////////////////5AAAABv///////////////////6AAAAb///////////",
"/////////1AAAG/////////////////////AAABv////////////////////8AAAb/////////////////////EAAAAAAAAAAAAAAAAAAADv///yAAAAAAAAAAAAAAAAAAAA7///8gAAAAAAAAAAAAAAAAAAAO//",
"//IAAAAAAAAAAAAAAAAAAADv///yAABv///6AAAAAAAAAAAA7///8gAAb///+gAAAAAAAAAAAO////IAAF/////////////////////xAABP////////////////////8AAAD////////////////////8AAAAn/",
"//////////////////9QAAAA3//////////////////6AAAAABz/////////////////kAAAAAAAW+/////////////+owAAAAAAAFvv/////////////yAAAAAAABv///////////////8gAAAAAADP////////",
"////////IAAAAAAI/////////////////yAAAAAAD/////////////////8gAAAAAE//////////////////IAAAAABf/////////////////yAAAAAAb///+gAAAAAAAAAAAAAAAAAAAG////oAAAAAAAAAAAAA",
"AAAAAABv///6AAAAAAAAAAAAAAAAAAAAb///+gAAAAAAAAAAAAAAAAAAAG////oAAAAAAAAAAAAAAAAAAABv///6AAAAAAAAAAAAAAAAAAAAb/////////////////6jAAAAAG///////////////////5AAAABv",
"///////////////////6AAAAb////////////////////1AAAG/////////////////////AAABv////////////////////8AAAb/////////////////////EAAG////oAAAAAAAAAAADv///yAABv///6AAAA",
"AAAAAAAA7///8gAAb///+gAAAAAAAAAAAO////IAAG////oAAAAAAAAAAADv///yAABv///6AAAAAAAAAAAA7///8gAAb///+gAAAAAAAAAAAO////IAAF/////////////////////xAABP////////////////",
"////8AAAD////////////////////8AAAAj///////////////////9QAAAAz//////////////////6AAAAABv/////////////////kAAAAAAAW+/////////////+owAAAN//////////////xwAAAN//////",
"/////////+MAAN////////////////8gAN/////////////////AAN/////////////////zAN/////////////////4AN/////////////////5AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAA",
"AAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAA",
"AAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAA",
"AAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAAAAAAAAAABv///6AAAAAFvv",
"/////////////qQAAAAAABv/////////////////oAAAAADP//////////////////sAAAAI////////////////////YAAAD////////////////////9AAAE/////////////////////xAABf////////////",
"////////8gAAb///+gAAAAAAAAAAAO////IAAG////oAAAAAAAAAAADv///yAABv///6AAAAAAAAAAAA7///8gAAb///+gAAAAAAAAAAAO////IAAG////oAAAAAAAAAAADv///yAABv///6AAAAAAAAAAAA7///",
"8gAAX/////////////////////EAAD/////////////////////wAAAO////////////////////oAAAC////////////////////3AAAB/////////////////////QAABP////////////////////8AAAX///",
"//////////////////IAAG////oAAAAAAAAAAADv///yAABv///6AAAAAAAAAAAA7///8gAAb///+gAAAAAAAAAAAO////IAAG////oAAAAAAAAAAADv///yAABv///6AAAAAAAAAAAA7///8gAAb///+gAAAAAA",
"AAAAAO////IAAF/////////////////////xAABP////////////////////8AAAD////////////////////7AAAAj///////////////////9AAAAAz//////////////////5AAAAABv/////////////////",
"kAAAAAAAW+/////////////+owAAAAAAAGzv/////////////ZIAAAAAAC3/////////////////cAAAAAHv//////////////////cAAAAL////////////////////IAAAL////////////////////5AAAG//",
"///////////////////QAAB/////////////////////8AAAj///+QAAAAAAAAAAAP////AAAI////kAAAAAAAAAAAD////wAACP///5AAAAAAAAAAAA////8AAAj///+QAAAAAAAAAAAP////AAAI////kAAAAA",
"AAAAAAD////wAACP///5AAAAAAAAAAAA////8AAAf/////////////////////AAAG/////////////////////wAAAf////////////////////8AAACv////////////////////AAAAHv////////////////",
"///wAAAALf//////////////////8AAAAABs7/////////////////AAAAAAAAAAAAAAAAAAAAD////wAAAAAAAAAAAAAAAAAAAA////8AAAAAAAAAAAAAAAAAAAAP////AAAAAAAAAAAAAAAAAAAAD////wAAAA",
"AAAAAAAAAAAAAAAA////8AAAAAAAAAAAAAAAAAAAAP////AAAI/////////////////////wAABP////////////////////0AAADf///////////////////5AAAAX///////////////////8gAAAAn///////",
"///////////3AAAAAAn/////////////////cAAAAAAAS+/////////////+kgAAAABP///////////+AABP///////////+AABP///////////+AABP///////////+AABP///////////+AABP///////////+",
"AABP///////////+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
"AAAAAAAAAAAAAAAAAAQMcwAnFwAAIAAFAAAFAAAAAAAhAAMA9QMLAAAAACIABgD1BgsRAAAAIwAMAPUMCzIAAAAkAAwA9AwOdAAAACUADgD1DgvIAAAAJgAOAPUOCxUBAAAnAAMA9QMLYgEAACgABAD1BAtzAQAA",
"KQAEAPUEC4kBAAAqAAcA9QgLnwEAACsABgD5BwfLAQAALAADAP4DBOQBAAAtAAgA+wgF6gEAAC4AAwD+AwL+AQAALwAIAPUICwECAAAwAA0A9Q0LLQIAADEABgD1Bgt1AgAAMgAMAPUMC5YCAAAzAAwA9QwL2AIA",
"ADQACwD1CwsaAwAANQAMAPUMC1cDAAA2AAwA9QwLmQMAADcACgD1CgvbAwAAOAANAPUNCxIEAAA5AAwA9QwLWgQAADoAAwD3AwmcBAAAOwADAPcDC6oEAAA8AAcA9wcJuwQAAD0ACgD5CgfbBAAAPgAHAPcICf4E",
"AAA/AAoA9QoLIgUAAEAADAD1DAtZBQAAQQANAPUNC5sFAABCAAwA9QwL4wUAAEMADAD1DAslBgAARAANAPUNC2cGAABFAAsA9QsLrwYAAEYACwD1CwvsBgAARwAMAPUMCykHAABIAA0A9Q0LawcAAEkAAwD1Awuz",
"BwAASgAMAPUMC8QHAABLAAwA9QwLBggAAEwADAD1DAtICAAATQAOAPUOC4oIAABOAAwA9QwL1wgAAE8ADAD1DAsZCQAAUAAMAPUMC1sJAABRAA0A9Q0LnQkAAFIADAD1DAvlCQAAUwAMAPUMCycKAABUAAsA9QwL",
"aQoAAFUADAD1DAurCgAAVgAPAPUPC+0KAABXABIA9RILQAsAAFgADAD1DAujCwAAWQAMAPUNC+ULAABaAAwA9QwLLQwAAFsABAD1BAtvDAAAXAAIAPUIC4UMAABdAAQA9QQLsQwAAF8ADAAADALHDAAAYAADAPEE",
"D9MMAABhAAoA9woJ8QwAAGIACgD0CgweDQAAYwAKAPcKCVoNAABkAAoA9AoMhw0AAGUACgD3CgnDDQAAZgAHAPQHDPANAABnAAoA9woMGg4AAGgACgD0CgxWDgAAaQAEAPQEDJIOAABqAAT99AcPqg4AAGsACgD0",
"CgzfDgAAbAAFAPQFDBsPAABtAA8A9w8JOQ8AAG4ACgD3Cgl9DwAAbwAKAPcKCaoPAABwAAoA9woM1w8AAHEACgD3CgwTEAAAcgAIAPcICU8QAABzAAoA9woJcxAAAHQABwD0BwygEAAAdQAKAPcKCcoQAAB2AAwA",
"9wwJ9xAAAHcAEAD3EAktEQAAeAAKAPcKCXURAAB5AAoA9woMohEAAHoACgD3CgneEQAAewAEAPUECwsSAAB8AAMA9AMOIRIAAH0ABAD1BQs2EgAAfgAGAPsGBVISAADhAAsA8wsNYRIAAOkACgDzCg2pEgAA7QAD",
"APMEDeoSAADzAAoA8woNBBMAAPoACgDzCg1FEwAAwQANAPEND4YTAADJAAsA8QsP6BMAAM0AAwDxBA87FAAA0wAMAPEMD1kUAADaAAwA8QwPsxQAAPEACwD0CwwNFQAA0QAMAPIMDk8VAAD8AAoA9AoMoxUAANwA",
"DADyDA7fFQAAvwAKAPUKCzMWAAChAAMA9QMLahYAALAABwD1Bwt7FgAAJiAJAP4JAqIWAAATIAsA+wsFqxYAABQgDAD7DAXHFgAArCAMAPUMC+UWAAAv0v0v0v0v0v0v0dsAAv0v0B/b9B/b9B/b9AAAAAAAAAAA",
"AAAAAAAAAAAAAAAAAAAAAAAAzzAv0AAC/QCPYB//////9R//////9QAf0Af3AABfkAvzAACPkx/wAI//////4I//////4Af4AN8QAA3yA/wAAAAAL9AAAAn////+YF//////8X9wL9AM839wL9AAAH9wL9AAAF//",
"///+YAn/////8QAAL9AM839wL9AM81//////8Qr////+cAAAL9AAAAAAL9AAAAbv5AAAB5Af//4AAJ+QT2CPIAv/QE9gjyHf4wAf//8+/RAABu/p/7AAAAAAb/k9/6AACP9wz//2AK/1AOwC+AH+MADP//YB0gAA",
"Pf+gAL////5QAAj/////8AAK9QAADvEACvUAAAAAAAn+YAAAAAAf//5gA4QAP8Kv/mf3AD/AAq//9wA/wAADv/9wH///////9Qbv////opQf0f0f0AAAAAAAAAAAAAAAAAbqH/o/wD/AP8A/wD/AP8A/wB/6Buov",
"sS/5BPsE+wT7BPsE+wT7BPsv+S+xAD/AAAVPwkBf///gXf//sQL/+gAL+/9AArFoAAAAAAAAAAAAAAAAAAAAAAAAv0AAC/QAz///bP//9gC/QAAL9AAAAAAAP8P8P5KxH///8B////AAAAAAAAAAAAAAAAA/w/wA",
"AAArAAAB3AAAC/cAAJ+gAAb9AAA/4gAB70AADPcAAK+gAADsAAAAwQAAAAXv////oAD//////2Av0AABz/gC/QAC3/+AL9AE78j4Av0G/7BvgC/Y/5AG+AL//3AAb4Av/1AABvgA//////9gBe////+gAAA/9wHv",
"9wz/95/Z9wAI9wAI9wAI9wAI9wAI9wAI9wAI9wXv////oA//////9S/QAAAG+AAAAAAG+AAAAAAG+Abv////9g//////oC/QAAAAAC/QAAAAAC//////+C//////+Abv///+QB//////4D/AAAAO8AAAAAAO8QBf",
"////8ABf////8gAAAAAH9wAAAAAH9z/AAAAH9x//////9QXv////kAAAAI/QAAAAr/0AAAC//9AAAc/4/QAC7+Mf0APvsQH9AO//////Xv/////1AAAAH9AAAAAB/QAAAAAf0AAv//////gv//////gv0AAAAAAv",
"0AAAAAAv/////6Av//////UAAAAABvgAAAAABvgv0AAABvgP//////YF7////6AF7////QAP/////QAv0AAAAAAv0AAAAAAv/////6Av//////Uv0AAABvgv0AAABvgv0AAABvgP//////YF7////6D////9QP//",
"///gAAAAD/AAAAAP8AAAAA/wAAAAD/AAAAAP8AAAAA/wAAAAD/AAAAAP8AAAAA/wBe////+gAP//////cC/QAAAG+AL9AAAAb4Af0AAABvgA//////9QL//////4Av0AAABvgC/QAAAG+AD//////2AF7////6AA",
"Bu////+QH//////1P8AAAAf3P8AAAAf3P8AAAAf3H//////3Bu/////3AAAAAAf3AAAAAAf3H//////1Be////+QP8P8AAAAAAAAAAP8P8A/s/sAAAAAAAAAA9k/s/k7EAAACFAAXvUDz/sp/9UA79AACf/VAAPP",
"/CAAXvUAAAhQH////7Af////sAAAAAAAH////7Af////sAAAAAAAAAAAAAAaEAAAH/gAAAn/5QAAPP/BAACv8wA8/8EJ/+UAH/cAABoQAACP////wo/////6AAAAAv0AAAAC/QAAAAL9AE3///oA7///wgD/AAAA",
"AAAAAAAA/wAAAAD/AAAABe////+gD//////2L9AAAAb4L9CP/Cb4L9P//6b4L9XyDMb4L9P////4L9CP///4L9AAAAAAD//////4Be/////4Be////+xAP//////gB/QAAAF+gL9AAAAX6Av0AAABfoC//////+g",
"L//////6Av0AAABfoC/QAAAF+gL9AAAAX6Av0AAABfoAH/////5gH//////xH9AAAAzzH9AAAAz0H//////zH//////1H9AAAAX6H9AAAAX7H9AAAAX6H//////4H/////+xBe/////5D//////5L9AAAAAAL9AA",
"AAAAL9AAAAAAL9AAAAAAL9AAAAAAL9AAAAAAL9AAAAAAD//////5Be/////5L/////+xAv//////gC/QAAAF+gL9AAAAX6Av0AAABfoC/QAAAF+gL9AAAAX6Av0AAABfoC/QAAAF+gL//////4Av/////7EAL///",
"///C//////wv0AAAAAL9AAAAAC/QAAAAAv////9AL/////QC/QAAAAAv0AAAAAL//////C//////wC//////wv/////8L9AAAAAC/QAAAAAv0AAAAAL/////QC/////0Av0AAAAAL9AAAAAC/QAAAAAv0AAAAAAF",
"7////7AP//////cv0AAABfov0AAAAAAv0AAAAAAv0AAM//ov0AAM//ov0AAABfov0AAABfoP//////gF7////7Ev0AAAAf4C/QAAAB/gL9AAAAH+Av0AAAAf4C/QAAAB/gL//////+Av//////4C/QAAAB/gL9AA",
"AAH+Av0AAAAf4C/QAAAB/gAv0v0v0v0v0v0v0v0v0v0v0AAAAAAv0AAAAAAv0AAAAAAv0AAAAAAv0AAAAAAv0AAAAAAv0AAAAAAv0AAAAAAv0P8AAAAv0N//////sE3////8IC/QAABP8i/QAAHvcC/QAAz6AC/Q",
"AH/AAC/QA/4QAC////YAAC////4QAC/QA//AAC/QAD/6AC/QAAT/cC/QAABf8i/QAAAAAC/QAAAAAC/QAAAAAC/QAAAAAC/QAAAAAC/QAAAAAC/QAAAAAC/QAAAAAC/QAAAAAC//////+i//////+i/2AAAAn/Av",
"/0AABv/wL//yAE//8C/b/RLvj/Av0N/N+w/wL9Ae/9AP8C/QA/4QD/Av0ABTAA/wL9AAAAAP8C/QAAAAD/Av0AAAAA/wL/YAAAX6L/9AAAX6L//iAAX6L9v9AAX6L9DfsAX6L9Au+AX6L9AE/1X6L9AAb/n6L9AA",
"Cf/6L9AAAL/6L9AAAB36Bu////+gH//////3L8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5L8AAAAb5H//////3Bu////+wL/////+xL//////4L9AAAAX6L9AAAAX6L9AAAAX6L//////4L///",
"//+wL9AAAAAAL9AAAAAAL9AAAAAAL9AAAAAABu////+gAf//////cC/AAAAG+QP8AAAAb5A/wAAABvkD/AAAAG+QP8AAAAb5A/wAAABvkC/AAAAG+QH///////4G7//////gL/////+wL//////3L9AAAAb5L9AA",
"AAb6L9AAAAb5L//////3L/////+wL9AAT/UAL9AAB/8gL9AAAL/QL9AAAB34Bu////+gH//////2P8AAAAf4P8AAAAAAP8AAAAAAH/////+wBu/////3AAAAAAf5P8AAAAf5H//////3Bu////+wv//////xv///",
"///xAABPsAAAAABPsAAAAABPsAAAAABPsAAAAABPsAAAAABPsAAAAABPsAAAAABPsAAAAABPsAAAP8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5L8AAAAb5H//////3Bu//",
"//+wP/IAAAAAz4CfoAAAAF/gAf8wAAAO9gAH/AAAB/wAAA71AAH/MAAAX+AAn6AAAADPcC/yAAAAA/8b+AAAAAAK/f4AAAAAAB//YAAAAAAAj9AAAABPwAAF/gAAL+AO8gAL/1AAj4AJ+AAf/6AA7zAD/gBvz/EE",
"/QAA3zDPW/YJ9wAAj5L/BfwP8gAAL+j5AP9/wAAADP/0AK//YAAAB//gAE//EAAAAf+AAA77AAAAAL8gAAn1AAA/9AAAL/YI/yAB36AAr+EM/AAADfyv4QAAAu//MAAAAG/5AAAAAu//MAAADfyv4QAAr+EM/AAI",
"/yAB36A/9AAAL/Zv4QAACP0Ar8AABf8gAe+QAv9gAAP/YN+gAAAH/8/hAAAAC//0AAAAAB74AAAAAADPMAAAAAAM8wAAAAAAzzAAAAAADPMAAAA///////k///////kAAAABz/QAAAAu/iAAAAT/wQAAAG/6AAAA",
"CP+AAAAAr/YAAAAc/0AAAAA///////k///////k/+z/7P8A/wD/AP8A/wD/AP8A/+z/70QAAAOwAAACvkAAADPYAAAHvQAAAP+IAAAb9AAAAn6AAAAz3AAAB7AAAADs/+j/6BfoF+gX6BfoF+gX6Bfo/+j/6P///",
"///4P//////4b5Av0A7xAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////6A/////9wAAAAX5AAAABfk/////+T/////5P8AABfkf////+Qfv///5P8AAAAA/wAAAAD/AAAAAP////7A/////9z/AAAX6P8AABfo/",
"wAAF+j/AAAX6P8AABfo/////9z////+wBu////kf////+T+wAAAAP7AAAAA/sAAAAD+wAAAAP7AAAAAf////+Qbv///5AAAADPMAAAAM8wAAAAzzC/////OP////869QAAzzr1AADPOvUAAM869QAAzzr1AADPOP",
"////8xv////zBu///6Af////9j+wAAX5P7AABfk/////+T/////5P7AAAAAf////+Qbv///5Bu//If//8j/AAAP///I///8j/AAAP8AAA/wAAD/AAAP8AAA/wAAD/AAACP///5A/////9W+QAAj3b5AACPdvkAAI",
"92+QAAj3b5AACPdP////9wj////3AAAACPcA////9QD///+QP8AAAAA/wAAAAD/AAAAAP////7A/////9z/AAAX6P8AABfo/wAAF+j/AAAX6P8AABfo/wAAF+j/AAAX6P8A/wAAAK4A/wD/AP8A/wD/AP8A/wD/A",
"AAD/AAAP8AAAAAAAD/AAAP8AAA/wAAD/AAAP8AAA/wAAD/AAAP8AAA/wAAD/Df//4N//1AA/wAAAAD/AAAAAP8AAAAA/wAAEUz/AAG/zP8AF/1A/wE/2AD///3AAP///kAA/wD/5AD/AA++AP8AALvY/wAP8AD/A",
"A/wAP8AD/AA/wAP8AD/AA/wAH/+Qbvk///////+xA////////4A/wADPMAT6A/wADPMAT6A/wADPMAT6A/wADPMAT6A/wADPMAT6A/wADPMAT6A/wADPMAT6AD////+wP/////c/wAAF+j/AAAX6P8AABfo/wAAF",
"+j/AAAX6P8AABfo/wAAF+gbv//+gH/////c/sAAF+T+wAAX5P7AABfk/sAAF+T+wAAX5H/////cG7///oD////+wP/////c/wAAF+j/AAAX6P8AABfo/wAAF+j/AAAX6P/////c/////sD/AAAAAP8AAAAA/wAAA",
"ABv////yj/////K/QAAN8r9AAA3yv0AADfK/QAAN8r9AAA3yn/////Ib////8gAAAA3yAAAADfIAAAAN8gbv//sf///7P8AAAD/AAAA/wAAAP8AAAD/AAAA/wAAAP8AAAAbv//+xH/////hPsAAAAE+wAAAAH///",
"/7AG7///9wAAAAb5P/////cJ////sD/AAAP8AAA/wAAD///yP///I/wAAD/AAAP8AAA/wAAD/AAAH///IG7/8j/AAAX6P8AABfo/wAAF+j/AAAX6P8AABfo/wAAF+j/AAAX5H/////cG7///sG/QAAAN9g31AABf",
"4AX9AADfUADfYAb9AABP4A70AAAM93/AAAAD/u8wAAAAv/sAAAAAL/IAAE/AAE/zAA3zDvMAv/oAP9AI+QH//xCfcAL/CPzPgO8gAM9u9V/m/AAAb//gDv/2AAAP/4AH//EAAAr/EAH/oAAABPoAAJ9QAD/0AA35",
"CP4gv9AAr9r+EAAM//MAAAT/oAAAHf/0AAC/2P8gCP4gv9A/9AAN+W+QAAj3b5AACPdvkAAI92+QAAj3b5AACPdvkAAI91+QAAj3P/////cI////9wAAAAj3AO////UA7///oD/////6P/////oAAAHP9QAAPv0w",
"AAb/sQAAn/gAAAz/UAAAP/////o/////+gTdDv0P8A/wf+CvYF/gD/AP8A79BN0/w/w/w/w/w/w/w/w/w/w/w/w/w/w/sAP/cAX6AF+gBP4gDPQE/RBfoAX6A/9wP7AAj9ckMEv7AAAAAAAAAAAAAAAf4AAAAAX6",
"AAAAAI9gAAAAAAAAAD////+gA/////9wAAAABfkAAAAAX5A/////+QP/////kD/AAAX5Af////+QB+////kAAAC/QAAAAP8AAAAD/AAAAAAAAAAG7///oB/////2P7AABfk/sAAF+T/////5P/////k/sAAAAB//",
"///5Bu////kL9A7xL9AAAD/AP8A/wD/AP8A/wD/AP8A/wAAAX6AAAACfYAAAAM8gAAAAAAAABu///6Af////9z+wAAX5P7AABfk/sAAF+T+wAAX5P7AABfkf////9wbv//+gAABfoAAAAJ9gAAAAzzAAAAAAAAA/",
"wAAF+j/AAAX6P8AABfo/wAAF+j/AAAX6P8AABfo/wAAF+R/////3Bu///7AAAAT7AAAAAAB/gAAAAAAL9AAAAAAAAAAAAAXv////sQD//////4Af0AAABfoC/QAAAF+gL9AAAAX6Av//////oC//////+gL9AAAA",
"X6Av0AAABfoC/QAAAF+gL9AAAAX6AAAADPMAAAAA/wAAAAA/sAAAAAAAAAAv/////8L//////C/QAAAAAv0AAAAAL9AAAAAC/////0Av////9AL9AAAAAC/QAAAAAv/////8L//////ADvEf4F+gAAAv0C/QL9Av",
"0C/QL9Av0C/QL9Av0C/QAAAF+gAAAAAI9wAAAAAM8wAAAAAAAAAABu////+gH//////3L8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5L8AAAAb5H//////3Bu////+wAAAF+gAAAAAI9wAAAAAM",
"8wAAAAAAAAAAP8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5L8AAAAb5H//////3Bu////+wAE/pMxAAAhKe4QAAAAAAAAP////7AD/////3A/wAAF+gP8AABfoD/AAAX6A/",
"wAAF+gP8AABfoD/AAAX6A/wAAF+gAAX+g0AAAAICn9AAAAAAAAAAL/YAAAX6L/9AAAX6L//iAAX6L9v9AAX6L9DfsAX6L9Au+AX6L9AE/1X6L9AAb/n6L9AACf/6L9AAAL/6L9AAAB36AA72+gAADvb6AAAAAAAA",
"P8AABfo/wAAF+j/AAAX6P8AABfo/wAAF+j/AAAX6P8AABfkf////9wbv//+wAADvb6AAAADvb6AAAAAAAAAAP8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5P8AAAAb5L8AAAAb5H///",
"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",
"//1gP/AAH/IZ//2P8AAf8gAZ///xAB/yAAAZ//9wDv////////ED3/////0zsQ/zD/MP8wAAAAAAAAAAAAAAAAAAAAAAAAPfIO/yH/QB/xAf8QH/EB/xAf8QH/EB/0AO/yA98g/UAP/xA/8wD/MA/zAP8wD/MA/z",
"AP8wP/MP/xD9QAAN9gAAct9kUE////0Ez//+oADf/2AAj/v/IAGmC1AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAABv0AAAb9AAv///87////MAb9AAAG/QAAAAAAAAAAAAH/If8h/gHTAP////AP////AAAAAAAAAA",
"AAAAAAAAAAAAAAAf8h/yAAAAA8AAAAHtAAAA36AAAL/AAACP4QAAb/MAAE/1AAAu9wAAHfoAAAv8AAAA7hAAAA0gAAAAAs/////8MAz//////9AP8wAACv/xD/MAAc//8Q/zAC7/r/EP8wT/9y/xD/Nv/0Av8Q/7",
"/+MAL/EP//0QAC/xD/+wAAAv8Qz//////9ACz/////0wAAv/IAn/8gb//yT/v/JFQf8gAB/yAAH/IAAf8gAB/yAAH/IAAf8gAB/yA9/////9MA3//////+AP8wAAAC/xAAAAAAAv8QAAAAAAL/ECz//////gDf//",
"///9MA/zAAAAAAAP8wAAAAAAD/MAAAAAAA////////EP///////xA9/////oAA7//////1Af8gAAAL+AAAAAAAC/gAAAAAAAv4AAD/////9wAA//////0AAAAAAAP/AAAAAAAD/wH/IAAAA/8A7//////9AD3///",
"//wgAAAACf8AAAAAv/8AAAAc//8AAALf/P8AAD7/g/8ABP/1A/8Ab/4wA/8A7//////87//////8AAAAA/8AAAAAA/8AAAAAA/8AD///////8Q////////EP8wAAAAAAD/MAAAAAAA/zAAAAAAAP//////0wD///",
"////4AAAAAAAL/EAAAAAAC/xD/MAAAAv8Q3//////+AD3/////0wA8/////yAA3/////8gAP8wAAAAAAD/MAAAAAAA/zAAAAAAAP//////0wD///////4A/zAAAAL/EP8wAAAC/xD/MAAAAv8Q3//////+ADz///",
"//0w/////9QP//////EAAAAA/zAAAAAP8wAAAAD/MAAAAA/zAAAAAP8wAAAAD/MAAAAA/zAAAAAP8wAAAAD/MAAAAA/zA8/////9MA3//////+AP8wAAAC/xD/MAAAAv8Q/zAAAAL/EN///////gDv//////8A/z",
"AAAAL/EP8wAAAC/xD/MAAAAv8Q3//////+ADz/////0wA9/////8IA7//////8Af8gAAAD/wH/IAAAA/8B/yAAAAP/AO///////wA9//////8AAAAAAAP/AAAAAAAD/wAAAAAAA/8A7//////8AD3/////wgH/If",
"8gAAAAAAAAAAAAAAAB/yH/Iv8S/xAAAAAAAAAAAAAAVQL/Ev8S/QLCAAAAGTAAB/8wBe/9E8/+cA7/kQAO/5EAA8//cAAF3/4QAAf/MAAAGTD/////4A/////+AAAAAAAAD/////4A/////+AAAAAAAAAAAAAAAA",
"CyAAAAD/kQAADP/3AAAF7/5QAAB//yAAB//yAF7/1QDP/nAAD/kQAACyAAAAf/////1Af//////wAAAAAB/yAAAAAB/yAAAAAB/yABv////wAJ////1AAL+AAAAAAAAAAAAAAAAAAAAAAL+AAAAAAL+AAAAAA8//",
"///9MA3//////9AP8wAAAC/xD/Mb/7Ev8Q/zr//6L/EP890A3i/xD/PdAN4v8Q/zr/////EP8xv////xD/MAAAAAAA3///////EDz//////xAs/////9QAz///////AP8wAAAA/zD/MAAAAP8w/zAAAAD/MP8wAA",
"AA/zD///////8w////////MP8wAAAA/zD/MAAAAP8w/zAAAAD/MP8wAAAA/zD//////6AA///////4AP9AAAAI+wD/QAAACPwA/0AAAAj7AP//////+gD///////8Q/0AAAAD/MP9AAAAA/0D/QAAAAP8w//////",
"//EP//////5QA8//////8g3///////IP8wAAAAAAD/MAAAAAAA/zAAAAAAAP8wAAAAAAD/MAAAAAAA/zAAAAAAAP8wAAAAAAD/MAAAAAAA3///////ID3//////yD//////9QA////////AP8wAAAA/zD/MAAAAP",
"8w/zAAAAD/MP8wAAAA/zD/MAAAAP8w/zAAAAD/MP8wAAAA/zD/MAAAAP8w////////AP//////1AD///////MP//////8w/0AAAAAAD/QAAAAAAP9AAAAAAA//////cAD/////9wAP9AAAAAAA/0AAAAAAD/QAAA",
"AAAP//////8w///////zD///////MP//////8w/0AAAAAAD/QAAAAAAP9AAAAAAA//////cAD/////9wAP9AAAAAAA/0AAAAAAD/QAAAAAAP9AAAAAAA/0AAAAAAA8/////9QA3///////AP8wAAAB/yD/MAAAAA",
"AA/zAAAAAAAP8wAA3//zD/MAAN//8w/zAAAAH/MP8wAAAB/zD/MAAAAf8g3//////+AD3/////1AD/MAAAAM9w/zAAAADPcP8wAAAAz3D/MAAAAM9w/zAAAADPcP///////3D///////9w/zAAAADPcP8wAAAAz3",
"D/MAAAAM9w/zAAAADPcP8wAAAAz3D/MP8w/zD/MP8w/zD/MP8w/zD/MP8w/zAAAAAAD/UAAAAAAP9QAAAAAA/1AAAAAAD/UAAAAAAP9QAAAAAA/1AAAAAAD/UAAAAAAP9f9QAAAA/171AAAAD/S///////8Rz///",
"//5QD/MAAAL/sA/zAAAd/hAP8wAAz/IAD/MACv9AAA/zAH/2AAAP////kAAAD////5AAAA/zAH/2AAAP8wAJ/0AAD/MAAM/yAA/zAAAd/hAP8wAAAv+wD/MAAAAAAA/zAAAAAAAP8wAAAAAAD/MAAAAAAA/zAAAA",
"AAAP8wAAAAAAD/MAAAAAAA/zAAAAAAAP8wAAAAAAD/MAAAAAAA////////MP///////zD/wAAAAC/8AP/6AAAB7/wA//9wAAz//AD/v/UAr/z8AP87/zf/aPwA/zDP7/kI/AD/MB7/sAj8AP8wA/0ACPwA/zAAQg",
"AI/AD/MAAAAAj8AP8wAAAACPwA/zAAAAAI/AD/wAAAAf8w//oAAAH/MP//gAAB/zD/v/YAAf8w/zr/QAH/MP8wz/IB/zD/MB7+Ef8w/zAC/8H/MP8wAE/7/zD/MAAG//8w/zAAAI//MP8wAAAK/zA9/////9QA3/",
"/////+Af8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8g3//////+AD3/////1AD//////9QA///////+AP8wAAAB/yD/MAAAAf8w/zAAAAH/MP8wAAAB/yD///",
"////4A///////UAP8wAAAAAAD/MAAAAAAA/zAAAAAAAP8wAAAAAAA9/////9MADf//////4AH/IAAAAf8gH/IAAAAf8gH/IAAAAf8gH/IAAAAf8gH/IAAAAf8gH/IAAAAf8gH/IAAAAf8gH/IAAAAf8gDf//////",
"/6A9///////6H//////9MB///////+Af8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH///////4B///////UAf8gAG/5AAH/IAAH/3AB/yAAAJ/1Af8gAAAL/xBN/////9QA7//////+Av8QAAAC/xL/EAAAAA",
"AC/xAAAAAAAO//////0wBN//////4AAAAAAAL/EAAAAAAC/xL/EAAAAv8Q///////+AE3/////0wr///////mv//////+QAACvkAAAAAAK+QAAAAAAr5AAAAAACvkAAAAAAK+QAAAAAAr5AAAAAACvkAAAAAAK+Q",
"AAAAAAr5AAAAAACvkAAAH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8g3//////+AD3/////1AL/cAAAAAAv9wj/EAAAAAv9AA76AA",
"AABf9AAF/0AAAA37AAAM/QAAB/8gAAAv9gAB/4AAAACf8QCv4AAAAAHvkD/1AAAAAAb/PfsAAAAAAAz+/yAAAAAAAD//kAAAAAAAAK/hAAAAP/IAAE/0AAAv8g34AACv+gAAj9AH/gAB//8AAO9wAf9ABv//YAT/",
"EAC/oAz5r8AK+wAAX/Av80/yH/UAAA/2j9AO+G/gAAAK/O9wCP7PkAAABP//EAL//zAAAADv+wAAz/0AAAAAj/UAAG/3AAAAAC/wAAAf8QAAL/oAAADP4Ab/gAAL/zAAn/UAj/UAAAv/Nv+AAAAA3+/6AAAAAB7/",
"wAAAAAAe/8AAAAAA3+/6AAAAC/82/4AAAJ/1AI/1AAb/gAAL/zAv+gAAAN/gX/UAAAA/9wn/IAAB77AA39EADP4QAC/7AJ/zAAAF/4b/cAAAAJ//+wAAAAAM/+EAAAAAAv9AAAAAAAD/MAAAAAAA/zAAAAAAAP8w",
"AAAAAAD/MAAAL///////8S////////EAAAAAC//gAAAAAd/8EAAAAD7/oAAAAAX/9wAAAACP/1AAAAAK/+MAAAABz/wQAAAAHv+gAAAAAC////////Ev///////xH/8x//Mf8gH/IB/yAf8gH/IB/yAf8gH/IB//",
"Mf/z0gAAAA7RAAAAv8AAAAHfoAAAAv9wAAAE/1AAAAb/MAAACf4QAAAL/AAAAA36AAAALtAAAAA8L/8i//IB/yAf8gH/IB/yAf8gH/IB/yAf8i//Iv/yH///////8B////////Bf4B/zDPcAAAAAAAAAAAAAAAAA",
"AAAAAAAAAAAAAAAAAB/////7EB//////oAAAAABf4AAAAABf4B//////4B//////4B/xAABf4B/xAABf4A7/////4APf////4B/yAAAAAf8gAAAAH/IAAAAB/////7Ef/////7H/IAAE/h/yAABP8f8gAAT/H/IA",
"AE/x/yAABP8f8gAAT+H/////+x/////7EAPf////0A7/////0C/xAAAAAC/xAAAAAC/xAAAAAC/xAAAAAC/xAAAAAC/xAAAAAA7/////4APf////4AAAAADfYAAAAA32AAAAAN9gn/////Zv/////2n6AAAN9p+g",
"AADfafoAAA32n6AAAN9p+gAADfafoAAA32b/////9gn/////YAPf///7EA7/////oC/xAABf0C/xAABf4C//////4C//////4C/xAAAAAC/xAAAAAA7/////4APf////4APf//Dv//8f8gAB////H///8f8gAB/y",
"AAH/IAAf8gAB/yAAH/IAAf8gAB/yAAAF7///+gAf/////3BP4AAAj6BP4AAAj7BP4AAAj7BP4AAAj7BP4AAAj7BP4AAAj7Af/////7AF7////7AAAAAAj7AAAAAAj6AAr////3AAr///+gAf8gAAAAH/IAAAAB/y",
"AAAAAf////+xH/////+x/yAABP4f8gAAT/H/IAAE/x/yAABP8f8gAAT/H/IAAE/x/yAABP8f8gAAT/Af8R/xAAAd0R/xH/Ef8R/xH/Ef8R/xH/Ef8QAADfYAAA32AAAAAAAABFIAAA32AAAN9gAADfYAAA32AAAN",
"9gAADfYAAA32AAAN9gAADfYAAA32AAAN9i////Qv//6AH/IAAAAB/yAAAAAf8gAAAAH/IAAL2h/yAAz/Mf8gC/9AH/IK/1AB////YAAf///0AAH/IK/zAB/yAM/iAf8gAd/RH/IAAe+wH/IAH/IAH/IAH/IAH/IA",
"H/IAH/IAH/IAH/IAH/IAH/IADv/zA9/zH////////nAB/////////0Af8gAO9QAL9wH/IADvUAC/cB/yAA71AAv3Af8gAO9QAL9wH/IADvUAC/cB/yAA71AAv3Af8gAO9QAL9wH/IADvUAC/cB/////7EB//////",
"sB/yAABP4B/yAABP8B/yAABP8B/yAABP8B/yAABP8B/yAABP8B/yAABP8B/yAABP8APf///7EA7/////oC/xAABf0C/xAABf4C/xAABf4C/xAABf4C/xAABf4C/xAABf0A7/////oAPf///7EB/////7Ef/////7",
"H/IAAE/h/yAABP8f8gAAT/H/IAAE/x/yAABP8f8gAAT+H/////+x/////7Ef8gAAAAH/IAAAAB/yAAAAAf8gAAAACf////9m//////avkAAA32r5AAAN9q+QAADfavkAAA32r5AAAN9q+QAADfZv/////2Cf////",
"9gAAAADfYAAAAA32AAAAAN9gAAAADfYD3///sO////sf8QAAAf8QAAAf8QAAAf8QAAAf8QAAAf8QAAAf8QAAAf8QAAAE3///+gAO/////4Av8AAAb8Av8AAAAAAP////+xAE3////5AAAAAAb9Av8AAAb9AO////",
"/5AD3///+xAf8gAB/yAAH/IAAf///x////H/IAAf8gAB/yAAH/IAAf8gAB/yAADv//8D3//wH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gDv////+gA9////sQX/MAAACf",
"4Q37AAAC/3AE/0AACv0AAL/AAD/1AAA/9QC/wAAACv0E/0AAAAL/bPsAAAAAn//yAAAAAB//oAAAAAAH/xAAAD/yAAX/YAAf9A34AAz/0AB/4Af+AD//9QDfgAH/UK/t/AP/IACvwf+G/zn8AABP+v8Q7772AAAO",
"//oAj//xAAAI//QAH/+gAAAB/9AACv9AAAAAv2AAA/4AAC/6AADf4Ab/cAv/MACf9Z/1AAAL//9wAAAB3/oAAAAC7/wAAAAN//+QAACv9I/2AAf/YAv/MC/5AADf4E/wAACPsE/wAACPsE/wAACPsE/wAACPsE/w",
"AACPsE/wAACPsE/wAACPsE/wAACPsB//////sAXv////sAAAAACPsAAAAACPsACv////gACv///6AB//////8B//////8AAAAC3/wAAABO/7AAAAf/+AAAAK//UAAAHP/SAAAA7/sQAAAB//////8B//////8AG/",
"YL/2DvcQ71Av9Qn8EJ/iAO9QDvUA73EL/2As9h/yH/If8h/yH/If8h/yH/If8h/yH/If8h/yH/If8h/yL9MC/+AE/xAf8gH/UAr9AM/QH/MB/yBP8S/+Av0wf9YAGf//2SAo7mAAAAAAAAAAAAAAAAAAAAAAB/wA",
"AAAAC/gAAAAAD/QAAAAAAAAAAB/////7EB//////oAAAAABf4AAAAABf4B//////4B//////4B/xAABf4B/xAABf4A7/////4APf////4AAAL/EAAAAH/QAAAAC/kAAAAAAAAAAD3///+xDv////+i/xAABf0v8Q",
"AAX+L//////i//////4v8QAAAAL/EAAAAA7/////4D3////+CPsM9w/zAAAf8R/xH/Ef8R/xH/Ef8R/xH/Ef8QAAC/gAAAAAD/QAAAAAP/AAAAAAAAAAAAPf///7EA7/////oC/xAABf0C/xAABf4C/xAABf4C/x",
"AABf4C/xAABf4C/xAABf0A7/////oAPf///7EAAAC/gAAAAAD/QAAAAAP/AAAAAAAAAAAB/yAABf4B/yAABf4B/yAABf4B/yAABf4B/yAABf4B/yAABf4B/yAABf4B/yAABf4A7/////oAPf///7EAAAAI/AAAAA",
"AADPcAAAAAAA/zAAAAAAAAAAAAACz/////1ADP//////8A/zAAAAD/MP8wAAAA/zD/MAAAAP8w/zAAAAD/MP///////zD///////8w/zAAAAD/MP8wAAAA/zD/MAAAAP8w/zAAAAD/MAAAH/IAAAAABf4AAAAAAJ",
"+gAAAAAAAAAAAA///////zD///////MP9AAAAAAA/0AAAAAAD/QAAAAAAP/////3AA//////cAD/QAAAAAAP9AAAAAAA/0AAAAAAD///////MP//////8wv4D/RP8AAAD/MP8w/zD/MP8w/zD/MP8w/zD/MP8w/z",
"AAAAn7AAAAAAAN9gAAAAAAH/IAAAAAAAAAAAAAPf/////UAN///////gH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/IN///////gA9/////9QAAAAJ+wAAAA",
"AADfYAAAAAAB/yAAAAAAAAAAAAAf8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yDf//////4APf/////UAADPswAAAAD//+4wAAAwSv",
"0gAAAAAAAAAf////+xAf/////7Af8gAAT+Af8gAAT/Af8gAAT/Af8gAAT/Af8gAAT/Af8gAAT/Af8gAAT/Af8gAAT/AAAM+0AAAAAADv/+5AAAAAMDr9IAAAAAAAAAAAD/wAAAAf8w//oAAAH/MP//gAAB/zD/v/",
"YAAf8w/zr/QAH/MP8wz/IB/zD/MB7+Ef8w/zAC/8H/MP8wAE/7/zD/MAAG//8w/zAAAI//MP8wAAAK/zAAf8j7AAAAf8j7AAAAAAAAAAH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/gH/IAAF/g",
"H/IAAF/gDv////+gA9////sQAABf5v0AAAAAX+b9AAAAAAAAAAAAH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8h/yAAAAH/If8gAAAB/yH/IAAAAf8g3//////+AD3///",
"//1AAAAAD/MAAAAA/zAAAAAAAAAAAAD/MAAAAA/yAK////4Aj////TAK+AAAAACvgAAAAAr4AAAAAI//////8K//////H/If8gAAHuEf8h/yH/If8h/yH/If8h/yBN/7EP//+j+gD+P6AP4f//+wTf+xAAAAAAAA",
"AAAAAAAAAAAAAAAAAAAAH/L/P/Qf8v8/9B//////8R//////8QAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAB////////Af///////wAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAb/////7AAr/////+wAM9w",
"AAAAAG//////8ABv//////AAAM9wAAAAAADPcAAAAABv//////AAb//////wAADPcAAAAAAAr/////+wABv/////sAUPcwBhJQAAIAAGAAAGAAAAAAAhAAQA8gQOAAAAACIABwDyBw4cAAAAIwAPAPIPDk0AAAAk",
"AA8A8A8StgAAACUAEgDyEg49AQAAJgASAPISDrsBAAAnAAQA8gQOOQIAACgABQDyBQ5VAgAAKQAFAPIFDngCAAAqAAkA8goOmwIAACsACAD3CQnhAgAALAAEAP4EBQoDAAAtAAoA+QoHFAMAAC4ABAD+BAI3AwAA",
"LwAKAPIKDjsDAAAwABAA8hAOgQMAADEABwDyBw7xAwAAMgAQAPIQDiIEAAAzABAA8hAOkgQAADQADgDyDg4CBQAANQAQAPIQDmQFAAA2ABAA8hAO1AUAADcADQDyDQ5EBgAAOAAQAPIQDp8GAAA5ABAA8hAODwcA",
"ADoABAD1BAt/BwAAOwAEAPUEDpUHAAA8AAkA9QkLsQcAAD0ADAD3DAnjBwAAPgAJAPUKCxkIAAA/AA0A8g0OUAgAAEAAEADyEA6rCAAAQQAQAPIQDhsJAABCABAA8hAOiwkAAEMAEADyEA77CQAARAAQAPIQDmsK",
"AABFAA8A8g8O2woAAEYADgDyDg5ECwAARwAQAPIQDqYLAABIABAA8hAOFgwAAEkABADyBA6GDAAASgAPAPIPDqIMAABLAA8A8g8OCw0AAEwADwDyDw50DQAATQASAPISDt0NAABOABAA8hAOWw4AAE8AEADyEA7L",
"DgAAUAAPAPIPDjsPAABRABEA8hEOpA8AAFIAEADyEA4bEAAAUwAQAPIQDosQAABUAA4A8g8O+xAAAFUAEADyEA5kEQAAVgATAPITDtQRAABXABYA8hYOWRIAAFgADwDyDw7zEgAAWQAPAPIQDlwTAABaABAA8hAO",
"zBMAAFsABQDyBQ48FAAAXAAKAPIKDl8UAABdAAUA8gUOpRQAAF8AEAAAEALIFAAAYAAEAO4FEtgUAABhAA0A9Q0LBRUAAGIADQDxDQ9NFQAAYwANAPUNC68VAABkAA0A8Q0P9xUAAGUADQD1DQtZFgAAZgAIAPEI",
"D6EWAABnAA0A9Q0Q3RYAAGgADQDxDQ9FFwAAaQAEAPEED6cXAABqAAX88QkTxRcAAGsADADxDQ8bGAAAbAAHAPEHD30YAABtABMA9RMLshgAAG4ADQD1DQsbGQAAbwANAPUNC2MZAABwAA0A9Q0PqxkAAHEADQD1",
"DQ8NGgAAcgAKAPUKC28aAABzAA0A9Q0LphoAAHQACADxCA/uGgAAdQANAPUNCyobAAB2AA8A9Q8LchsAAHcAFAD1FAvFGwAAeAANAPUNCzMcAAB5AA0A9Q0QexwAAHoADQD1DQvjHAAAewAFAPIFDisdAAB8AAQA",
"8AQSTh0AAH0ABQDyBg5yHQAAfgAIAPkIB5wdAADhAA4A8A4QuB0AAOkADADwDRAoHgAA7QAEAPAFEJAeAADzAA0A8A0QuB4AAPoADQDwDRAgHwAAwQAQAO4QEogfAADJAA8A7g8SGCAAAM0ABADuBRKfIAAA0wAQ",
"AO4QEswgAADaABAA7hASXCEAAPEADQDwDRDsIQAA0QAQAO4QElQiAAD8AA0A8A0Q5CIAANwAEADuEBJMIwAAvwANAPINDtwjAAChAAQA8gQONyQAALAACADzCA1TJAAAJiALAP4LAockAAATIA0A+Q0HkiQAABQg",
"EAD5EAfAJAAArCAPAPIPDvgkAAAO+Q75DvkO+Q75DvkO+Q75DvkN+AAAAAAO+Q75DvrfoO+t+g7636AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAACf4AC/wAAADvkAH/cAAAP/QAb/EA",
"3///////9g3///////9gAE/zAH/wAAAI/gAK/QAAAL+gAO+QAAAP/HQv9gAG////////0G////////0AD/gAL/UAAAT/MAf/EAAAn+AAz7AAAAAAAN+gAAAAAAAN+gAAAATf/////7IB////////wF/yAN+gBP8V",
"/yAN+gBP81/yAN+gAAAF/yAN+gAAAB///////8IATf//////0AAAAN+gBP8gAAAN+gBP81/yAN+gBP80/yAN+gBP8h7///////0APf/////8IAAAAN+gAAAAAAAN+gAAAAG//oAAAABOAAv///YAAAb/AA/wBfsA",
"AI//AB/wBfwACv/jAA/wBfsBz/0gAAz///ct/8EAAAG//oPv+gAAAAAAAF//iO/7EAAAB//2X///wAAAn/9Ar2AP8QAL/+MAv2AP8gCP/RAAr2AP8QCfsAAAb///wACZAAAACO/7IAA8/////7EAAADv//////sA",
"AAP///////8AAAT/MAAAB/8AAAT/MAAAAAAAAAL/kQAAAAAAAAn//5EAAAAAAA////+iAP+AAA/4bv//o/+AAA/4AH7///+AAA/4AAB+///lAA/4AAAAfv//oAr////////f0AG//////+cFoA75DvkO+QAAAAAA",
"AAAAAAAAAAAAAAAAAAAAAAABr6C/+g/8UP9wD/cA/3AP9wD/cA/3AP9wD/cA/8UL/6Ab+g/oAP/2CO+gDPsAz7AM+wDPsAz7AM+wDPsAz7CO+g//YP6AAAf/AAAAB/8AAA6r/42AT////9BM////oAB///EAAf//",
"+gAG/1z+EABaArEAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAf9gAAAf9gAK////8a////8QAf9gAAAf9gAAAf9gAAAAAAAAAAAAAAD/gP+A/3D/IMQA7////gDv///+AAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
"AAAAD/gP+AAAAAA9AAAAAe0AAAAM/QAAAK/0AAAH/2AAAE/6AAAC78AAAA3+EAAAr/MAAAf/YAAAT/kAAADfwAAAAO4QAAAA0wAAAAAAn//////mAAn///////9ADf///////5AO+QAAAJ//oA75AAAc//+gDvkA",
"A+/436AO+QBf/1DfoA75CP/SAN+gDvq/+xAA36AO//+AAADfoA7/9QAAAN+gDf///////5AJ////////QACv/////+YAAAT/4ALv/gDf/+C///6P+5/gAAn+AACf4AAJ/gAAn+AACf4AAJ/gAAn+AACf4AAJ/gCf",
"/////+YACP///////zAN+QAAAADfgA75AAAAAN+gAAAAAAAA36AAAAAAAADfoACv//////+ACf///////0AO///////mAA75AAAAAAAADvkAAAAAAAAO+QAAAAAAAA7///////+gDv///////6AAr/////+hAAn/",
"//////oADvgAAAAH/wAP+AAAAAf/AAAAAAAAB/8AAAAAAAAH/wAACv/////+AAAK//////9QAAAAAAAA/4AAAAAAAAD/gAAAAAAAAP+AD/gAAAAA/4AM////////MAK//////+YAAAAAAK/zAAAAABz/8wAAAAHf",
"//MAAAA+///zAAAE//5/8wAAb//RT/MACP/7AE/zAJ//kABP8wDv///////y7///////8gAAAABP8wAAAAAAT/MAAAAAAE/zAAAAAABP8wAO////////oA7///////+gDvkAAAAAAAAO+QAAAAAAAA75AAAAAAAA",
"Dv//////5gAO////////MA7///////+AAAAAAAAA36AAAAAAAADfoA75AAAAAN+gDfkAAAAA34AI////////QACf/////+YAAK//////cAAJ//////9wAA75AAAAAAAADvkAAAAAAAAO+QAAAAAAAA7//////+YA",
"Dv///////zAO////////gA75AAAAAN+gDvkAAAAA36AO+QAAAADfoA75AAAAAN+ACf///////0AAr//////mAP/////9QA///////yAAAAAAD/YAAAAAAP9wAAAAAA/3AAAAAAD/cAAAAAAP9wAAAAAA/3AAAAAA",
"D/cAAAAAAP9wAAAAAA/3AAAAAAD/cAAAAAAP9wAAAAAA/3AAr//////nAAn///////9QDv///////5AO+QAAAADfoA75AAAAAN+gDvkAAAAA35AK////////YAz///////9wDvkAAAAA35AO+QAAAADfoA75AAAA",
"AN+gDvkAAAAA35AJ////////QACv/////+cAAa//////5gAK////////MA/4AAAAAP9wD/gAAAAA/4AP+AAAAAD/gA/4AAAAAP+AD////////4AK////////gAGv//////+AAAAAAAAA/4AAAAAAAAD/gAAAAAAA",
"AP9wDf///////zACv//////mAA/4D/gP+AAAAAAAAAAAAAAAAA/4D/gP9w/3D/cAAAAAAAAAAAAAAAAO5g/3D/YP8g1AAAAAKwAAAZ/xAAf//wBe//kQz/+yAA7/gAAAv/+zAABd//oQAAf//wAAAZ/xAAAAKwAO",
"//////EO//////EO//////EAAAAAAAAO//////EO//////EO//////EAAAAAAAAAAAAAAAAKMAAAAA76IAAADf/5EAAAj//3AAABr//gAAAG//EAAa//0ACP/+cADf/5EAAO+iAAAAowAAAAb//////UBv//////",
"8gAAAAAA/2AAAAAAD/cAAAAAAP9wAAAAAA/3AAXf////YAL/////8gBv////1QAH/wAAAAAAAAAAAAAAAAAAAAAAAH/wAAAAAAf/AAAAAACv/////+cACf///////0AO+QAAAADfkA75AAAAAN+gDvkF3/sg36AO",
"+S///9DfoA75X5AN8d+gDvlfkA3x36AO+S//////oA75Bd////+gDvkAAAAAAAAO+QAAAAAAAAn///////+gAK///////6AAn//////oAAn///////9wDf///////7AO+QAAAADPwA75AAAAAM/ADvkAAAAAz8AO",
"+QAAAADPwA7////////ADv///////8AO////////wA75AAAAAM/ADvkAAAAAz8AO+QAAAADPwA75AAAAAM/ADv//////wwAO///////+AA7///////8wDvoAAAAE/0AO+gAAAAT/QA76AAAABP8wDv///////yAO",
"////////kA7////////ADvoAAAAAv8AO+gAAAAC/wA7///////+wDv///////3AO///////pAAGv//////+wCf///////7AO////////sA/5AAAAAAAAD/kAAAAAAAAP+QAAAAAAAA/5AAAAAAAAD/kAAAAAAAAP",
"+QAAAAAAAA/5AAAAAAAAD/kAAAAAAAAO////////sAn///////+wAa///////7AO///////oAA7///////9wDv///////7AO+QAAAADPwA75AAAAAM/ADvkAAAAAz8AO+QAAAADPwA75AAAAAM/ADvkAAAAAz8AO",
"+QAAAADPwA75AAAAAM/ADv///////7AO////////cA7//////+gADv//////+wDv//////+wDv//////+wDvoAAAAAAADvoAAAAAAADvoAAAAAAADv/////7AADv/////7AADv/////7AADvoAAAAAAADvoAAAAA",
"AADv//////+wDv//////+wDv//////+wDv//////+w7///////sO///////7DvoAAAAAAA76AAAAAAAO+gAAAAAADv/////7AA7/////+wAO//////sADvoAAAAAAA76AAAAAAAO+gAAAAAADvoAAAAAAA76AAAA",
"AAABr//////nAAn///////9QDv///////6AP+QAAAADPwA/5AAAAAAAAD/kAAAAAAAAP+QAADv//wA/5AAAO///AD/kAAA7//8AP+QAAAADPwA/5AAAAAM/ADv///////7AJ////////YAGv/////+gADvkAAAAA",
"f/EO+QAAAAB/8Q75AAAAAH/xDvkAAAAAf/EO+QAAAAB/8Q75AAAAAH/xDv////////EO////////8Q7////////xDvkAAAAAf/EO+QAAAAB/8Q75AAAAAH/xDvkAAAAAf/EO+QAAAAB/8Q75DvkO+Q75DvkO+Q75",
"DvkO+Q75DvkO+Q75DvkAAAAAAAz8AAAAAAAAz8AAAAAAAAz8AAAAAAAAz8AAAAAAAAz8AAAAAAAAz8AAAAAAAAz8AAAAAAAAz8AAAAAAAAz8AAAAAAAAz8DvkAAAAAz8Dv///////7Cv///////2Aa//////6AAO",
"+QAAAA3/MO+QAAAK/5AO+QAAB//AAO+QAAP/4QAO+QAB7/IAAO+QAM/1AAAO////+AAAAO////+AAAAO/////1AAAO+QAK//IAAO+QAAv/4QAO+QAADP/AAO+QAAAd/5AO+QAAAB3/MO+QAAAAAAAO+QAAAAAAAO",
"+QAAAAAAAO+QAAAAAAAO+QAAAAAAAO+QAAAAAAAO+QAAAAAAAO+QAAAAAAAO+QAAAAAAAO+QAAAAAAAO+QAAAAAAAO////////wO////////wO////////wP/zAAAAAK/3AP/+IAAACP/3AP//0AAAX//3AP//+w",
"AD///3AP+c/4Ae/1/3AP+R3/ff9w/3AP+QLv//oA/3AP+QBP/8AA/3AP+QAG/RAA/3AP+QAAggAA/3AP+QAAAAAA/3AP+QAAAAAA/3AP+QAAAAAA/3AP+QAAAAAA/3AP/zAAAADPwA//4QAAAM/AD//8AAAAz8AP",
"//+gAADPwA/5z/cAAM/AD/ke/1AAz8AP+QP/8gDPwA/5AF/9EM/AD/kACP+wz8AP+QAAr/nPwA/5AAAN///AD/kAAAHv/8AP+QAAAD//wA/5AAAABv/AAa//////5wAK////////UA7///////+gD/gAAAAA37AP",
"+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA7///////+gCv///////1ABr//////oAA///////+cA////////9Q////////+g/5AAAAAM/A/5AAAAAM/A/5AA",
"AAAM/A/5AAAAAM/A////////+g////////9Q///////+cA/5AAAAAAAA/5AAAAAAAA/5AAAAAAAA/5AAAAAAAAGv/////+gAAK////////YADv///////6AA/4AAAAAN+wAP+AAAAADfsAD/gAAAAA37AA/4AAAA",
"AN+wAP+AAAAADfsAD/gAAAAA37AA/4AAAAAN+wAP+AAAAADfsADv////////9Qr/////////UBr////////1D///////5wAP////////QA////////+gD/gAAAAAz7AP+AAAAADPsA/4AAAAAM+wD/gAAAAAz7AP",
"////////oA////////9AD///////5wAP+AAAf/wAAA/4AAAH/8AAD/gAAACP+wAP+AAAAAj/kAGv/////+YACv///////0AP////////kA/3AAAAAO+gD/cAAAAAAAAP9wAAAAAAAA///////+cACv///////1AB",
"r///////kAAAAAAAAO+gD/cAAAAA76AP////////kAr///////9QAa//////5wCv////////Gv////////Gv////////EAAAD/gAAAAAAAD/gAAAAAAAD/gAAAAAAAD/gAAAAAAAD/gAAAAAAAD/gAAAAAAAD/gA",
"AAAAAAD/gAAAAAAAD/gAAAAAAAD/gAAAAAAAD/gAAAAP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+w",
"Dv///////6AK////////UAGv/////+gAH/0AAAAAAAf/cH/2AAAAAAHv0ADv4AAAAACf9QAF/4AAAAAv/AAADP8gAAAL/zAAAD/6AAAE/6AAAACv8wAA3/EAAAAC/8AAb/cAAAAACP9QDv4AAAAAAA7+CP9QAAAA",
"AABv+f/AAAAAAAAA3//zAAAAAAAABP/6AAAAAAAAAAv/IAAAAC/4AAAD/5AAAC/3DP0AAAn/4AAAj/IH/zAADv/0AADvwAH/kABf//oABP9gAL/gAK/7/wAJ/xAAb/QB/6X/UA/7AAAP+gb/QP+wX/UAAAr/DP4A",
"n/G/8AAABf9/+ABP9/+gAAAA7//zAA7//0AAAACf/9AACP/+AAAAAD//cAAD//kAAAAADv8gAADf8wAAAAAI/AAAAH/QAAAf/iAAAAn/gH/9AAAH/9AAr/sABP/iAADP+QL/9AAAAe/37/YAAAAD///5AAAAAAX/",
"+wAAAAAAX/+wAAAAAD///5AAAAAe/47/YAAADP+QP/8wAAr/sABf/iAH/9AAAH/9Af/iAAAAn/hf+wAAAADf8gn/cAAAC/9gAN/0AAB/+gAAP/4gBP/hAAAH/9Au/zAAAAC/+s/4AAAAAB7//8AAAAAABP//IAAA",
"AAAAj/UAAAAAAABf8gAAAAAAAF/yAAAAAAAAX/IAAAAAAABf8gAAAAAAAF/yAAAAD////////6AP////////oA////////+QAAAAAACf+gAAAAAAG/9wAAAAAALf9AAAAAAAT/0gAAAAAAf/wQAAAAAAn/kAAAAA",
"ABz/cAAAAAAC3+QAAAAAAA////////+gD////////6AP////////oA//oP/6D/gA/4AP+AD/gA/4AP+AD/gA/4AP+AD/gA//oP/60wAAAADuEAAAAO/AAAAAT/kAAAAH/2AAAACv8wAAAA3+EAAAAu/AAAAAT/kA",
"AAAH/2AAAACv8wAAAAz9AAAAAe0AAAAATQ//kP/5AO+QDvkA75AO+QDvkA75AO+QDvkA75AO+Q//kP/5D////////5AP////////kD/0AO+QCv0AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
"AA//////wgD//////9AAAAAABf8gAAAAAF/yD///////IP//////8g///////yD/cAAAX/IP9wAABf8gv//////yAa//////IA/4AAAAAAD/gAAAAAAP+AAAAAAA/4AAAAAAD//////CAP//////0A/4AAAE/yD/",
"gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/yD//////+AP/////8IAAb//////IL//////8g/3AAAAAAD/cAAAAAAP9wAAAAAA/3AAAAAAD/cAAAAAAP9wAAAAAA/3AAAAAAC///////IBv///",
"//8gAAAAAA36AAAAAADfoAAAAAAN+gAAAAAA36AG7/////oE//////+gj/AAAA36Cf8AAADfoJ/wAAAN+gn/AAAA36Cf8AAADfoJ/wAAAN+gj/AAAA36BP//////oAbv////+gABv////7IAv//////AD/cAAAX/",
"EP9wAABf8g///////yD///////IP//////8g/3AAAAAAD/cAAAAAAL//////8gG//////yABr//8Cv///A////wP+AAAD////A////wP+AAAD/gAAA/4AAAP+AAAD/gAAA/4AAAP+AAAD/gAAA/4AAACz////6EA",
"7/////+gL/QAAAj+A/9AAACP8D/0AAAI/wP/QAAAj/A/9AAACP8D/0AAAI/wL/QAAAj/AO//////8APP/////wAAAAAAj/AAAAAACP8ABv/////gAG/////6AAb////6EA/4AAAAAAD/gAAAAAAP+AAAAAAA/4AA",
"AAAAD//////CAP//////0A/4AAAE/yD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8wD/cP9w/3AAAP9w/3D/cP9w/3D/cP9w/3D/cP9w/3AAAK/QAAAK/QAAAK/QAA",
"AHqAAAAK/QAAAK/QAAAK/QAAAK/QAAAK/QAAAK/QAAAK/QAAAK/QAAAK/QAAAK/QAAAK/QAAAK/Aj///+wj///9Qj//+cAAP+AAAAAAA/4AAAAAAD/gAAAAAAP+AAAAkQA/4AABP/gD/gAA//iAP+AA//zAA/4Au",
"/0AAD////2AAAP///+AAAA////+wAAD/gC7/kAAP+AAu/3AA/4AALv9QD/gAAC7/AA/4AAD/gAAP+AAA/4AAD/gAAP+AAA/4AAD/gAAP+AAA/4AAD/gAAP+AAA/4AAC//9ABv/0AD/////////wwAP/////////+",
"AA/4AAH/cAAv9AD/gAAf9wAC/1AP+AAB/3AAL/UA/4AAH/cAAv9QD/gAAf9wAC/1AP+AAB/3AAL/UA/4AAH/cAAv9QD/gAAf9wAC/1AP+AAB/3AAL/UAD//////CAP//////0A/4AAAE/yD/gAAAT/MP+AAABP8w",
"/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8wAb////+yAL//////0A/3AAAF/xD/cAAAX/IP9wAABf8g/3AAAF/yD/cAAAX/IP9wAABf8g/3AAAF/xC//////9ABv////8IAD//////CAP//",
"////0A/4AAAE/yD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/yD//////+AP/////8IA/4AAAAAAD/gAAAAAAP+AAAAAAA/4AAAAAAAH7/////kF//////+Qn+AAAA75Cv4AAADvkK/gAAAO",
"+Qr+AAAA75Cv4AAADvkK/gAAAO+Qn+AAAA75Bf//////kAfv////+QAAAAAA75AAAAAADvkAAAAAAO+QAAAAAA75AAGv///7C/////sP9wAAAA/3AAAAD/cAAAAP9wAAAA/3AAAAD/cAAAAP9wAAAA/3AAAAD/cA",
"AAABv////7IAz//////QD/YAAAb/Ef9gAAAAAA//////sQDP/////8ABv/////8AAAAAAG/xH/YAAAb/EN//////wAK/////sQAP+AAAD/gAAA/4AAAP+AAAD////A////wP+AAAD/gAAA/4AAAP+AAAD/gAAA/4",
"AAAP+AAACv///AG///wP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/IL//////0AG/////wgBf+AAAAAX/gM/xAAAA3+AD/5AAAG/2AAr/IAAO/QAAL/sA",
"CP9QAACf8wH/wAAAAf/An/MAAAAH/3/6AAAAAA7//yAAAAAAX/+AAAAAAADf4QAAAC/4AABv+QAAX/UL/gAA3/8QAL/gBf9QBP//gAH/kADvsAv//+AH/zAAj/Iv+4/3Df0AAC/5n/Qf/j/3AAAM///QCf/v8QAA",
"Bv//YAL//7AAAAD//wAAv/9QAAAAn/kAAD/+AAAAAD/yAAAM+QAAH/4QAA3/MG/9AAv/gACP+wn/oAAAr/z/wAAAAM//0QAAAAT/9gAAAAHv/+IAAADP+v/QAACf+gj/oABv/AAK/4Af/hAADf8wP/QAAAj/A/9A",
"AACP8D/0AAAI/wP/QAAAj/A/9AAACP8D/0AAAI/wP/QAAAj/A/9AAACP8C/0AAAI/wDv//////ACz/////8AAAAAAI/wAAAAAAj/AAX/////4ABf////+gAF////+hAP//////8w///////zAAAAAu//MAAABf//",
"cAAACP/+QAAACv/9IAAALf/7AAAATv/4AAAAD//1AAAAAP//////8w///////zAAjuB//gv+cM+wDPsD77Cf4wn/UB37AM+wDPsAv+cH/+AI7g/4D/gP+A/4D/gP+A/4D/gP+A/4D/gP+A/4D/gP+A/4D/gP+A/m",
"AA//QAj/gADvkADvkADv0gBf9gB/9gDvwQDvkADvkAj/gA//QA/mAG7pIACP//3WIBbP0wAAAAAAAAAAAAAAAAAAAAAAAADPsAAAAAAB/2AAAAAABv8gAAAAAAAAAAAAAAAAAAAAAA//////wgAP//////0AAAAA",
"AAX/IAAAAAAF/yAP//////8gD///////IA///////yAP9wAABf8gD/cAAAX/IAv//////yABr/////8gAAAJ/gAAAAAA75AAAAAAP/UAAAAAAAAAAAAAAAAAAAAAG/////sgC//////8AP9wAABf8Q/3AAAF/yD/",
"//////IP//////8g///////yD/cAAAAAAP9wAAAAAAv//////yAb//////IF/yCv4A75AAAAAAAA/3AP9wD/cA/3AP9wD/cA/3AP9wD/cA/3AP9wAAAB/2AAAAAAb/IAAAAACv0AAAAAAAAAAAAAAAAAAAAAG///",
"//sgC//////9AP9wAABf8Q/3AAAF/yD/cAAAX/IP9wAABf8g/3AAAF/yD/cAAAX/IP9wAABf8Qv//////QAb/////CAAAAH/cAAAAABv8gAAAAAK/QAAAAAAAAAAAAAAAAAAAAD/gAAAT/MP+AAABP8w/4AAAE/z",
"D/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/yC//////9ABv////8IAAAAAv8AAAAAAAAD/cAAAAAAABf8wAAAAAAAAAAAAAAAJ//////6AAJ////////cA3///////+wDvkAAAAAz8AO+QAA",
"AADPwA75AAAAAM/ADvkAAAAAz8AO////////wA7////////ADv///////8AO+QAAAADPwA75AAAAAM/ADvkAAAAAz8AO+QAAAADPwAAAAG/yAAAAAAAL/QAAAAAAAP+AAAAAAAAAAAAAAA7///////sA7///////",
"sA7///////sA76AAAAAAAA76AAAAAAAA76AAAAAAAA7/////+wAA7/////+wAA7/////+wAA76AAAAAAAA76AAAAAAAA7///////sA7///////sA7///////sAn+AN+gL/UAAAAO+QDvkA75AO+QDvkA75AO+QDv",
"kA75AO+QDvkA75AO+QDvkAAAAA37AAAAAAAAH/YAAAAAAABv8gAAAAAAAAAAAAAAAa//////5wAK////////UA7///////+gD/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+w",
"D/gAAAAA37AP+AAAAADfsA7///////+gCv///////1ABr//////oAAAAAA37AAAAAAAAH/YAAAAAAABv8gAAAAAAAAAAAAAAD/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+w",
"D/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA7///////+gCv///////1ABr//////oAAAH/pEAAAAAr//95AAAAwFs/TAAAAAAAAAAAAAAAAAAAP/////8IA///////QD/gAAAT/IP+AAA",
"BP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/zAABe6jABAAAAAH///dcAAAAAIQW/5QAAAAAAAAAAAAAP/zAAAADPwA//4QAAAM/AD//8AAAAz8AP//+gAADPwA/5z/cAAM/A",
"D/ke/1AAz8AP+QP/8gDPwA/5AF/9EM/AD/kACP+wz8AP+QAAr/nPwA/5AAAN///AD/kAAAHv/8AP+QAAAD//wA/5AAAABv/AAAD/fPsAAAAP98+wAAAA/3z7AAAAAAAAAAAAAAAAAAAA/4AAAE/zD/gAAAT/MP+A",
"AABP8w/4AAAE/zD/gAAAT/MP+AAABP8w/4AAAE/zD/gAAAT/MP+AAABP8gv//////QAb/////CAAAAz7j/AAAAAADPuP8AAAAAAM+4/wAAAAAAAAAAAAAA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+w",
"D/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AP+AAAAADfsA/4AAAAAN+wD/gAAAAA37AO////////oAr///////9QAa//////6AAAAAAD/0AAAAAAP/QAAAAAAAAAAAAAAAAAAAAAAAP/QAB+////8wBP",
"/////gAJ/////DAAr9AAAAAACv0AAAAAAK/QAAAAAAn9AAAAAABP//////8wfv/////zD/gP+AAAAAAP9w/4D/gP+A/4D/gP+A/4D/gP+APP/pAO///3L/AG+y/wBvsO///3A8/+kAAAAAAAAAAAAAAAAAAAAAAA",
"AAAAAAAAAAAAAAAP+I/x/2D/iP8f9g///////2D///////YP//////9gAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAP////////cA////////9wD////////3AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
"AAAAAAAF3/////8gA///////8gB/8AAAAAAACP8AAAAAAF///////zAF///////zAACP8AAAAAAACP8AAAAAAF///////zAF///////zAACP8AAAAAAAB/8AAAAAAAA///////8gAF3/////8gMKcwA0EQAAIAAE",
"AAAEAAAAAAAhAAMA9wMJAAAAACIABQD3BQkOAAAAIwAKAPcKCSUAAAAkAAoA9QoMUgAAACUADQD3DQmOAAAAJgAMAPcMCckAAAAnAAMA9wMJ/wAAACgABAD3BAkNAQAAKQAEAPcECR8BAAAqAAYA9wcJMQEAACsA",
"BgD6BgZRAQAALAADAP8DA2MBAAAtAAcA/AcEaAEAAC4AAwD/AwF2AQAALwAHAPcHCXgBAAAwAAsA9wsJmAEAADEABQD3BQnKAQAAMgALAPcLCeEBAAAzAAsA9wsJEwIAADQACQD3CglFAgAANQALAPcLCXICAAA2",
"AAsA9wsJpAIAADcACQD3CQnWAgAAOAALAPcLCf8CAAA5AAsA9wsJMQMAADoAAwD5AwdjAwAAOwADAPkDCW4DAAA8AAYA+AYIfAMAAD0ACAD6CAaUAwAAPgAGAPgHCKwDAAA/AAkA9wkJyAMAAEAACwD3CwnxAwAA",
"QQALAPcLCSMEAABCAAsA9wsJVQQAAEMACwD3CwmHBAAARAALAPcLCbkEAABFAAoA9woJ6wQAAEYACQD3CgkYBQAARwALAPcLCUUFAABIAAsA9wsJdwUAAEkAAwD3AwmpBQAASgAKAPcKCbcFAABLAAoA9woJ5AUA",
"AEwACgD3CwkRBgAATQAMAPcMCUMGAABOAAsA9wsJeQYAAE8ACwD3CwmrBgAAUAAKAPcLCd0GAABRAAsA9wwJDwcAAFIACwD3CwlFBwAAUwALAPcLCXcHAABUAAoA9woJqQcAAFUACwD3CwnWBwAAVgANAPcNCQgI",
"AABXAA8A9w8JQwgAAFgACwD3CwmHCAAAWQAKAPcLCbkIAABaAAsA9wsJ6wgAAFsABAD3BAkdCQAAXAAHAPcHCS8JAABdAAQA9wQJTwkAAF8ACwAACwFhCQAAYAADAPMDDWcJAABhAAkA+QkHewkAAGIACQD2CQqb",
"CQAAYwAJAPkJB8gJAABkAAkA9gkK6AkAAGUACQD5CQcVCgAAZgAFAPYGCjUKAABnAAkA+QkKUwoAAGgACQD2CQqACgAAaQADAPYDCq0KAABqAAP99gYNvAoAAGsACAD2CQrjCgAAbAAEAPYEChALAABtAA0A+Q0H",
"JAsAAG4ACQD5CQdSCwAAbwAJAPkJB3ILAABwAAkA+QkKkgsAAHEACQD5CQq/CwAAcgAHAPkHB+wLAABzAAkA+QkHBQwAAHQABQD2BgolDAAAdQAJAPgJCEMMAAB2AAoA+AoIZwwAAHcADgD4DgiPDAAAeAAJAPgJ",
"CMcMAAB5AAkA+AkL6wwAAHoACQD5CQcdDQAAewAEAPcECT0NAAB8AAMA9QMMTw0AAH0ABAD3BAlhDQAAfgAFAPsFBXMNAADhAAkA9AkMgA0AAOkACAD0CQy2DQAA7QADAPQDDOwNAADzAAkA9AkM/g0AAPoACQD0",
"CQw0DgAAwQALAPMLDWoOAADJAAoA8woNsg4AAM0AAwDzAw3zDgAA0wALAPMLDQcPAADaAAsA8wsNTw8AAPEACQD0CQyXDwAA0QALAPMLDc0PAAD8AAkA9QkLFRAAANwACwD0CwxHEAAAvwAJAPcJCYkQAAChAAMA",
"9wMJshAAALAABgD3BgnAEAAAJiAHAP8HAdsQAAATIAkA/AkE3xAAABQgCwD8CwTxEAAArCAKAPcKCQcRAABPJPJPJPJPJPI8EABPID+PE/jxAAAAAAAAAAAAAAAAAAAAAAAAAAPyAfUACdAG8D//////AF8QL0AA",
"nABvAADbQawAn/////gJ0AXwAA6AC7AAAACdAAAAAJ0AAC3////kjQCdAKydAJ0AAI0AnQAALf///+QAAJ0ArAAAnQCcjQCdAKwt////5AAAnQAAC/+QAACxBcAPIALeAFwA8gTtIADP+Qf6AAAAAAr3AAAAABz0",
"Pf5gAD7SCYBNAD+wAJgE0ASAAAPv9gAE7///4wAMoAAAygAMkAAAAAAK5wAAAAA/7+YAJgBfFM/VXwBfEATP/xBPEAAE3+UL////91k/I/IAAAAAAAAAAAAAAAvgT2BfEF8QXxBfEF8QT2AL4E9gGuAH8AfwB/AH",
"8AfwGuBPYACOAAWr6JBL/9gAb+wACYLBAAAAAAAAAAAAAAAAAAAAAOgAAOgAz//2AOgAAOgAAAAATxTxSAA///8AAAAAAAAAAAAAAE8QAAABgAAAygAArRAAjiAAbzAAT1AAL3AADZAAAJAAAAAK////+APyAABf",
"8E8gAH//FPIAr8XxTyG/oE8U9N+ABPFP/1AATxP+QAAF8Ar////4AADPUK/1j29QAfUAH1AB9QAfUAH1AB9QCv////gD8gAABfAAAAAATxAAAAAF8Qr////4A/IAAAAATyAAAAAE8gAAAABP/////xAL////0gTx",
"AAAMkAAAAADKAAAAAAyQAK////sAAAAABvAAAAAAXwTyAAAG8Av////3AAAABvoAAACv+gAALfrKAAT+ULoAj7EAugDv////8AAAALoAAAAAugAAAAC6AE//////FPIAAAAATyAAAAAE8gAAAABP////+AAAAAAF",
"8AAAAABPE/IAAAXxC/////gACv///4AD8gAAAABPIAAAAATyAAAAAE/////4BPIAAAXwTyAAAE8T8gAABfEK////+AD////kAAAACcAAAACdAAAACdAAAACdAAAACdAAAACdAAAACdAAAACdAAr////4A/IAAAXx",
"TyAAAE8T8gAABfEf/////gTyAAAF8U8gAABPE/IAAAXwCv////gAC/////cF8QAABvBfEAAAbwXxAAAG8Av/////AAAAAAbwAAAAAG8AAAAABvAc////9wBPEAAAAAAAAABPEF8QAAAAAAAAEF8V8FgAAAB1AD31",
"Gf1A73AA73AAGf1AAD31AAB1P///+AAAAAAAAAAAP///+AAAAAAAAAAAOAAAAv5QAALPsgAAbvEABe8QLPsgL+UAA4AAAJ////0gAAAA2AAAAA2AAAAA2ACv//0gLzAAAAAAAAAAAAAAAAPzAAAACv////gD8gAA",
"BfFPJe/jTxTy1Qek8U8tUHtPFPJe///xTyAAAAAD8gAAAAAK/////xAK////+APyAAAF8U8gAABPFPIAAATxTyAAAE8U//////FPIAAATxTyAAAE8U8gAABPED/////jA/MAAAuwPyAAAKsD8wAAC7A//////APz",
"AAAE8T8gAABPI/MAAATxP/////gACv////8T8gAAAABPIAAAAATyAAAAAE8gAAAABPIAAAAATyAAAAAD8gAAAAAK/////xBP////+ATyAAAF8U8gAABPFPIAAATxTyAAAE8U8gAABPFPIAAATxTyAAAF8U/////4",
"AE/////1TyAAAABPIAAAAE8gAAAAT////wBPIAAAAE8gAAAATyAAAABP////9U/////1TyAAAABPIAAAAE8gAAAAT////wBPIAAAAE8gAAAATyAAAABPIAAAAAr////4A/IAAAXxTyAAAAAE8gAAAABPIACP/xTy",
"AAAF8U8gAABfE/IAAAXwCv////gATyAAAB9U8gAAAfVPIAAAH1TyAAAB9U//////VPIAAAH1TyAAAB9U8gAAAfVPIAAAH1BPJPJPJPJPJPJPJPJPIAAAAAD2AAAAAPYAAAAA9gAAAAD2AAAAAPYAAAAA9vcAAAD2",
"1wAAAPVf////wE8gAAX3TyAAP5BPIAHrAE8gDNAAT///MABPIAzQAE8gAesATyAAP5BPIAAF908gAAAABPIAAAAATyAAAAAE8gAAAABPIAAAAATyAAAAAE8gAAAABPIAAAAAT/////8QT8AAAAv1T/oAAJ/1T29w",
"Bvb1Tyf1T4H1TyCf+gH1TyALwAH1TyABEAH1TyAAAAH1TyAAAAH1T8AAAF8U/7AABfFPb5AAXxTyb3AF8U8gj1BfFPIArzXxTyAAvn8U8gAA3/FPIAAB7xAK////9wTyAAAF8E8QAABfFPEAAAXxTxAAAF8U8QAA",
"BfFPEAAAXxTyAAAF8Av////3AE/////5BPIAAAXxTyAAAF8U8gAABfFP////+QTyAAAAAE8gAAAABPIAAAAATyAAAAAACv////cATyAAAF8ATxAAAF8QTxAAAF8QTxAAAF8QTxAAAF8QTxAAAF8QTyAAAF8AC///",
"///zT/////gE8gAABfBPIAAAXxTyAAAF8E/////4BPIAHsAATyAAX3AE8gAArzBPIAAA3QAL////9wTxAAAG8F8QAAAABPEAAAAAC/////cAAAAABvAAAAAAbwXxAAAG8Av////3AL/////6AADKAAAAAMoAAAAA",
"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",
"P0APkAAD9AD5j/////9yz////8EAAD9AAAAAA/QAAAn/wQAAGwA+ALcAA+4AXgCpAF/iAD4Atwf8EAAJ/8GvoAAAAAAc92/9MAAD70DzB7AAX+IB8gbQAvwQAPMHsAKgAABv/jAC3///+gAAr/////QAC9AAAC9g",
"AK0AAAAAAAu6QAAAAAT0BrUAigBPQAB8e9AE9AAAB/4gP///////YJ/////jVy9S9QAAAAAAAAAAAAAAAAnyP6FPME8wTzBPME8wTzA/oQnyP4Aa8QXzBfMF8wXzBfMF8xrxP4AAXzACZvRhj///UE/+MAj79gBp",
"C1AAAAAAAAAAAAAAAAAAAADMAADMAM///c///QDMAADMAAAAAE9E9E8jgC///2L///YAAAAAAAAAAAAAAE9E9AAAAGMAAATzAAAukAAB2wAADNEAAK4gAAf0AABfYAAA6AAAAKAAAAAI/////kAv/////8A/UAAB",
"v+A/UAA+u+A/UAf3CuA/Ub4wCuA/jrEACuA/9wAACuAv/////8AI/////kAAn6Bv+k+9pFDaAA2gANoADaAA2gANoADaCf////5AL//////AAAAAAArgAAAAAArgCP/////AH/////5AP1AAAAAAP1AAAAAAP///",
"///gP//////gCv////sAP/////9QAAAAAC9gAAAAAC9gAH////9QAH////+wAAAAAAvQAAAAAAvQP//////ACv////4wAAAAv0AAAAz/QAABz79AAB32T0AB3jBPQC3BAE9A3/////zv/////AAAAE9AAAAAT0A/",
"/////+A//////+A/UAAAAAA/UAAAAAA//////kA//////8AAAAAACuAAAAAACuAv/////8AJ/////kAI////8wL/////MD9QAAAAA/UAAAAAP/////5D//////w/UAAACuP1AAAAri//////wI/////k////+w//",
"///1AAAAH3AAAAH3AAAAH3AAAAH3AAAAH3AAAAH3AAAAH3AAAAH3CP////5AL//////QP1AAAArgP1AAAArQH/////+wH1AAAArAP1AAAArgP1AAAArgL//////ACP////5ACf////0wP/////+wTzAAAAvATzAA",
"AAvAP//////ACf/////AAAAAAAvAAAAAAAvAL/////+wB/////0wT0T0AAAAAAAAT0T0TzTzAAAAAAAAFRTzTySQAABKAAKvwBj/cA75EADvkQAAj/cAACr8AAADoC////8S////8S////8S////8QAAAAAAAAAA",
"ACkQAAL/cAACr+UAADz4AAPPgCr+UC/3AAKRAACf////gJ/////yAAAABfMAAAAF8wBe///yAO///5AA9wAAAAAAAAAAAPcAAAAA9wAAAAj////+QC//////0D9QAAAK4D9S3/oK4D9ZoA864D9ZoA9K4D9S3///",
"4D9QAAAAAC//////4Aj/////4Aj////+QB//////0D9QAAAK4D9QAAAK4D9QAAAK4D//////4D//////4D9QAAAK4D9QAAAK4D9QAAAK4C/////7AC//////YC9QAAAPcC9QAAAPcC//////YC//////wC9QAAAK",
"4C9QAAAK4C//////0C/////+QAj/////0C//////0D9QAAAAAD9AAAAAAD9AAAAAAD9AAAAAAD9AAAAAAD9QAAAAAC//////0Aj/////0D/////+QD//////0D9QAAAK4D9QAAAK4D9QAAAK4D9QAAAK4D9QAAAK",
"4D9QAAAK4D//////0D/////+QD//////A//////wP1AAAAAD9QAAAAA/////gAP////4AD9QAAAAA/UAAAAAP/////8D//////A//////wP/////8D9QAAAAA/UAAAAAP////4AD////+AA/UAAAAAP1AAAAAD9Q",
"AAAAA/UAAAAACP////5QL//////QP1AAAAAAP0AAAAAAP0AAD//QP0AAD//QP0AAAArQP1AAAArQL//////ACP////4wP1AAAAbxP1AAAAbxP1AAAAbxP1AAAAbxP//////xP//////xP1AAAAbxP1AAAAbxP1AA",
"AAbxP1AAAAbxP1P1P1P1P1P1P1P1P1P1AAAAAG8gAAAABvIAAAAAbyAAAAAG8gAAAABvIAAAAAbyAAAAAG8vkAAABvLf/////xTv////cD9QAAC/Q/UAAK9gP1AAj4AD9QB/sAA////QAAP///0AAD9QB/sAA/UA",
"CPgAP1AACvYD9QAAC/M/UAAAAAP1AAAAAD9QAAAAA/UAAAAAP1AAAAAD9QAAAAA/UAAAAAP1AAAAAD//////4//////+P+EAAAHvM//AAADf8z+foAC/nzP0f4CPdPM/QJ+vkE8z9AC/sATzP0ABsQBPM/QAAAAE",
"8z9AAAAATzP0AAAABPM/4QAACtA//AAACtA/n6AACtA/R/gACtA/QJ9gCtA/QAv0CtA/QADeKtA/QAAu29A/QAAD/9A/QAAAX9AJ/////kAv/////8BPQAAAC9BPQAAACtBPQAAACtBPQAAACtBPQAAACtBPQAAA",
"C9Av/////8AJ/////kA//////jP//////D9QAAAK0/QAAACtP1AAAArT//////w//////jP0AAAAAD9AAAAAA/QAAAAACf////5AAv/////8AE9AAAAL0AT0AAAArQBPQAAACtAE9AAAAK0AT0AAAArQBPQAAAC9",
"AC///////xCf//////E//////jA//////7A/QAAACtA/QAAACtA/QAAACtA//////7A//////jA/QAB/gAA/QAAH+AA/QAAAf3AJ/////kA//////8BPMAAAAABPMAAAAAA//////TAJ/////7AAAAAAC8AAAAAA",
"C8BP/////7AK/////TC//////1v/////9QAAfxAAAAAH8QAAAAB/EAAAAAfxAAAAAH8QAAAAB/EAAAAAfxAAAAAH8QAAT0AAAArQT0AAAArQT0AAAArQT0AAAArQT0AAAArQT0AAAArQT0AAAArQT0AAAAvQL///",
"///ACf////5AP4AAAAAG9QryAAAADsAB+gAAAI8wAH9AAAL5AAAN0AAL8QAABfYAT3AAAAC+EN0AAAAAL5f0AAAAAAn/sAAAAAAB7yAAAF9AAAvzAADNAOoAAf+QAC9wCfAAf88ACPEAP2ANxPUA2wAA3AP2DrA/",
"UAAI8Z8QjxnwAAAvjqAC9/oAAADP9AAM/0AAAAb+AAB/4AAAAA+QAAH4AAAvwAAAf3BPsABfkABvgD/AAACfftEAAAC/4gAAAAv+IAAACfftEAAG+AP7AAT7AAX5Av0AAAf3b2AAAC+gCvMAAd0AAN4QC/MAAD/A",
"j3AAAAb7+wAAAACv4QAAAAAvYAAAAAAfYAAAAAAfYAAAAAAfYAAAT//////AT/////+wAAAAAcoAAAAAPnAAAAAG5AAAAACsEAAAAC2QAAAABOYAAAAAP//////AT//////AT/JP8k9AT0BPQE9AT0BPQE/yT/Kg",
"AAAA6AAAAF9gAAAH8wAAAK4gAAAM0QAAAdsAAAAvkAAABPIAAABjT/JP8gbyBvIG8gbyBvIG8k/yT/JP/////9BP/////9BvEvUAAAAAAAAAAAAAAAAAAAAAAABP///+UE/////gAAAACPBP////8E/////wTzAA",
"CPAv////8An////wT0AAAABPQAAAAE9AAAAAT////mBP////8E9AAAjwT0AACPBPQAAI8E9AAAjwT/////BP///+YAn////wP/////BPMAAAAE8wAAAATzAAAABPMAAAAD/////wCf////AAAAAPkAAAAPkAAAAP",
"kt////mf////mtAAAPmtAAAPmtAAAPmtAAAPmf////kt////kAn///5QP////+BPMAAI8E/////wT/////BPMAAAAD/////wCf////AJ//k///lPQABP//lP//lPQABPQABPQABPQABPQABPQAAL///+QF/////A",
"bxAAC9BvEAAK0G8QAArQbxAAC9Bf////0Av////QAAAAC9AA////wAD///5AT0AAAABPQAAAAE9AAAAAT////lBP////8E9AAAjwT0AACPBPQAAI8E9AAAjwT0AACPBPQAAI8E808wIE808080808080808wAADa",
"AADaAACoAADaAADaAADaAADaAADaAADaAADaAADaAADar//3r//BT0AAAAT0AAAAT0AABET0AAn2T0AI9wT0B/kAT//7AAT//+IAT0Bv0QT0AG/AT0AAb6BPMATzAE8wBPMATzAE8wBPMATzAE9AA//xCf8QT///",
"///+UE///////+BPQADqAAnwT0AA6QAI8E9AAOkACPBPQADpAAjwT0AA6QAI8E9AAOkACPBP///+YE/////wT0AACPBPQAAI8E9AAAjwT0AACPBPQAAI8E9AAAjwCf///lA/////4E8wAAjwTzAACPBPMAAI8E8w",
"AAjwP////+AJ///+UE////5gT/////BPQAAI8E9AAAjwT0AACPBPQAAI8E/////wT////mBPQAAAAE9AAAAAT0AAAAAt////iv////i9AAAPi8AAAPi8AAAPi9AAAPiv////gt////gAAAAPgAAAAPgAAAAPgAn/",
"//E////xT0AAAE8wAABPMAAATzAAAE8wAABPMAAACf///lA/////4F8wAAAAP////kAK////0AAAAAnwT////9AK///+QE9AAE9AAE9AAE//+U//+U9AAE9AAE9AAE9AAD//+Qn/+U9AAAjwT0AACPBPQAAI8E9A",
"AAjwT0AACPBPQAAI8D/////gCf///mBvUAAAP3DdAAAM4AT2AAX1AAvgAOwAAD+AfzAAAJ8/oAAAAf/yAAAACPgAAF9AAJ+QAE9A6wAf/xAL4AjyB/n4AfgAH4DtDfB/IAC+b2BvfcAABf/wAO/2AAAO+AAH/wAA",
"AI8gAB+gAC/QAD/ABPsB7RAAb53iAAAI/zAAAAn/QAAAf3zyAAT6Ae4QL8AAP8BvEAAK0G8QAArQbxAACtBvEAAK0G8QAArQbxAACtBf////0Av////QAAAACtAA////wAD///5AT/////BP////4AAAAaoQAABN",
"YAAACMIAAALHAAAAL/////BP////8Ab1D8IfcB9wrSCeMB9wH3APwgb1T0T0T0T0T0T0T0T0T0T0T0T0T0T0T3Ar8AbyBvIB2wLqBvIG8ivxT3CfoxEQXfMAAAAAAAAAAAAAAJ4AAAAA2gAAAAAAAAAAAAAAAE//",
"//5QT////+AAAAAI8E/////wT/////BPMAAI8C/////wCf////AAAvUAAABvEAAAAAAAAAAAAAAAAAAAAJ///+U/////5PMAAI9P////9P////9PMAAAA/////8J////8A6S9QAAAE808080808080808wAAywAA",
"AAH3AAAAAAAAAAAAAAAAAAAAAAAJ///+UD/////gTzAACPBPMAAI8E8wAAjwTzAACPA/////4An///5QAADLAAAAAPcAAAAAAAAAAAAAAAAAAAAAAE9AAAjwT0AACPBPQAAI8E9AAAjwT0AACPBPQAAI8D/////g",
"Cf///mAAAAywAAAAAA9wAAAAAAAAAAAAAAAAAAAI/////kAf/////9A/UAAACuA/UAAACuA/UAAACuA//////+A//////+A/UAAACuA/UAAACuA/UAAACuAAAE8wAAAACPAAAAAAAAAAAAAAAAAAP/////8D////",
"//A/UAAAAAP1AAAAAD////+AA/////gAP1AAAAAD9QAAAAA//////wP/////8B9l8gAAAD9T9T9T9T9T9T9T9T9T9QAADaAAAAAAH2AAAAAAAAAAAAAAAAAAAAn////+QC//////wE9AAAAL0E9AAAAK0E9AAAAK",
"0E9AAAAK0E9AAAAK0E9AAAAL0C//////wAn////+QAAADaAAAAAAH2AAAAAAAAAAAAAAAAAAAE9AAAAK0E9AAAAK0E9AAAAK0E9AAAAK0E9AAAAK0E9AAAAK0E9AAAAK0E9AAAAL0C//////wAn////+QAB/tAEA",
"ABBM9QAAAAAAAAAAAAAAT////mBP////8E9AAAjwT0AACPBPQAAI8E9AAAjwT0AACPBPQAAI8AAJ+jEQAAABBd8wAAAAAAAAAAAAAAAAAD/hAAAK0D/8AAAK0D+foAAK0D9H+AAK0D9An2AK0D9AC/QK0D9AAN4q",
"0D9AAC7b0D9AAAP/0D9AAABf0AAfa8AAAB9rwAAAAAAAAE9AAAjwT0AACPBPQAAI8E9AAAjwT0AACPBPQAAI8D/////gCf///mAAAvXLAAAAAvXLAAAAAAAAAABPQAAACtBPQAAACtBPQAAACtBPQAAACtBPQAAA",
"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",
"UF7/////kHUfoB+gH6AAAAAAAAAAAAAAAAAAAAAAAAAF6Q/3L5AvkC+QL5AvkC+QL5AvkA/3BukfsB33AfoB+gH6AfoB+gH6AfoB+h33H7AAD8AAAg/AMF/f7vI7//+iAM/6AAf6z1ADwSsgAAAAAAAAAAAAAAAA",
"AAAAAAAAAAAAb0AABvQAv///q///+gBvQAAG9AAAAAAAAAAAL5L5L3KwH///9R////UAAAAAAAAAAAAAAAAAAAAAL5L5AAAABjAAAAP0AAAB7hAAAM8wAACfUAAAb4AAAD+wAAAe0QAADPMAAAn1AAAA6AAAAAoA",
"AAAABO/////5AO//////9B+gAAAH/2H6AAAJ/vcfoAAc+l9x+gAt+AT3H6BO9QBPcfpv4wAE9x/v0gAAT3H/sQAABfYO//////9AXv////+QAC/1Ad/1C/31j7b1AAb1AAb1AAb1AAb1AAb1AAb1AAb1AAb1BO//",
"///5AO//////9B+gAAAAX2AAAAAABPcAAAAAAF9gTv/////0Dv/////5AfoAAAAAAB+gAAAAAAH6AAAAAAAf//////9x///////3Be/////SAP//////sC+QAAAA3gAAAAAADeAAAAAAAN0AAf/////AAB//////",
"MAAAAAAG9QAAAAAAX2L5AAAABvUO//////8wXv////+AAAAADPcAAAABz/cAAAAd//cAAALfxvcAAC76BPcAA+9wBPcAP/QABPcA7//////y7//////yAAAABPcAAAAABPcAAAAABPcAH///////cf//////9x+g",
"AAAAAAH6AAAAAAAfoAAAAAAB//////+QH///////QAAAAAAF9gAAAAAAT3H6AAAABfYO//////9ATv////+QBO////+AAO/////4AB+gAAAAAAH6AAAAAAAfoAAAAAAB//////+QH///////QfoAAAAF9h+gAAAA",
"T3H6AAAABfYO//////9AXv////+Q/////7AP/////3AAAAAB+gAAAAAfoAAAAAH6AAAAAB+gAAAAAfoAAAAAH6AAAAAB+gAAAAAfoAAAAAH6AAAAAB+gBO/////5AO//////9R+gAAAAX3H6AAAABPcfoAAAAF9g",
"3//////zD///////UfoAAAAF9h+gAAAAT3H6AAAABfYO//////9AXv////+QBu/////3Af//////8i+QAAAAb1P4AAAABvUvkAAAAG9R///////1Bu//////UAAAAAAG9QAAAAAAb1AAAAAABvUP//////8gXv//",
"//+AL5L5AAAAAAAAAAAAL5L5P4P4AAAAAAAAAAAALGP4P2KwAAAFgAADz6ACv/kQj/sgAO9wAACP+iAAAq/5EAADz6AAAAWAH/////Qf////9AAAAAAAH/////Qf////9AAAAAAAAAAAAAAKIAAAD/kQAATP9wAA",
"Be/kAAAd+AAF79MDz+cAD/kQAAsgAACP////+Qj/////9QAAAAA/gAAAAAP4AAAAAD+AAAAAA/gALP///1AK////kADPAAAAAAAAAAAAAM8AAAAADPAAAAAE7/////gA7//////0H6AAAABfYfoAAAAE9x+gbv+Q",
"T3H6D1APVPcfovQA909x+g9QD3T3H6Bu////cfoAAAAAAA7//////3Be//////cE7/////kA7//////0H7AAAABfcfoAAAAE9x+gAAAAT3H6AAAABPcf//////9x///////3H6AAAABPcfoAAAAE9x+gAAAAT3H6",
"AAAABPcf/////9MB///////QH7AAAADPAfoAAAAM8B+wAAAAzwH//////+Af//////9R+wAAAAT3H6AAAABPcfsAAAAE9x///////0H//////5AE7/////9g///////2H6AAAAAAAfoAAAAAAB+gAAAAAAH6AAAA",
"AAAfoAAAAAAB+gAAAAAAH6AAAAAAAfoAAAAAAA///////2Be//////Yf//////kB///////0H7AAAABfcfoAAAAE9x+gAAAAT3H6AAAABPcfoAAAAE9x+gAAAAT3H6AAAABPcfsAAAAF9x///////0H//////5Af",
"//////cf//////cfoAAAAAAfoAAAAAAfoAAAAAAf/////AAf/////AAfoAAAAAAfoAAAAAAfoAAAAAAf//////cf//////cf//////cf//////cfoAAAAAAfoAAAAAAfoAAAAAAf/////AAf/////AAfoAAAAAAf",
"oAAAAAAfoAAAAAAfoAAAAAAfoAAAAAAF7/////gA///////zH6AAAABfYfoAAAAAAB+gAAAAAAH6AAAAAAAfoAAA//9h+gAAD//2H6AAAABfYfoAAAAF9g///////0Be/////5AfoAAAAA+wH6AAAAAPsB+gAAAA",
"D7AfoAAAAA+wH6AAAAAPsB///////7Af//////+wH6AAAAAPsB+gAAAAD7AfoAAAAA+wH6AAAAAPsB+gAAAAD7AfoB+gH6AfoB+gH6AfoB+gH6AfoB+gH6AAAAAAAvkAAAAAAvkAAAAAAvkAAAAAAvkAAAAAAvkA",
"AAAAAvkAAAAAAvkAAAAAAvkAAAAAAvn9AAAAAvnf//////ZN/////6AfoAAAB/wB+gAABP4QH6AAAv8wAfoAAd9gAB+gAL+QAAH////AAAAf///8AAAB+gAL+QAAH6AAHfYAAfoAAC/zAB+gAABP4QH6AAAAf8Af",
"oAAAAAAB+gAAAAAAH6AAAAAAAfoAAAAAAB+gAAAAAAH6AAAAAAAfoAAAAAAB+gAAAAAAH6AAAAAAAfoAAAAAAB///////3H///////cf9QAAAAj/Af/zAAAF//Af3+IAA//vAfp/0ALvTPAfoJ+x33DPAfoAz++Q",
"DPAfoAHfwADPAfoAAsEADPAfoAAAAADPAfoAAAAADPAfoAAAAADPAfoAAAAADPAf9QAAAF9h//MAAAX2H9/hAABfYfp/sAAF9h+gr5AAX2H6AN9gBfYfoALvMF9h+gAE/hX2H6AAB/xfYfoAAAr99h+gAAAM/2H6",
"AAAAHvYF7/////gA///////zL6AAAABvYvkAAAAF9i+QAAAAX2L5AAAABfYvkAAAAF9i+QAAAAX2L5AAAABfYvoAAAAG9g///////zBe/////4Af//////gB///////zH6AAAABfYfoAAAAF9h+gAAAAX2H6AAAA",
"BfYf//////9B//////+AH6AAAAAAAfoAAAAAAB+gAAAAAAH6AAAAAAAF7/////gAD///////MC+gAAAAb2AvkAAAAF9gL5AAAABfYC+QAAAAX2AvkAAAAF9gL5AAAABfYC+QAAAAX2AvoAAAAG9gD////////QXv",
"//////0v//////gC///////zL6AAAABfYvkAAAAF9i+QAAAAX2L6AAAABfYv//////8y//////+AL5AACvkAAvkAAAz3AC+QAAAd9QL5AAAALvMF7/////cA///////yL5AAAABvU/gAAAAAAC+QAAAAAAD/////",
"/3AG7/////8wAAAAAAb1AAAAAABvUvkAAAAG9Q///////yBe/////3C///////2///////0AAAzwAAAAAAzwAAAAAAzwAAAAAAzwAAAAAAzwAAAAAAzwAAAAAAzwAAAAAAzwAAAAAAzwAAAAAAzwAAAvkAAAAF9i",
"+QAAAAX2L5AAAABfYvkAAAAF9i+QAAAAX2L5AAAABfYvkAAAAF9i+QAAAAX2L5AAAABfYvoAAAAG9g///////zBe/////4Av0AAAAAAK9An2AAAAAD+wAf4AAAAAzzAAj3AAAAX6AAAO8QAADfEAAAb5AAB/gAAA",
"AN8gAe4AAAAAT7AI9gAAAAAL9C/QAAAAAAL8r1AAAAAAAJ/8AAAAAAAAH/MAAABPkAAAr4AAAL8Q7gAAD/4AAB/ACfQABf/zAAb2AD+QAL9vkADPEADfAB/A7gAfsAAI9Qb2CfQH9gAAL6DPED+QzwAAAN8vsADf",
"L6AAAAf89gAI/PUAAAAv/wAAL/8AAAAAz6AAAN+gAAAABvUAAAf0AAAe8wAAA/4QT+IAAu9AAH/QAN9gAACvsL+gAAAAz9/AAAAAAe/hAAAAAB7+EAAAAAz9/AAAAAr7C/kAAAf9AA32AAT+IAAu9AHvMAAAP+Fv",
"oAAAAM9Ar3AAAJ+AAe9AAG/QAAT+ID/yAAAI/B72AAAADf/7AAAAAC/+EAAAAACPYAAAAAAG9QAAAAAAb1AAAAAABvUAAAAAAG9QAAA///////9T///////1AAAAAAj8EAAAAAr6AAAAABz4AAAAAC72AAAAAE/0",
"AAAAAG/SAAAAAI/BAAAAAK+gAAAAAD///////1P///////Uv+S/5L5AvkC+QL5AvkC+QL5AvkC/5L/mQAAAADoAAAACvUAAAAM8gAAAB7RAAAAP7AAAABvgAAAAJ9QAAAAzyAAAAHtEAAAA/MAAAAGM/+T/5AvkC",
"+QL5AvkC+QL5AvkC+T/5P/kv//////9i///////2b1L4D8AAAAAAAAAAAAAAAAAAAAAAAAAAL////+cC//////IAAAAAf0L/////9C//////QvkAAAf0L5AAAH9A//////QF7////0AvkAAAAAL5AAAAAC+QAAAA",
"Av////9wL/////8i+QAAB/QvkAAAb0L5AAAG9C+QAABvQvkAAAf0L/////8i/////3AG7////zH/////8z+QAAAAA/gAAAAAP4AAAAAD+AAAAAA/kAAAAAH/////9Abv////QAAAAADtAAAAAA7QAAAAAO0Bv///",
"/9CP/////QrxAAAP0K8QAADtCvEAAA7QrxAAAO0K8QAAD9CP/////QG/////0Abv///nAf/////yP5AAAH9D//////Q//////0P4AAAAAD+QAAAAAf/////0Bu////9ABu//YP//9i+QAAL///Yv//9i+QAAL5AA",
"AvkAAC+QAAL5AAAvkAAC+QAACP///+QD//////BfYAAArxX2AAAK8V9gAACvFfYAAArxX2AAAK8T//////EI/////xAAAAAK8QAAAACvEAv////wAL///+UAL5AAAAAC+QAAAAAvkAAAAAL/////cC//////IvoA",
"AAf0L5AAAG9C+QAABvQvkAAAb0L5AAAG9C+QAABvQvkAAAb0L5L5BCL5L5L5L5L5L5L5L5L5AACvEAAK8QAAIwAACvEAAK8QAArxAACvEAAK8QAArxAACvEAAK8QAArxAACvEAAL8P///Q///TAvkAAAAAL5AAAA",
"AC+QAALLEvkAAu9AL5AB31AC+QDPcAAv//+QAAL///oAAC+QHfcAAvkAHvUAL5AAP/MC+QAAT+EvkAL5AC+QAvkAL5AC+QAvkAL5AC+QAvkAH/+gbvov///////8IC////////+gL6AAH7AADsAvkAAPsAAOwC+Q",
"AA+wAA7AL5AAD7AADsAvkAAPsAAOwC+QAA+wAA7AL5AAD7AADsAv////9wL/////8i+gAAB/QvkAAAb0L5AAAG9C+QAABvQvkAAAb0L5AAAG9C+QAABvQAbv///nAf/////yP5AAAI8z+AAAB/Q/gAAAf0P4AAAH",
"9D+QAAB/Mf/////yBu///+cAL/////cC//////IvkAAAf0L5AAAG9C+QAABvQvkAAAb0L5AAAH9C//////Iv////9wL5AAAAAC+QAAAAAvkAAAAAL5AAAAAAG/////wJ/////8C/EAAA/AvwAAAPwL8AAAD8C/AA",
"AA/AvxAAAPwJ/////8Ac/////AAAAAAPwAAAAAD8AAAAAA/AAAAAAPwABu///xH////xL5AAAAL5AAAAL5AAAAL5AAAAL5AAAAL5AAAAL5AAAAAH7///5wL/////8j+AAAAAAv////5QB/////8AAAAACPMAAAAA",
"jzL/////8Qj////lAC+QAAL5AAAvkAAC///2L///YvkAAC+QAAL5AAAvkAAC+QAAD///YG7/9i+QAAB/QvkAAAf0L5AAAH9C+QAAB/QvkAAAf0L5AAAH9C+QAAB/QP/////yBu////cAb5AAAADuEM8wAACPcAP7",
"AAAv0AAK9AAK9AAAL9AD+wAAAI9gzyAAAADub5AAAAAG//EAAAAADfcAAAA/kAAK/AAAf2DfEAH/9AAN8Ab3AI/PsAT5AB/QD/HfMK8wAJ9H+Qb7H9AAA/vfIA759wAADP+wAH//EAAAb/QAAf+gAAAA/QAACPQA",
"AB7zAAP/ID/iAe9AAE/Rz1AAAG//cAAAAM/QAAAAj++QAABfwL9gAD/hAd9AHvMAAv8gX2AAAJ8V9gAACfFfYAAAnxX2AAAJ8V9gAACfFfYAAAnxX3AAAK8T//////EI/////xAAAAAJ8QAAAACvEAv////wAL//",
"/+UAL/////9C//////QAAAAK9wAAAD3TAAAAf5AAAALOUAAABfwQAAAC//////Qv/////0AD3QDPoA7AAOwAH8AK5ACfYAD8AA7AAOwADPoAPdAvkvkvkvkvkvkvkvkvkvkvkvkvkvkvkD+gAt9gAvgAL5AC+wAI",
"9AC/MC+QAvkAL4At9gP6AI/GEgEDr+AAAAAAAAAAAAAAAAAAAAAADdAAAAAAH6AAAAAAT2AAAAAAAAAAAAAAAAAAAC/////nAC//////IAAAAAB/QC//////QC//////QC+QAAB/QC+QAAB/QA//////QAXv////",
"QAAAjyAAAAAM8AAAAAD7AAAAAAAAAAAAAAAAAABu///+cB//////I/kAAAf0P/////9D//////Q/gAAAAAP5AAAAAB//////QG7////0C/AO0B+QAAAAAC+QL5AvkC+QL5AvkC+QL5AvkAAAH5AAAAAF9gAAAACP",
"IAAAAAAAAAAAAAAAAABu///+cB//////I/kAAAjzP4AAAH9D+AAAB/Q/gAAAf0P5AAAH8x//////IG7///5wAAAfoAAAAAT2AAAAAI8wAAAAAAAAAAAAAAAAAvkAAAf0L5AAAH9C+QAAB/QvkAAAf0L5AAAH9C+Q",
"AAB/QvkAAAf0D/////8gbv///3AAAAD8AAAAAAAvgAAAAAAG9QAAAAAAAAAAAATv////+QDv//////QfsAAAAF9x+gAAAAT3H6AAAABPcfoAAAAE9x///////3H///////cfoAAAAE9x+gAAAAT3H6AAAABPcfoA",
"AAAE9wAACPMAAAAAC/AAAAAADsAAAAAAAAAAAB//////9x//////9x+gAAAAAB+gAAAAAB+gAAAAAB/////8AB/////8AB+gAAAAAB+gAAAAAB+gAAAAAB//////9x//////9w7QH5BfYAAAH6AfoB+gH6AfoB+g",
"H6AfoB+gH6AfoB+gAAAA+wAAAAAAP3AAAAAAB/QAAAAAAAAAAAAF7/////gA///////zL6AAAABvYvkAAAAF9i+QAAAAX2L5AAAABfYvkAAAAF9i+QAAAAX2L5AAAABfYvoAAAAG9g///////zBe/////4AAAAD7",
"AAAAAAA/cAAAAAAH9AAAAAAAAAAAAC+QAAAAX2L5AAAABfYvkAAAAF9i+QAAAAX2L5AAAABfYvkAAAAF9i+QAAAAX2L5AAAABfYvkAAAAF9i+gAAAAb2D///////MF7/////gAAe6TAgAAABbfYAAAAAAAAAAAAA",
"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",
"AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAL8wAO8QAAD+AAP7AAAF+QAI9gDf///////A3///////wABPoAB/cAAAr0AA3xAAAP4AAvwABv///////zb///////8wDvAAH9AAAD+wAG+AAACPYAC/MA",
"AAAAAO8QAAAAAADvEAAABu//////kC////////ZfkADvEAb5b5AA7xAAAG+QAO8QAABfkADvEAAAL///////kAbv//////YAAADvEAb5AAAA7xAG+W+QAO8QBvk////////2B+//////kAAAAO8QAAAAAADvEAAA",
"BN/9QAAAAIUA7//+AAAAr1AvcAfyAAHP4gL3AH8gA+/BAA7//+AF/7AAAE3/1Af/gAAAAAAACv9gAAAAAAAc/jG//oAAAC39IJ///0AAT/sQDMAC9wBf+QAAzAAvcAr2AAAJ///0AJQAAAAb/+gAAF7////+cAAA",
"L///////MAAF+gAAAAn2AABfoAAAAAAAAAT6AAAAAAAAAD/8QAAAAAAADvn/xAAAQwAA/gGP/EAP4AAP4AAY/8T+AAD+AAABn//gAA/gAAAAGf/lAN///////9/zA9//////whkwD/AP8A/wAAAAAAAAAAAAAAAA",
"AAAAAAAAAAADzwDf8A/gAf4AH+AB/gAf4AH+AB/gAf4AD+AA3/AD3wAP0wD/4ADfEA3xAN8QDfEA3xAN8QDfEA3xAN8Q/+AP0wAACfYAAACfYAAvq/q+Bv////MCn/+BAAv/+QAG/j/zAApAeAAAAAAAAAAAAAAA",
"AAAAAAAAAAAAAAAAAAAf0AAAH9AAAB/QAL////i////4AB/QAAAf0AAAAAAAAAAAAA/g/g/Awg////9A////9AAAAAAAAAAAAAAAAAAAAAAAAA/gD+AAAAAAZAAAAAT0AAAALvIAAADfQAAAC/cAAACfkAAABvwA",
"AABP0QAAAu8gAAAN9AAAAL9wAAAA6QAAAACgAAAAAALP/////8IAz///////wA/wAAAATv8A/wAAAG//8A/wAACf9v8A/wABv+QP8A/wAt/SAP8A/wTvsQAP8A/2/5AAAP8A//9gAAAP8A//QAAAAP8Az///////",
"wALP/////8IAAAv/AAn/8Ab//wT/T/BWQP8AAA/wAAD/AAAP8AAA/wAAD/AAAP8AAA/wAAD/AALP/////8IAz///////sA/wAAAAAP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP8ALP//////sAz//////8IA/wAAAA",
"AAAA/wAAAAAAAA/wAAAAAAAA////////8A////////8AA8/////+YADf//////8gD+AAAAAJ9QAAAAAAAJ9gAAAAAAAJ9gAAv/////9AAAv/////9wAAAAAAAB/QAAAAAAAA/gAAAAAAAA/gD+AAAAAB/gDf////",
"//+gA8//////wQAAAAABz6AAAAAB3/oAAAAC3/+gAAAC7+n6AAAD79JfoAAE/8EF+gAF/6AAX6AG/4AABfoA7///////jv//////+AAAAABfoAAAAAAF+gAAAAAAX6AAD////////wD////////wD/AAAAAAAAD/",
"AAAAAAAAD/AAAAAAAAD///////wgD///////+wAAAAAAAA/wAAAAAAAA/wAAAAAAAA/wD/AAAAAA/wDP//////+wAs//////wgACz/////0AAM//////0AAP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP///////CAP",
"///////7AP8AAAAAD/AP8AAAAAD/AP8AAAAAD/AP8AAAAAD/AM///////7ACz//////CAP/////7EP//////oAAAAAAv0AAAAAAf0AAAAAAf0AAAAAAf0AAAAAAf0AAAAAAf0AAAAAAf0AAAAAAf0AAAAAAf0AAA",
"AAAf0AAAAAAf0ALP/////8IAz///////wA/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A3///////4Ar///////oA7wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8Az///////wALP/////8IAA9//////sQDf////",
"//+gD+AAAAAB/QH9AAAAAB/gH9AAAAAB/gD+AAAAAB/gDf///////gA8///////gAAAAAAAB/gAAAAAAAB/gAAAAAAAB/QDf//////+gA9//////sQAP4A/gAAAAAAAAAAAAAAAAAAAP4A/gH9H9AAAAAAAAAAAA",
"AzH9H9H6HBAAAABmAAADz3AAGf/jAG7/gAC//CAADvsAAAC//CAAAF7/gAAAGf/jAAADz3AAAABmAA//////YP/////2AAAAAAAA//////YP/////2AAAAAAAAAAAAAAAAAAAAAACiAAAAD/gAAACf/lAAADz/sg",
"AABv/0AAAD/3AAB//0AD3/sgCf/kAAD/gAAACiAAAAB//////7F///////kAAAAAAv0AAAAAAf0AAAAAAf0AAAAAAv0ACO////kAX////7EAf3AAAAAAAAAAAAAAAAAAAAAAj3AAAAAAj3AAAAACz//////CAM//",
"/////7AP8AAAAAD/AP8An/+QD/AP8F///2D/AP8J8AD5D/AP8K8ADqD/AP8J8ADqD/AP8F//////AP8An/////AP8AAAAAAAAM////////ACz///////AALP/////8IAv///////wA/wAAAAAP8A/wAAAAAP8A/w",
"AAAAAP8A/wAAAAAP8A////////8A////////8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8AD//////+cAD///////9AD/AAAAAI9wD/AAAAAH9wD/AAAAAI9wD///////9QD///////+QD/",
"AAAAAA/wD/AAAAAA7wD/AAAAAA7wD/AAAAAA/wD////////AD///////wgACz///////AM////////AP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP",
"8AAAAAAAAM////////ACz///////AA///////8IA////////wA/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A/wAAAAAP8A////////wA///////8IA",
"D///////4A///////+AP8AAAAAAAD/AAAAAAAA/wAAAAAAAP8AAAAAAAD//////wAA//////8AAP8AAAAAAAD/AAAAAAAA/wAAAAAAAP///////gD///////4A///////+D///////4P8AAAAAAA/wAAAAAAD/AA",
"AAAAAP8AAAAAAA//////8AD//////wAP8AAAAAAA/wAAAAAAD/AAAAAAAP8AAAAAAA/wAAAAAAACz//////CAM///////8AP8AAAAAD/AP8AAAAAAAAP8AAAAAAAAP8AAAAAAAAP8AAAD///AP8AAAD///AP8AAA",
"AAD/AP8AAAAAD/AP8AAAAAD/AM///////8ACz//////CAA/wAAAAAK9A/wAAAAAK9A/wAAAAAK9A/wAAAAAK9A/wAAAAAK9A/wAAAAAK9A////////9A////////9A/wAAAAAK9A/wAAAAAK9A/wAAAAAK9A/wAA",
"AAAK9A/wAAAAAK9AD/AP8A/wD/AP8A/wD/AP8A/wD/AP8A/wD/AAAAAAAA7wAAAAAAAO8AAAAAAADvAAAAAAAA7wAAAAAAAO8AAAAAAADvAAAAAAAA7wAAAAAAAO8AAAAAAADvDvAAAAAA7w7xAAAAAO8K//////",
"/8Ab//////wgD/AAAAA/9A/wAAAB73AP8AAAC/oAD/AAAI/AAA/wAAT+EAAP8AAe8gAAD////4AAAA/////yAAAP8AAd/hAAD/AAAu/AAA/wAAAu+gAP8AAAA/9wD/AAAABP9A/wAAAAAAAP8AAAAAAAD/AAAAAA",
"AA/wAAAAAAAP8AAAAAAAD/AAAAAAAA/wAAAAAAAP8AAAAAAAD/AAAAAAAA/wAAAAAAAP8AAAAAAAD////////w////////8P+wAAAAAu+wD/+QAAAA3/sA//9gAAC/77AP9P9AAI/l+wD/B/8gb/NPsA/wCf1f9Q",
"T7AP8AC//3AE+wD/AAHfoABPsA/wAAKwAAT7AP8AAAAAAE+wD/AAAAAABPsA/wAAAAAAT7AP8AAAAAAE+wAP+wAAAAD/AP/5AAAAD/AP//YAAAD/AP9P9AAAD/AP8H/iAAD/AP8An9EAD/AP8ADPsAD/AP8AAd+Q",
"D/AP8AAC/2D/AP8AAAT/T/AP8AAABv//AP8AAAAJ//AP8AAAAAv/AALP/////8IA3///////sA/wAAAAAf4A/gAAAAAP8A/gAAAAAP8A/gAAAAAP8A/gAAAAAP8A/gAAAAAP8A/gAAAAAP8A/gAAAAAP8A/wAAAA",
"AP4A3///////sALP/////8IAD///////wg////////wP8AAAAAD/D/AAAAAA/w/wAAAAAP8P8AAAAAD/D////////A///////8IP8AAAAAAAD/AAAAAAAA/wAAAAAAAP8AAAAAAAD/AAAAAAAALP/////8IADf//",
"////+wAP8AAAAAH+AA/gAAAAAP8AD+AAAAAA/wAP4AAAAAD/AA/gAAAAAP8AD+AAAAAA/wAP4AAAAAD/AA/gAAAAAP8AD/AAAAAA/gAN////////+ALP///////4D///////wgD////////AD/AAAAAA/wD/AAAA",
"AA/wD/AAAAAA/wD/AAAAAA/wD////////AD///////wgD/AAAM+gAAD/AAAC73AAD/AAAAT/QAD/AAAACP4QD/AAAAAL/AADz/////+xAN///////6AP4AAAAAH9Af0AAAAAAAAf0AAAAAAAAP4AAAAAAAAN////",
"//+xACz//////7AAAAAAAAH9AAAAAAAAH+Af4AAAAAH9AO///////7AD3/////+xAK////////Wv///////1AAAC/QAAAAAAAv0AAAAAAAL9AAAAAAAC/QAAAAAAAv0AAAAAAAL9AAAAAAAC/QAAAAAAAv0AAAAA",
"AAL9AAAAAAAC/QAAAAAAAv0AAAAP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP4AAAAAD/AP8AAAAAD+AN///////7ACz//////CAB/y",
"AAAAAAAe8wj7AAAAAACfoADvUAAAAAL/IABf0AAAAAv4AAAM9wAAAE/gAAAD/xAAAN9QAAAAr5AAB/wAAAAAH/MAHvMAAAAAB/wAn6AAAAAAAN9S/xAAAAAAAF/s9wAAAAAAAAv/4AAAAAAAAAL/UAAAAD/gAAAJ",
"/QAAAK9g3zAAAO/yAAAP8Qf5AABf/4AABvoAH/AAC/j+AADPUAC/UAH/DPQAH+AABvsAb6BvoAf5AAAP8Qz0Af8A3zAAAK9i/gAL9T/QAAAE/I+QAF+5+AAAAA7+8wAA/+8gAAAAn/0AAAn/wAAAAAP/cAAAT/YA",
"AAAADfEAAADvEAAAHvgAAAAd+AA/9gAADPsAAF/0AAn9EAAAf+IH/iAAAACv1f9AAAAAAM//YAAAAAAC/8AAAAAAAM//YAAAAACv1f9AAAAAf+IH/iAAAF/0AAn9EAA/9gAADPsAHvgAAAAd+ABf4QAAAAj8AJ/A",
"AAAE/yAA35AAAu9QAAL/UADfkAAABv8gr9AAAAAK/Y/yAAAAAA3/9gAAAAAAP/oAAAAAAAC/MAAAAAAAC/MAAAAAAAC/MAAAAAAAC/MAAAAAAAC/MAAAAB////////4B////////4AAAAAAAX/kAAAAAAI/3AAAA",
"AACv9AAAAAABz+IAAAAAA+/BAAAAAAT/oAAAAAAH/3AAAAAACf9QAAAAAAz+MAAAAAAB////////4B////////4AD/8Q//EP4AD+AA/gAP4AD+AA/gAP4AD+AA/gAP/xD/8QoAAAAADpAAAAAL9wAAAAHfQAAAAC",
"7yAAAABP0QAAAAb8AAAAAJ+QAAAAC/cAAAAB30AAAAAu8gAAAAT0AAAAAGQf/wH/8AD/AA/wAP8AD/AA/wAP8AD/AA/wAP8B//Af/wAP////////AP////////BPoB/QDfEAAAAAAAAAAAAAAAAAAAAAAAAAAAAA",
"AAAAAAAAAAAf/////5Af//////UAAAAABvgAAAAABvkf//////kf//////kf4AAABvkP4AAABvkN//////kD3/////kP4AAAAAAP4AAAAAAP4AAAAAAP4AAAAAAP/////5AP//////YP8AAABvkP4AAABfkP4AAA",
"BfkP4AAABfkP4AAABfkP8AAABvkP//////YP/////5AD3/////gA7/////+AH+AAAAAAAf0AAAAAAB/QAAAAAAH9AAAAAAAf0AAAAAAB/gAAAAAADv/////4AD3/////gAAAAAAO8AAAAAAO8AAAAAAO8AAAAAAO",
"8An/////8G//////8J9gAAAO8J9QAAAO8J9QAAAO8J9QAAAO8J9QAAAO8J9gAAAO8G//////8An/////8APf///+gA7/////9R/gAAAH+B/QAAAG+B//////+B//////+B/QAAAAAB/gAAAAAA7/////+APf////",
"+APP//MN///zD+AAAA/gAAAP///zD///8w/gAAAP4AAAD+AAAA/gAAAP4AAAD+AAAA/gAAAP4AAABe////5gH//////yT7AAAAr1T7AAAAn1T7AAAAn1T7AAAAn1T7AAAAn1T7AAAAr1H//////1Be/////1AAAA",
"AAn1AAAAAAr1AG/////yAG////5gD+AAAAAAD+AAAAAAD+AAAAAAD+AAAAAAD/////+QD//////2D/AAAAb5D+AAAAX5D+AAAAX5D+AAAAX5D+AAAAX5D+AAAAX5D+AAAAX5D+AAAAX5H+Af4AAAB2Af4B/gH+Af",
"4B/gH+Af4B/gH+Af4AAACPcAAAj3AAAAAAAABJQAAAj3AAAI9wAACPcAAAj3AAAI9wAACPcAAAj3AAAI9wAACPcAAAj3AAAI9wAACPZf///zX//+cA/gAAAAAA/gAAAAAA/gAAAAAA/gAAADQQ/gAACP4g/gAAf+",
"IA/gAG/zAA/gBP9AAA////YAAA////gAAA/gBP9wAA/gAE/2AA/gAAX/UA/gAABf8x/gAB/gAB/gAB/gAB/gAB/gAB/gAB/gAB/gAB/gAB/gAA/gAA3/8wPf8w/////////6AA//////////cA/wAAP9AABfoA/g",
"AAL8AABPoA/gAAL8AABPoA/gAAL8AABPoA/gAAL8AABPoA/gAAL8AABPoA/gAAL8AABPoA/gAAL8AABPoA//////kAD//////2AP8AAABvkA/gAAAF+QD+AAAAX5AP4AAABfkA/gAAAF+QD+AAAAX5AP4AAABfkA",
"/gAAAF+QA9////6ADv/////1H+AAAAf4H9AAAAb4H9AAAAb4H9AAAAb4H9AAAAb4H+AAAAf4Dv/////1A9////+AD/////+QD//////2D/AAAAb5D+AAAAX5D+AAAAX5D+AAAAX5D+AAAAX5D/AAAAb5D//////2",
"D/////+QD+AAAAAAD+AAAAAAD+AAAAAAD+AAAAAACv/////wf//////wr1AAAA/wr0AAAA/wr0AAAA/wr0AAAA/wr0AAAA/wr1AAAA/wf//////wCv/////wAAAAAA/wAAAAAA/wAAAAAA/wAAAAAA/wA9////EO",
"////8Q/gAAAAH+AAAAAf4AAAAB/gAAAAH+AAAAAf4AAAAB/gAAAAH+AAAAAE3////nAO//////Mv0AAACPcv0AAAAAAO/////oAE3/////QAAAAAB/cf0AAAB/cO//////QD3////oAP4AAAD+AAAA/gAAAP4AAA",
"D///8w////MP4AAAD+AAAA/gAAAP4AAAD+AAAA/gAAAN///zA9//8w/gAAAG+QD+AAAAb5AP4AAABvkA/gAAAG+QD+AAAAb5AP4AAABvkA/gAAAG+QD+AAAAb5AN//////YAPf////kAX9AAAAAK+Az3AAAAP+AD",
"/xAAAM9gAJ+QAAb9AAAf8wAO8wAAB/sAj6AAAADfUv8gAAAAT9r4AAAAAAv/4AAAAAAC/1AAAC/gAAC/4AAAn3DPUAAv/3AAD/EF/AAJ/v4ABvoADvMB/z72AN9AAI+Qj8B/4D/QAAL/HvUA72n3AAAL/f0ACP3/",
"EAAAT/9gAB//sAAAAN/gAACf9AAAAAf4AAAB/gAADfgAAC72Au9gAd+AAD/0DPoAAAT/v7AAAABv/AAAAACP/hAAAAb+n8AAAE/zC/sAAv9QAN+QHvgAAC72T7AAAAn2T7AAAAn2T7AAAAn2T7AAAAn2T7AAAAn2",
"T7AAAAn2T7AAAAn2P7AAAAn2H//////2Be/////2AAAAAAn2AAAAAAn1AG/////yAG////5gD//////5AP//////kAAAAACv4wAAAAPfsQAAAAf/YAAAABv9IAAAAE75AAAAAI/lAAAAAA//////+QD//////5AB",
"v0Cf9AzyAM8gDPIH/RCfMAX/EAzyAM8gDPIAn/QBv0AP4A/gD+AP4A/gD+AP4A/gD+AP4A/gD+AP4A/gD+AP4A/gH8IB/8AA/wAP8AD/AAv6AB7QDfcA/wAP8AD/Af/AH8IAf+kwIQJ9+gAAAAAAAAAAAAAAAAAA",
"AAAD+wAAAAAAf3AAAAAAC/MAAAAAAAAAAAAAAAAAAAAAAAAAAAAAH/////+QAf//////UAAAAAAG+AAAAAAAb5Af//////kB//////+QH+AAAAb5AP4AAABvkA3/////+QA9/////5AAAA/wAAAAAD+wAAAAAH9w",
"AAAAAAAAAAAAAAAAAAAAAAAAAAAD3////oAO//////Uf4AAAB/gf0AAABvgf//////gf//////gf0AAAAAAf4AAAAAAO//////gD3/////gI9gzyD+AAAAAAAAAf4B/gH+Af4B/gH+Af4B/gH+Af4AAACPcAAAAA",
"DPMAAAAAD/AAAAAAAAAAAAAAAAAAAAAAAAAAAAPf///+gA7/////9R/gAAAH+B/QAAAG+B/QAAAG+B/QAAAG+B/QAAAG+B/gAAAH+A7/////9QPf////gAAAB/cAAAAAAL8wAAAAAA/wAAAAAAAAAAAAAAAAAAAA",
"AAAAAAAAAA/gAAAG+QD+AAAAb5AP4AAABvkA/gAAAG+QD+AAAAb5AP4AAABvkA/gAAAG+QD+AAAAb5AN//////YAPf////kAAAAAP7AAAAAAAAf3AAAAAAAAvzAAAAAAAAAAAAAAAAAAAAAAAAAs//////wgC///",
"/////AD/AAAAAA/wD/AAAAAA/wD/AAAAAA/wD/AAAAAA/wD////////wD////////wD/AAAAAA/wD/AAAAAA/wD/AAAAAA/wD/AAAAAA/wD/AAAAAA/wAAAA3xAAAAAAAf0AAAAAAAX5AAAAAAAAAAAAAAAAAAAA",
"AAAP///////gD///////4A/wAAAAAAAP8AAAAAAAD/AAAAAAAA/wAAAAAAAP//////AAD//////wAA/wAAAAAAAP8AAAAAAAD/AAAAAAAA///////+AP///////gDPMP4D+wAAAAAA/wD/AP8A/wD/AP8A/wD/AP",
"8A/wD/AP8A/wAAAAT6AAAAAAAAj2AAAAAAAAzyAAAAAAAAAAAAAAAAAAAAAAAAAs//////wgDf//////+wD/AAAAAB/gD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA",
"/wD/AAAAAA/gDf//////+wAs//////wgAAAAT6AAAAAAAAj2AAAAAAAAzyAAAAAAAAAAAAAAAAAAAAAAAAD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA/wD+AAAAAA",
"/wD+AAAAAA/wD+AAAAAA/wD/AAAAAA/gDf//////+wAs//////wgAAv9cgIAAAAQKO9wAAAAAAAAAAAAAAAAAAAAAAAAAAAA//////kAD//////2AP8AAABvkA/gAAAF+QD+AAAAX5AP4AAABfkA/gAAAF+QD+AA",
"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",
NULL };
static const char *const hr_sky_b64[] = {
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQgWBQgXBQgXBQgXBQgXBQkXBQkXBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkXBQkXBQgXBQgXBQgXBQgXBQgXBQgWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQgWBQgXBQgXBQgXBQgXBQkXBQkYBQkYBQoYBQoYBQoZBQoZBQoZBQsZBQsZBQsZBQsZBQsZBQsZBQoZBQoZBQoZBQoYBQoYBQkYBQkYBQkYBQkXBQgXBQgXBQgXBQgXBQgWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcWBQcWBQgWBQgXBQgXBQgXBQkXBQkYBQkYBQoYBQoZBQsZBQsZBQsaBQwaBQwaBQwaBQ0bBQ0bBQ0bBQ0bBQ0bBQ0bBQwaBQwaBQwaBQwaBQsZBQsZBQoZBQoYBQoYBQkYBQkYBQkXBQgXBQgXBQgXBQgXBQgW",
"BQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcWBQcW",
"BQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcX",
"BQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcX",
"BQgXBQgYBQgYBQgYBQkYBQkZBQoZBQoaBQsaBQsaBQwbBQwbBQ0cBQ4cBQ4dBQ4dBQ8eBg8eBg8eBg8eBg8eBg8eBg8eBQ8eBQ4dBQ4dBQ4dBQ0cBQ0cBQwbBQwbBQsaBQsaBQoaBQoZBQkZBQkZBQkYBQgYBQgY",
"BQgYBQgYBQgXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcX",
"BQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcX",
"BQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQgY",
"BQgYBQgYBQkZBQkZBQoZBQoaBQsaBQsbBQwcBQ0cBg4dBg8eBg8eBhAfBhAfBhEfBhIgBhIgBhIgBhIgBhIgBhIgBhIgBhIgBhEgBhEfBhAfBhAeBg8eBQ4dBQ4dBQ0cBQwbBQwbBQsaBQsaBQoaBQoZBQkZBQkZ",
"BQkYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgXBQgXBQgXBQgXBQgXBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgXBQgXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcX",
"BQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcX",
"BQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcXBQcYBQcYBQgYBQgY",
"BQgZBQkZBQkZBQoaBQsbBgsbBgwcBg0dBg4eBg8eBhAfBhEgBhIhBhMhBhQiBhQjBhUjBhUjBhYkBhYkBhYkBhYkBhUjBhUjBhUjBhQiBhMiBhMhBhIgBhEgBhAfBhAeBQ8eBQ4dBQ0cBQ0cBQwbBQsaBQsaBQoa",
"BQoZBQkZBQkZBQkZBQkYBQkYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQkYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgXBQcXBQcXBQcXBQcX",
"BQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgY",
"BQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgZBQgZBQgZBQkZBQkaBQka",
"BgobBgobBgscBgwdBg0dBg4eBg8fBhAgBhEhBhIiBhQjBhUkBhYlBxcmBxgmBxknBxonBxooBxsoBxsoBxsoBxsoBxooBxooBhonBhgmBhgmBhclBhYkBhUkBhQjBhMiBhIhBhEgBhAfBQ8fBQ8eBQ4dBQ0dBQwc",
"BQwcBQsbBQsbBQsbBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQsbBQsbBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQoaBQkaBQkZBQkZBQkZBQkZBQkZBQkZBQgZBQgY",
"BQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgY",
"BQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgZBQgZBQgZBQgZBgkaBgkaBgkaBgobBgob",
"BgscBgwdBgweBg4fBw8gBxAhBxEiBxMjBxUkBxYlBxcmBxknBxopBxwpBx0rBx4rBx8sBx8sByAtByAtByAtByAtByAsBx8sBx8rBx4rBx0qBxwpBhsoBhknBhgmBhclBhYkBhUjBhQiBhMhBhIgBhEfBRAfBQ8e",
"BQ8dBQ4dBQ0cBQ0cBQ0cBQwbBQwbBQwbBQwbBQwbBQwbBQwbBQwbBQwbBQwbBQwbBQwcBQ0cBQ0cBQ0cBQ0cBQ0cBQ0cBQ0cBQ0cBQ0cBQwcBQwbBQwbBQwbBQsbBQsbBQsaBQsaBQoaBQoaBQoZBQoZBQkZBQkZ",
"BQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgY",
"BQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgYBQgZBQgZBQgZBggZBggaBgkaBgkaBgkbBgkbBgocBgocBwsd",
"BwweBw0fBw4gBxAhBxEiBxIkCBQlCBYmCBcoCBkpCBsrCB0sCB4tCCAuCCEvCCMwCCQwCCUxCCUxCCYyCCYyCCYxCCUxCCUwByQwByMvByIuByEtByAsBx4rBx0qBxwoBhonBhkmBhclBhYkBhUjBhQiBhMhBhIg",
"BhEgBhAfBRAfBQ8eBQ8eBQ8dBQ4dBQ4dBQ4dBQ4dBQ4dBQ4dBQ4dBQ4dBQ4dBQ4dBQ8dBQ8eBQ8eBQ8eBQ8eBQ8eBQ8eBQ8eBQ8eBQ8eBQ8eBQ4dBQ4dBQ4dBQ0cBQ0cBQ0cBQwbBQwbBQsbBQsaBQsaBQoaBQoa",
"BQkaBQkaBQkaBQkaBQkZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZ",
"BQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgaBQgaBQgaBggaBggbBggbBgkbBgkcBgkcBwkdBwodBwoeBwsfBwsgCAwh",
"CA0iCA8jCBAkCBElCBMnCRUoCRcqCRkrCRstCR0uCR8wCSExCSMzCSU0CSc1CSg2CSk3CSo3CSs4CSs4CCs4CCs4CCs3CCs3CCo2CCk1CCg0CCYzByUyByMwByIvByAuBx8sBx0rBxwqBhooBhknBhcmBhYlBhUk",
"BhQjBhQjBhMiBhIhBhEhBhEhBhEgBhEgBhAgBhAgBhAgBhAgBhAgBhEgBhEgBhEhBhEhBhEhBhEhBhIhBhIhBhIhBhIhBhIhBhIhBhEhBhEhBhEhBhEgBhAgBRAgBQ8fBQ8fBQ4eBQ4eBQ0dBQ0dBQwcBQwcBQsc",
"BQoaBQoaBQkaBQkaBQkaBQkaBQkaBQkZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZ",
"BQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgZBQgaBQgaBQgaBggaBggbBggbBggbBgkcBgkcBwkcBwkdBwoeBwofCAofCAsgCAwhCAwiCQ4j",
"CQ8lCRAmCRInChQpChYrChgsChouChwwCx8yCyEzCyM1CyY3Cyg4Cio6Ciw7Ci48Ci88CjA9CjE9CTI+CTI9CTI9CTE9CTE8CTA7CS86CC45CCw4CCs3CCk1CCg0CCYyByQxByIvByEuBx8sBx0rBxwqBhspBhkn",
"BhgnBhcmBhYlBhUlBhUkBhQjBhQjBhQjBhQjBhQjBhQjBhQjBhQjBhQjBhQjBhQjBhUkBhUkBhUkBhUkBhUkBhUkBhUkBhUkBhUkBhUkBhUkBhQjBhQjBhMiBhMiBhIhBhEhBhEgBRAgBQ8fBQ8fBQ4eBQ4eBQ0d",
"BgsbBgsbBgobBgobBgobBgoaBgkaBgkaBgkaBgkaBgkZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggZBggaBggaBggaBggaBggaBggaBggaBggaBggaBgga",
"BggaBggaBggaBggaBggaBggaBggaBggaBggaBggaBggaBggZBggZBggZBggZBggZBggaBggaBggaBggaBggaBggaBggaBwgbBwgbBwgbBwkcBwkcBwkcCAkdCAkeCAoeCQofCQogCQshCgsiCgwjCg0kCw4lCw8n",
"DBEoDBIqDBQsDBYtDRgvDRsxDR0zDSA1DSI3DSU5DSg7DSo8DS0+DS8/DTFADDNCDDVCDDZDDDdDDDhEDDhDCzhDCzhDCjdCCjZBCjVACjQ/CjM9CTE8CS86CS05CSs3CSo2CSg0CCYyCCQxCCIvCCEuCB8tCB4s",
"CB0qBxspBxsoBxkoBxknBxgnBxgmBxcmBxcmBxcmBxcmBxcmBxcmBxgmBxgmBxgnBxgnBxknBxknBxknBxkoBxkoBxkoBxkoBxknBxknBxgnBxgmBxcmBxcmBxYlBxUkBxQkBxQjBxMiBxIhBxEhBhEgBhAgBhAg",
"BgwdBgwdBgwdBgsdBgscBgscBgocBgocBgobBgkbBgkbBgkbBgkbBgkaBggaBggaBggaBggaBggaBggbBggbBggbBggbBggbBggbBggbBgkbBgkbBgkbBgkbBgkbBgkbBgkbBgkbBgkcBwkcBwgcBwgcBwgcBwgc",
"BwgcBwgcBwgcBwgcBwgcBwgcBwgbBwgbBwgbBwgbBwgbBwgbBggbBggbBggbBggbBwgbBwgbBwgbBwgcBwgcBwgcBwkcBwkdBwkdCAkdCAkeCAkfCQkfCQogCQohCgoiCgsjCwskCwwlDAwmDA4nDQ8pDRAqDREs",
"DhMuDhQvDhYxDxkzDxs1Dx43DyA6DyM8DyY+DylADyxBDy9DDzJFDzRGDjZIDjlJDjpKDjxKDT1KDT5LDT5KDT5KDD5KDD5JDD1IDDxHCzpFCzlECjdCCjZBCjQ/CjI9CTA8CS46CSw4CSo3CSg1CSY0CCUyCCMx",
"CCIwCCAvCB8uCB4tCB4sCB0rCBwrCBwrCBwrCBwqCBwrCBwrCBwrCBwrCB0rCB0rCB0sCB4sCB4tCB4tCB4tCB4tCB4tCB4tCB4tCB4sCB0sCB0rCBwrCBsqBxopBxooBxgoBxcnBxYmBxUlBxUlBxQkBxMjBxMj",
"Bg8fBg8fBg4fBg4eBg0eBg0dBgwdBgwdBgscBgscBgscBgobBgobBgobBgobBgobBgobBgobBgobBgobBgobBgobBgocBgocBgocBgocBgocBgocBgocBgocBwocBwocBwocBwodBwodBwodBwodBwodBwodBwod",
"BwodBwodBwodBwodBwodBwodBwodBwodBwocBwocBwocBwkcBwkcBwkcBwkcBwkcBwkcBwocBwodBwodBwodCAodCAoeCAoeCAofCQofCQsgCQshCgsiCgsjCwwkCwwlDA0mDQ0nDQ4pDg8qDhArDxEtDxIvEBQx",
"EBYzERc1ERo3ERw5Eh87EiI9EiVAEihCEitEEi5GEjFIETRKETdLETpNEDxOED9PEEFQD0JQD0NRDkVRDkVRDkVQDUVQDUVPDURODENMDEJLDEBKDD9ICz1HCztFCjlDCjdBCjU/CjM+CTE8CS86CS05CSs3CSo2",
"CSg0CSczCCYyCCUyCCQxCCMwCCIwCCIvCCIvCCIvCCIvCCIvCCIvCCIvCCMwCCMwCCMwCCQxCCQxCCQxCCUxCCUyCCUyCCUxCCQxCCQxCCMwCCMwCCIvCCEuCCAuCB8tCB4rCB0rBxwpBxooBxkoBxgnBxcmBxcm",
"BxIhBxEhBhEhBhAgBhAgBg8fBg4eBg0eBg0dBgwdBgwdBgscBgscBgscBgscBgocBgocBgocBgocBgocBgocBgscBgsdBgsdBgsdBgsdBgsdBwsdBwseBwseBwseBwseBwseBwseBwseCAseCAsfCAsfCAsfCAof",
"CAofCAofCAofCAofCAofCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAoeCAofCQofCQogCQshCQshCgsiCgsjCwwkCwwlDAwmDQ0nDQ0oDg4qDw8rDw8tEBAvEREwEhIyEhQ0ExY2",
"Exg4FBo7FBw9FB8/FCJBFSREFShGFStIFS5LFDJMFDVPFDhQEztSEz5TE0FVEkNWEkVWEUdXEUlXEEpXD0tXD0tWDktWDktVDkpTDUlSDUhRDUdQDEVODENMDEJKC0BJCz5HCztFCjlDCjdBCjVACjQ+CjI9CTA7",
"CS46CS04CSw3CSs3CSo2CSk1CSg1CSg0CSg0CSg0CSg0CSg0CSg0CSg0CSk1CSk1CSk1CSo2CSo2CSo2CSs3CSs3CSs3CSs3CSo2CSo2CSk1CSk1CSg0CSYzCCUyCCQxCCMwCCEvCCAuCB8tCB4sCB0rBxwqBxsp",
"BxUlBxQkBxQkBxMjBxIjBxEiBhAhBhAhBg8gBg4fBg0fBg0eBgweBgweBgweBgseBgseBgseBgseBgsfBgsfBgwfBgwfBgwgBwwgBwwgBwwgBwwgBwwhBwwhBwwhCAwhCAwhCAwiCAwiCAwiCAwiCQsiCQsiCQsi",
"CQsiCQsiCQsiCQsiCQsiCQsiCQsiCQshCQshCQshCQshCQohCQohCQohCQohCQohCQohCQshCQshCQsiCQsiCgsjCgsjCgskCwwlDAwmDAwnDQ0oDQ0pDg0rDw4sDw8uEA8vERAxEhEzExI1FBM3FBU5FRY7FRg9",
"FhpAFxxCFx9EGCFHGCRJGCdMGCtOGC5QGDFSGDVUFzhWFzxYFj9aFkJbFUVcFEddFEpeE0xeE05eEk9eEVBeEVBdEFBcD1BbD1BaDk9ZDk5YDU1WDUtUDUpTDEhRDEZPDERNDEJMC0BKCz5ICjxGCjpECjhDCjZC",
"CjVACjM/CjI+CTE9CTA8CS87CS87CS47CS46CS46CS46CS46CS47CS47CS87CS88CTA8CTA8CTA9CTE9CTE9CTE9CTE9CTE9CTE9CTA8CS88CS87CS46CSw5CSs4CSo3CSk2CSc0CCUzCCQyCCMxCCIwCCEvCCAu",
"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",
"CS06CSw5CSs4CSk3CSc2CCU1CCMzCCEyCB8xCB4wCBwvCBsuCBotCBgtCBgtCBctCBcuCBcuCBcvCBcwCBgxCRgxCRgyCRgzCRgzCRk0Chk0Chk1Cxk2DBk2DBk3DRg3DRg3Dhg4Dhg4Dxc5EBc5EBc5ERc5EhY6",
"EhY6EhU5ExU5ExQ5ExQ5ExQ4ExM4ExM4ExM3ExM3ExI2ExI2ExI2ExI2ExI2ExI2ExI2FBI3FBI3FBI4FRM5FRM6FhM8FxQ9GBQ/GRVBGhZCGxZFHBdHHRhJHhhMHxlOIRpRIhtTIxxWJB1YJh9bJyBdKCJgKCNi",
"KSVlKihnKippKixsKy9uKzJwKzVyKjh0Kjt1KT52KUJ3KEV5J0h5Jkt6JE56I1F6IlR6IFZ5H1l5Hlp4HFx3G152GV91GGB0F2ByFmFxFWFwFGFuE2FsEmBrEmBqEV9oEF5nD11lD1xkD1tiDlphDlhgDldeDlZd",
"DlVcDVRbDVNbDVJaDVFZDVFZDVBYDVBYDVBYDVBYDVBYDVBYDVBYDVBZDVFZDVFZDlFaDlJaDlJbDlJbDlNbDlNbDlNbDlNbDlJbDVJaDVFZDVBZDU9YDU5WDUxVDUtUDElSDEdRDEZPDERODENNC0FLC0BKCz9J",
"CjNBCjJACTA/CS89CS08CSs7CSg5CSY4CSQ2CCI1CCA0CB80CB4zCB0zCBwzCBs0CBs0CRs1CRs1CRs2CRs3CRw4CRw5Chw6Ch06Ch07Cx08DB08DB09DR0+DR0+Dhw+Dxw/Dxw/EBtAERtAEhtBExpBExpBFBlB",
"FBlBFRhBFRhBFRdBFhdBFhdAFhZAFhY/FhU/FhU+FhU+FhQ+FhQ9FhQ9FhQ9FhQ9FhQ+FxQ+FxQ/GBU/GBVBGRVCGRZDGhZFGxdHHBdJHRhLHhhNHxlPIRpSIhtUIxxXJB1ZJh5cJx9eKCBhKSFjKiJmKyRoLCVq",
"LSdtLilvLixxLi5zLjB1LjN3LjV5Ljh6Ljt8LT59LEJ+K0R/Kkh/KUp/KE5/JlB/JVN/JFV+Ilh+IFp9H1x8HV17HF95GmB4GWF3GGJ1FmJ0FWJyFGJxE2JvE2JuEmJtEWFrEWBqEF9pEF9nD15mD11lD1xkD1tj",
"DlpiDllhDlhhDlhgDldfDlZfDlZfDlZfDlVfDlVfDlVfDlZfDlZfDlZfDlZgDldgDldhDldhDlhhD1hhD1hiD1hiDlhiDlhhDlhhDldhDldgDlZfDlVeDlRdDlJcDVFaDU9ZDU5XDUxWDUpVDElTDEhSDEZRDEZQ",
"CzpGCzhFCzZECzVDCjJBCjBACi4+Cis9Cik8Cic7CiU6CiM5CiI5CiE4CiA5Ch85Ch86Ch86Ch87Ch88Ch89CyA+CyA/CyBADCFBDCFCDSFDDSFDDiFEDiFEDyFFECBGESBGEiBHEh9HEx9IFB5IFR5IFh1IFx1J",
"FxxJGBxJGBtIGRpIGRpIGRlHGRlHGRhGGRhGGRhFGRdFGRdEGRdEGhdEGhZEGhZEGhZEGhdFGxdGGxdHHBdIHRhJHRhKHhlMHxlOIBpQIRtSIhtUJBxXJR1ZJh1cJx5eKR9hKiBjKyFmLCJoLSNqLyRtLyZvMChx",
"MSl0Mit1Mi14Mi95MjF7MjN9MjZ+MjiAMTuBMT6CMEGCL0ODLkaDLUmDK0yDKk+DKVGCJ1SCJVaBJFiAIlp/IFx+H158HV97HGB5GmF4GWJ3GGN1F2N0FWNyFWNxFGNwE2NuEmJtEmJsEmFrEWFqEWBpEF9oEF9n",
"EF5nEF1mEF1lD1xlD1xkD1tkD1tkD1tkD1tkD1tkD1tkEFtkEFtkEFtlEFtlEFxmEFxmEFxmEF1mEF1nEF1nEF1nEF1nEF1nEF1mEFxmEFxlD1tlD1pkD1liD1hhD1dgD1VfDlRdDlJcDlFaDk9ZDk5YDU1XDUxW",
"DEBMDD5LDDxKDDtJCzhHCzZGCzNECzFDCy5CCyxACypACyg/Cyc/CyU/CyU/CyQ/CyRACyNBCyNCCyRDDCREDCRFDSVGDSVHDSVIDiZJDiZKDyZKDyZLECVMESVNEiVNEyVOFCROFCRPFSNPFiNPFyJQGSFQGSFQ",
"GiBQGx9QGx9QHB5QHB1PHR1PHRxOHRxOHRtNHRpNHRpMHRpMHRlMHhlLHhlLHhlMHhlMHhlNHxlNHxpOIBpPIBpRIRtSIhxUIxxWJB1YJR1aJh5cKB9eKR9hKiBjKyFmLCJoLiNqLyRtMCVvMSZxMid0Myh2NCl4",
"NSt6NSx8NS59Ni9/NjKANjOCNjaDNjiENTqFNT2GND+GM0KHMkSHMUeHL0qHLkyGLE+GK1GFKVSEJ1aDJViCJFqBIlx/IF19H198HWB7G2F5GmJ4GWJ2GGN1F2NzFmNyFWNxFGNwFGNvE2NuE2NtEmJsEmJsEmJr",
"EmFqEmFqEWBpEWBpEWBpEV9pEV9pEV9pEV9pEV9pEV9pEV9pEl9pEl9qEmBqEmBqEmBrEmFrEmFsEmFsEmFsEmFsEmFsEmFsEmFrEmFrEWBqEWBpEV9pEF5oEF1mEFtlEFpkD1liD1hhD1ZgD1VfD1ReDlNcDlJc",
"DUZTDURSDUNRDUFQDT5ODDxNDDlLDDZKDDRJCzJICy9HCy5GCyxGCytGDCpHDClHDChIDChJDShKDSlLDSlMDSlODipPDipQDipRDypSDytTECtTECtUESpVEipVEypWFClWFSlXFihXFyhYGCdYGSZZGiVZGyVZ",
"HCRZHSNZHiJZHiJYHyFYHyBYICBXIB9XIB5WIB5WIB1VIB1VIB1VIRxUIRxUIRxUIRxVIhxVIhxWIx1XIx1YJB1ZJR5bJR5dJh9fKCBgKSBiKiFlKyJnLCJpLSNrLyRuMCVwMSVyMiZ1Myd3NCh5NSl7Nip9Nit+",
"NyyAOC2COC+DODCEOTKGOTOHODWIODeJODmJNzyKNj6KNUCLNUOLNEWLMkeKMUqKL0yJLU+ILFGIKlOGKFWFJleEJVmDI1uBIVx/H15+Hl98HGB7G2F5GmJ4GWJ3GGN1F2N0FmNzFWNyFGRyFGRxFGRwE2RvE2Rv",
"E2NvE2NuE2NuEmNuEmNuEmNuEmNuEmNuEmNuEmNuEmNuEmNvE2NvE2NvE2NwE2RwE2RwE2RxE2RxE2RxE2VxE2VxE2VxE2VxE2RxEmRwEmRwEmNvEmNuEmJtEWFsEWBrEF9qEF1pEFxnEFtmD1plD1lkD1hjD1di",
"DkxZDktYDklXDUdWDURVDUJTDT9SDTxQDTpPDTdODTVODTNNDTFNDTBNDS9ODS5ODS5PDS1QDS5RDi5TDi5UDi5VDi9WDy9XDzBYEDBZEDBaETBbEjBcEzBdEy9dFC9eFS5eFi5fGC1fGS1gGixgGythHCphHSlh",
"HihhHyhhICdhISZgISVgIiRgIiNfIyNfIyJeIyJeIyFdJCFdJCBcJCBcJCBcJCBcJSBdJSBdJSBeJiBfJiBgJyFhKCFjKSJkKiJmKyNoLCNqLSRsLiVuLyZwMCZzMSd1Mih3NCh5NSl7Nip9Nit/NyyBOCyCOS2E",
"OS6FOi+GOjCHOzGIOzKJOzOKOzWLOjeLOjmMOjqNOTyNOD6NN0CNNkONNUWNM0eMMkmLMEyKL06KLVCJK1KHKVSGJ1aEJliDJFqBIluAIFx+H159HV97HGB6G2B4GmF3GWJ2GGN1F2N0FmN0FWRzFWRzFWRyFGRy",
"FGVyFGVyFGVyFGVxE2VxE2VyE2VyE2VyE2VyE2VyFGZzFGZzFGZzFGZzFGZ0FGZ0FGZ0FGd1FGd1FGd1FGd1FGd1FGd1FGd1E2d1E2d0E2d0E2ZzE2ZzEmVyEmRxEmRwEmNvEWJtEWFsEGBrEF9qEF5pEF1oEF1o",
"DlNfDlFeDk9dDk1cDkpbDkhaDkVYDkNXDkBWDj1VDjtVDjlUDjdUDjZVDjVVDjRWDjRXDjNYDjNZDzRaDzRcDzRdDzVeEDVfEDVgETZhEjZiEjZjEzZkFDZkFDVlFTVmFjRmGDRnGTNnGjJoGzFoHTBoHjBpHy9p",
"IC5pIS1pIixoIytoJCpoJClnJShnJSdmJSdmJiZlJiVlJiVkJiRkJyRkJyRkJyRkJyRkKCRlKCRmKSRmKSRoKiVpKyVqKyZsLCZtLSdvLihxLyhzMCl1MSl3Mip5NCt7NSt9Nix/Ni2BNy2COC6EOS6FOi+HOi+I",
"OzCJOzCKOzKKPDKLPDOMPDSNPDWNPDeNOziOOzmOOjuOOj2OOT+OOEGON0OONkWNNEeNM0mMMUuLME6KLk+JLFGIKlOGKVWFJ1eDJVmCI1qAIVt+IF19Hl57HV96G2B5GmF4GmJ3GWJ2GGN2F2R1FmR1FmV0FmV0",
"FWZ0FWZ0FWZ0FWd0FWd0FWd1FWd1FWd1FWh2FWh2FWh2FWh3FWh3FWh3FWl4FWl4FWl4FWl4FWl5FWl5FWp5FWp5FWp5FGp5FGp4FGp4FGl4FGl3E2l3E2h2E2h1E2d0EmZzEmZyEmVxEmRwEWRvEWNuEGJtEGJt",
"D1hmD1ZlD1RkD1JjD1BiD01hD0tgDkhfDkVeDkNdDkBdDj9cDj1dDztdDzpeDzlfDzlgDzlhDzliEDljEDlkEDlmEDpnETpoEjppEjtqEjtrEztsFDtsFDptFTptFjpuGDlvGTlvGjhwGzdwHTZwHjVxHzRxIDNx",
"ITJxIzFxJDBxJC9xJS5wJi5wJixvJytvKCtuKCpuKCltKSltKShtKShtKShtKidtKidtKidtKyduKyhvLChwLChxLSlyLil0Lyp2MCp3MCt5MSx7Mix9NC1/NC2ANS6CNi6ENy+FOC+HOS+IOjCKOjCKOzGLOzGM",
"OzGNPDKOPDKOPDOPPDOPPDSPPDWPPDWPPDeQPDiQOzmQOzuQOjyQOj6QOUCPN0KPNkSPNUaONEiNMkqNMEyLL06KLU+JK1GHKlOFKFWEJlaDJFiBIll/IVp+H1x9Hl17HV56HF95G2B5GmF4GWJ4GWN4GGR4F2V4",
"F2V4F2Z4FmZ4Fmd4Fmd4Fmd5Fmh5Fmh5Fml6Fml6Fml6Fml7Fml7Fml8Fml8Fmp8Fmp9Fmp9Fmp9Fmp9Fmp9Fmp9FWp9FWp9FWp9FWp9FWp8FWp8FGp7FGp6FGp5E2l5E2l4E2h3Emd2Emd1EmZ0EmZ0EmVzEWVy",
"EFxsEFtrEFlqEFdpD1RoD1JnD09mD01mD0plD0hkD0VkD0NkD0JkD0BkED9lED5mED5nED5oED1pET5rET5sEj5tEj9uEj9vEz9wEz9xE0ByFEBzFT90FT90Fj91GD91GT52Gj12Gzx3HDx3HTt3Hzp4IDl4ITh4",
"Izd4JDZ4JTV4JjR4JjJ3JzF3KDF3KTB2KS92Ki51Ki11Ki11Kyx0Kyx0Kyt0LCt0LCt1LSt1LSt1Lit2Lix3Lyx4Lyx5MC17MS18MS5+Mi5/My+BNC+DNTCENTCGNjGHNzGJODKKOTKLOTKMOjKNOjOOOzOPOzOP",
"PDOPPDOPPDOQPDOQPDOQPTSQPTSQPDWQPDWQPDeQPDiQPDmQOzqQOzuQOj2QOT+POECPN0KPNkSONUaNM0iMMUqLMEyKLk2ILE+HKlGFKVKEJ1SDJVWBJFd/Ilh+IFp9H1t8Hlx7HV16HF96G2B5GmB5GmJ5GWN5",
"GWR5GWV6GGV6GGZ6GGd7GGd7GGd8F2h8F2l9F2l9F2l+F2l+F2l/F2l/F2p/F2qAF2qAF2qAF2qAF2qAF2qAF2qAFmqAFmqAFmuAFmuAFmt/FWt/FWt+FWt+FGp9FGp8FGp7E2p7E2l6E2l5E2l5Emh4Emh3Emh3",
"EGBxEF5wEF1vEFtvEFluEFZtEFRtEFFsEE9rEExrEEprEEhrEEZrEEVsEURsEUNtEUJuEkJvEkJxEkJyEkJzE0N0E0N1E0R2FER3FER4FER5FUR6FUR6FkR7F0N7GEN8GUJ8GkJ9G0F9HUB+Hj9+Hz9+ID1/Ijx/",
"Izt/JDp/JTl/Jjh+KDd+KDZ+KTV9KjR9KjN9KzJ8KzF8LDF7LDB7LTB7LS97Li97Li97Li98Ly98Ly99MC9+MDB/MTCAMTCBMjGCMzGEMzKFNDKHNTOINTOJNjSLNjSMNzSNODWOOTWPOTWQOjWQOjWQOzWROzSR",
"OzSROzSRPDSQPDSQPDSQPDSQPDSQPDSPPDWPPDWPPDaPPDePOziPOzmPOzqPOjuPOT2POT+PN0GONkKONUSNNEaMMkiLMEmJL0uILU2GK06FKlCEKFGCJlOBJVSAI1Z+Ild+IVl9H1p8Hlt7Hl17HV57HF97G2B7",
"G2F7GmN8GmR8GmV9GmV9GWZ+GWd+GWd/GWd/GWiAGWiBGWmBGWmBGWmCGGmDGGmDGGmDGGmDGGmDGGqEGGqEGGqEGGqEGGqDF2qDF2qDFmuDFmuCFmuCFWuBFWuAFWuAFGt/FGt+FGp+E2p9E2p8E2p8E2p7E2p7",
"EWN3EWF2EWB2EV51EVx1EVp0EVh0EVVzEVNzEVBzEk9zEk1zEktzEkp0Ekh0Ekd1E0d2E0d3E0Z5E0Z6E0d7FEd8FEd9FEd+FUh/FUiAFUiAFkiBFkiCF0iCGEeDGUeDGkaDG0aEHEWEHUSEHkSFH0OFIUKFIkGG",
"I0CGJD+GJj2GJzyFKDuFKTqFKjmFKjiEKzeELDaELDaDLTWDLTSDLjSCLjSCLzOCLzODLzODMDOEMDOEMDOFMTSGMTSHMjSIMzWJMzWKNDWLNDaNNTaONTePNjeQNjeRNziSNziSODiTOTiTOTeUOTeUOjeUOjaT",
"OjaTOjWSOzWSOzWROzSROzSQOzSQOzSQOzSPOzSPOzSPOzWPOzaPOzePOziPOjmPOjqPOTyPOT2PNz+PN0CONkKNNESMM0WLMUeKMEiJLkqHLEyGK02FKU+EKFCCJlKBJVOAJFV/IlZ/IVh+IFl+H1t+Hlx+Hl5+",
"HV9/HWB/HGF/HGOAG2SAG2SBG2WCGmaDGmaDGmeEGmeEGmeFGmeFGmiGGWiGGWiGGWiHGWiHGWmHGWmHGWmHGWmHGWmHGGmHGGqHGGqGGGqGF2qGFmqFFmqFFmuEFWuEFWuDFWuDFGuCFGuBFGuBFGuAE2uAE2t/",
"EmV7EmR7EmJ7EmF6El96El16Elt5Elh5ElZ5ElR5ElJ5E1B5E096E056E0x7E0t8FEt9FEp+FEp/FEqAFUqBFUqCFUqDFUuEFUuEFkuFFkuFFkuGF0uHGEuHGUuHGUqIGkqIG0mIHEmJHUiJHkeJH0aKIEWKIkSL",
"I0SLJEOLJUGLJkCLKD+KKT6KKj2KKjyKKzuJLDqJLDqJLTmJLjmILjiILzeILzeILzeJMDeJMDeJMDeKMTeKMTeLMTiMMjiNMjiOMzmPMzmQNDmRNDqRNTqSNTqTNTqUNjqVNjqVNzqVNzqVNzqVODmVODmVODmU",
"ODiUOTeSOTeSOTaROTWQOTSPOjSPOjSOOjOOOjONOjONOjSNOjSNOzWOOjaOOjeOOjiOOjmOOTqOOTuOOD2ONz6NNkCMNUKMNEOLMkWKMUaJL0iHLUmGLEuFK0yEKU6DKE+CJlGBJVOAJFSAI1aAIleAIVmAIFqA",
"H1yAH12BHl+BHmCCHWGDHWKEHGOEHGSFHGWFG2WGG2aHG2aHG2aIGmaIGmeJGmeJGmeJGmeKGmeKGmeKGmeKGWeKGWiKGWiKGWiJGGmJGGmJGGmIGGqIF2qIFmqHFmqGFmqGFWuGFWuFFWuFFGuEFGuEFGuDFGuD",
"E2eAE2aAE2V/E2R/E2J/E2B/E15/E1x/E1p/E1h/E1Z/FFR/FFOAFFGAFFCBFFCCFU+DFU+EFU6FFU6FFk6GFk6HFk6IFk6IFk+JF0+JF0+KGE+KGE+KGE6LGU6LGU6LGk2MG02MHEyMHUyNHkuNH0qOIEqOIUmO",
"I0iPJEePJUaPJkWPJ0SPKEOPKUKOKkGOK0COKz+OLD+OLT6NLj2NLj2NLjyNLzyNLzyNLzyOMDyOMDyOMDyPMTyQMTyQMT2RMT2RMj2SMj6TMz6UMz6VMz6VND+WND+WND+XNT6XNT6XNT6XNT6WNj2WNjyVNjuV",
"NjuUNjqSNjmRNjiQNzePNzaONzWNNzWMODSMODSLODSLOTSLOTSLOjSLOjWMOjWMOjaMOjeNOjmNOTqNOTuNODyNNz2MNj+MNUCLNEKLM0OKMUWJMEaHL0eGLUmFLEuFKkyEKU6DKFCCJlGCJVOCJFWCI1aCIliC",
"IVqDIVuDIF2EH16EH2CFHmGGHmKGHmOHHWSIHWSJHWWJHGWKHGWKG2aLG2aLG2aLG2aMG2aMGmaMGmeMGmeMGmeMGmeMGmeMGWiMGWiMGWiLGGmLGGmLGGqKF2qKFmqJFmuJFmuIFWuIFWuHFWyHFWyHFGyGFGyG",
"E2iFE2eEE2aEE2WEE2SEFGKEFGCEFF6FFFyFFFuFFFmFFVeGFVaGFVSHFlOIFlKIFlKJFlGKF1GKF1GLF1CMF1CMGFCNGFCNGFCNGFCOGFCOGFCOGFCOGVCPGVCPGVCPGlCPG0+QG0+QHU6QHk6RH02RIEySIUyS",
"IkuSI0qSJEqTJUiTJkeTKEeTKUaTKUWTKkSTK0OTK0OSLEKSLUGSLUGSLkCSLkCSL0CSL0CTL0CTL0CTMECUMECUMECVMECVMUGWMUGXMUGXMUGYMUKYMkKZMkKZMkKaM0KaM0KaM0GaM0GZNECYNECYND+XND6W",
"ND2VNDyTNDuSNDqRNDmPNTiONTaNNTWMNTWLNjSKNjSKNzOKNzOKODOKODSLOTSLOTWMOjWMOjaNOTeNOTmNOTqNOTuNODyNNz2NNj+MNUCMNEGLM0OKMUSJMEaIL0eHLUmGLEqGKkyFKU6FKFCFJ1GFJlOFJVWF",
"JFeGI1mGIlqHIVyHIV2IIF6JH2CKH2GLHmGLHmKMHmOMHWONHWSNHWSOHGWOHGWPG2WPG2WPG2WQG2WQG2WQGmaQGmaQGmaQGmaPGWePGWePGWeOGWiOGGiOGGmNF2mNF2qMFmqMFmqMFmuLFWuLFWuLFWuKFWuK",
"FWiIFWiIFWeIFWaIFWSIFWOJFWGJFWCJFl6JFlyKFluKF1mKF1eLF1aMF1WMGFSNGFSNGVOOGVKOGVKPGVKPGVKPGVGQGlGQGlGQGlGQGlGQGlGQGlGQGlGQGlGQGlGQG1GRG1CRHFCRHVCSHlCSH0+TIE+TIE6T",
"IU2UIk2VJEyVJUuVJkuWJ0qWKEmWKUiWKkeWKkeWK0aWLEWWLEWWLUSWLUSWLUSWLkSWLkOWL0OWL0OXL0SXL0SXL0SXMESYMESYMESZMEWaMEWaMEWbMEWbMUWbMUWbMUWbMUWbMUWbMUSaMUOZMkKYMkGXMkCW",
"Mj+UMj6TMj2RMjuQMjqOMjmMMziLMzaKNDWJNDSINTSINTOHNjOINzOINzOIODOJOTOKOTSLOjWLOjWMOjaMOjeNOjmNOjqNOTuNODyNNz2MNz+MNkCLNEGLM0KKMkSJMEaIL0eILUmHLEuHK0yHKk6HKVCHJ1KH",
"JlSIJlaIJViJJFmKI1uLIlyLIV2MIV6NIGCNIGCOH2GPH2KPHmKQHmKQHmORHWORHWORHGORHGSRHGSSHGSSHGSSG2SSG2WRG2WRG2WRGmaRGmaRGmaQGWeQGWeQGWiPGGiPGGmOF2mOF2qOF2qNFmqNFmqNFmuN",
"FWiLFWiMFWeMFWaMFmWMFmOMFmKMFmCNF1+NF12OF1uOGFqPGFmPGVeQGVaQGVWQGlWRGlSRGlSRGlORGlKRGlKRGlKRGlKRGlGRGlGRGlGRGlGQGlGQGlGQGlGQGlGQG1GRG1GRG1GRHFGSHVCSHlCTH1CTH1CU",
"IE+VIU+WIk6WI06WJE2XJUyXJkyXJ0uYKEuYKUqYKkqYKkmYK0iYK0iYLEeYLEeYLEeYLEeYLUeZLUeZLUeZLUeaLUeaLUeaLUebLkibLkibLkicLkicLkicLkicLkicLkicLkecL0ebL0abL0aaL0WYL0SXL0OW",
"L0KUL0CSLz+RLz2PLzyNMDqLMDmKMDiIMTaHMTWGMjSGMzSGNDOFNDOGNTKGNjKHNzOIODOIODOKOTSLOjWLOjWMOjaMOjiNOjmNOTqNODuNODyNNz2MNj+MNUCMNEGLMkOLMUWKMEaKLkiJLUqJLEyJK06JKVCK",
"KFGKJ1OLJlWLJVeMJFiMI1qNIluOIVyPIV2QIF6QIF+RH2CRH2CSHmGSHmGSHmGTHWGTHWKTHGKTHGKTHGKTHGKTHGOTG2OTG2OTG2STG2STGmWSGmWSGmaSGWaSGWaRGWeRGGeRF2iQF2iQF2iQF2mQFmmQFmmP",
"FmiPFmeQFmaQFmaQFmWRFmORF2KRF2CRF1+SGF2SGVySGVuTGlmTGliTGleTG1aUG1WUG1SUG1SUG1OUHFKUHFKTG1GTG1GTG1GSG1GSG1GRGlGRGlCRGlCQGlCQGlCQGlCRGlCRG1CRG1GSHFGSHFCTHVCUHlCV",
"H1CWIFCXIVCXIk+YIk+YJE+ZJU6ZJU6aJk2aJ02bJ0ybKEybKUubKUubKkubKkqbKkqbK0qcK0qcK0qcK0qcK0qcK0qcK0qdK0udK0udK0udK0ueK0ueK0ueLEueLEueLEudLEqdLEqcLEmcLEmbLEiZLEaYLEWX",
"LESVLEOTLEGRLECPLD6NLDyLLTuJLTmILTiHLjaGLzWFMDSFMTSEMjOFMzOFNDKGNTKHNjKINzOJODOKODSLOTSMOjWNOjaNOjeOOjiOOjmPOTqPODuPNzyONj6ONT+ONEGNM0KNMUSNMEaNL0eMLUqMLEuNK02N",
"Kk+NKVGOJ1OOJlWPJVaQJFiRI1mRIluSIVySIVyTIF2TH16UH1+UHl+VHmCVHmCWHWCWHWCWHGCWHGCWHGGWHGGWHGGWG2GWG2KWG2KWG2KVGmOVGmOVGmSUGmSUGWWUGWWUGWaTGGaTF2eTF2eTF2eTF2iTF2iS",
"FmeSFmaSFmaSF2WTF2STF2KTGGGUGGCUGV+UGV2VGlyVGlqVG1mWG1iWHFeWHFaWHFWWHFSWHVOVHVKUHVGUHVGTHFCTHFCSHFCRG0+RG0+QG0+PGk+PGk+OGk+OGk+OGk+OGk+OGlCPGlCQG1CQG1CRHFCSHFCT",
"HVCUHlCVH1CWIFCXIVCYIlCZIlCZI1CaJE+bJU+bJU+bJk6cJ06cJ06cJ02cKE2cKE2cKE2dKU2dKU2dKU2dKU2dKU2dKU2dKU2dKU2eKU2eKU6eKU6eKU6eKU6eKU2eKU2dKU2dKUycKUycKUubKUqZKUmYKUiW",
"KUaUKUWTKUSRKUKPKUCNKj+LKj2JKjuHKzqGKziFLDeDLTWDLjWDLzSDMDODMTOEMzKFNDKGNTOHNjOINzOJODSLODSMOTWNOjaOOjeOOjiPOTmQOTqQODuQNzyQNj6QNT+QNEGPM0KPMUSPMEaPL0iPLUqPLEyP",
"K06QKVCQKFGRJ1ORJlWSJVaSJFiTIlmUIVqUIVuVIFyVH1yWH12WH12WHl6XHl6XHV6XHV+XHF+XHF+XHF+XHF+XHGCXG2CXG2CXG2CXG2GXGmGXGmKWGmKWGmOWGWOWGWSVGWSVGGWVGGWUF2WUF2aUF2aUF2aU",
"F2aUF2aUF2WVF2SVGGOVGWKWGWGWGWCXGl6XGl2XG1uXG1qXHFmXHFeXHVaXHlWXHlSWHlOWHlKVHlGUHlCTHk+SHk+RHU6QHE6PHE2OG02NG02MGk2LGk2LGk2KGU2KGU2LGU6LGU6LGU+MGk+NGk+OGlCQG1CR",
"HFCSHFCTHVGUHlGWH1GXIFGYIFGZIVGZIlGaIlGbI1GbJFGcJFCcJVCcJVCcJlCdJlCdJlCdJlCdJlCdJlCdJlCdJlCdJlCdJlCdJlCeJlCeJlCeJlCeJlCdJlCeJlCdJlCdJk+cJk+cJk+bJk6aJk2ZJkyYJkuW",
"JkmUJkiSJkaRJkWOJkOMJkGKJz+IJz6HJzyFKDqDKTmCKjiCKzaBLDWBLTWCLzSCMDSDMTOEMzOGNDOHNTOINjSJNzSLODWMODWOOTaOOTiQOTiQOTmRODuRODyRNz2SNj+SNUCSNEKRMkSRMUWRMEeRLkmSLEuS",
"K02SKk+SKVCTJ1KTJlSUJVWUJFeVIliVIVmWIVqWIFuXH1yXH1yXHl2XHl2YHV2YHV2YHF2YHF6YHF6YHF6YG16YG16YG1+YG1+YG1+YGmCXGmCXGmCXGmGXGmGXGWKXGWKWGWOWGGOWGGSWGGSWF2SWF2WWF2WW",
"F2WXGGWYGGSYGWOYGWKYGWGZGmCZGl+ZG16ZHFyZHFuZHVqZHliZHleZH1aYH1SYH1OXH1KWH1CVH0+UH06TH02RHk2QHkyOHUuNHEuLHEuKG0qJGkqIGkqHGUuHGUuHGUuHGEyHGEyIGE2JGU2KGU6LGU+NGlCO",
"GlCQG1GRG1GTHFGUHVKVHlKXH1KYH1KZIFKaIFKaIVKbIlKcIlKcIlKdI1KdI1KdI1KdJFKeJFKeJFKeJFKeJFKeJFKeJFKeJFKeJFKeJFKeJFKeJFKeI1KeI1KeI1KdI1KdI1KdI1GcI1GbI1CaI1CZI06YI02X",
"I0yVI0uTI0mRI0iPI0aNJESLJEKJJEGHJT+GJT2EJjyDJzqCKDmBKjiBKzeBLDaCLTWDLzWEMDWFMjWHMzWINTWKNjWLNzaNNzaOODePODiRODmSODqTODuTODyUNz2UNj+UNUGUNEKUMkSUMUaUMEeULkmVLUuV",
"K02VKk+VKVCWJ1KWJlOXJVWXJFaXIliYIViYIFqYIFuZH1uZHlyZHlyZHVyZHVyZHF2ZHF2ZHF2ZG12ZG12ZG12ZG12ZG16ZG16ZGl6ZGl6ZGl+YGl+YGmCYGWCYGWGYGWGYGWKYGGKYGGKYGGOYGGOYF2OYF2OY",
"GWOZGWOZGWKZGmKZGmGaGmCaG16aG12aHFyaHVuaHlmaHliaH1aZH1WZIFOYIFKXIFCWIE+VIE6TIE2SIEuQIEqOH0mMHkiKHkiJHEeHHEeFG0eEGkeDGUeCGUeCGEeBF0iBF0iCF0mDF0qEF0uFF0yGF0yIGE2K",
"GU6LGU+NGlCPG1GRG1GSHFKUHVKVHVKWHlOYH1OZH1OZIFOaIFObIFObIVOcIVOcIVOcIVOdIVOdIVOdIVOdIVOdIVOdIVOdIVOdIVOdIVOdIVOdIVOdIVOcIVOcIVOcIVOcIVObIVKaIVKaIVGZIVGYIVCXIU+W",
"IU6UIU2TIUuRIUqPIUiNIUeLIUWJIUOHIkGGI0CEIz6DJDyCJTuBJjqBKDmBKTiBKzeCLDaDLjaELzaGMTaHMjaJNDaLNTeNNjeONziPNzmRNzqSODuTNzyUNz2VNz6VNkCWNUGWNEKWMkSXMUaXMEeXLkmXLUuX",
"K02XKk6YKFCYJ1KYJlOYJFWYI1aZIleZIViZIFiZH1qZH1qZHluZHVuZHFuZHFuZHFuZG1uZG1yZG1yZG1yZGlyZGlyYGlyYGlyYGl2YGl2YGl2YGV2YGV6YGV6YGV+YGV+YGV+YGGCYGGCYGGGYGGGYF2GYF2GY",
"GWKaGmGaGmGaGmCaG1+aG16aHF2aHVuaHlqaHliaH1eaIFWZIFSZIVKYIVGXIU+VIU6UIUySIUuRIUmOIUiMIEeKH0aIH0WGHkSEHEOCG0OAG0J+GkJ9GUJ8GEN7F0N7F0R7FkR7FkV8FkZ+Fkd/FkiAFkmCF0uE",
"F0yGF02JGE6KGU+MGlCPGlGQG1GSG1KTHFKUHFOWHVOXHVOYHlOYHlOZH1OZH1SaH1SaH1SaH1SbH1SbH1SbH1SbH1SbH1SbH1SbH1SbH1SaH1SaH1SaH1SaH1SaH1SaH1OaH1OZH1OZH1OZH1KYH1KXH1GWH1CV",
"H1CUH06SH02RH0yPH0qNH0mLH0eJH0WIIESGIEKEIUCDIj+CIz2BJDyBJTuBJzqBKDmCKjiCKziELTeFLjeHMDeIMTiKMziMNDmONTmQNjqRNjuTNjyUNj2VNj6WNj+XNUGYNEKYM0OYMkWYMUaZL0iZLUqZLEuZ",
"K02ZKU+ZJ1CZJlKZJVOZJFSZIlWZIVaZIFeZH1iZH1iZHlmZHVmZHFqZHFqYG1qYG1qYG1qYGlqYGlqYGlqXGlqXGlqXGlqXGVuXGVuXGVuXGVuXGVyXGVyXGVyXGV2XGF2XGF2XGF6XGF6XGF6XGF6XF1+XF1+X",
"Gl+bGl+bG16bG12cHFycHFucHVqbHlmbH1ebIFabIFSaIVOZIVGZIk+XIk6VIkyUIkqSIkmQIkeOIkaLIUSJIEOGIEKEH0GBHj9/HD98Gz57Gj55GT53GD52Fz51Fj51Fj91FUB2FUF2FUJ4FUN5FUR7FUZ9FUd/",
"FkiCFkqEF0uGF0yJGE2LGE+NGVCOGlCQGlGSG1KTG1KUG1KVHFOWHFOXHFOYHVOZHVSZHVSZHVSZHVSZHVSZHVSZHVSZHVSZHVSZHVSZHVSZHVSZHVSZHFSZHFSZHFOYHFOYHFOYHFOYHFOXHFOXHFKWHFKWHFGV",
"HFCUHFCTHE+RHE2QHUyOHUuNHUmLHUeJHkaIHkSGH0OFIEGEIUCDIT6CIz2CJDyCJjuDJzuDKTqFKjqGLDqILTqJLzqLMDqNMTqPMzuRNDyTNDyUNT2VNT6XNUCYNEGZNEKaM0OaMkWaMUabL0ebLkmbLEubK0yb",
"Kk2bKE+bJ1GbJVKbJFObIlSaIVWaIFaaH1aaHleaHleZHViZHFiZG1iZG1iYGliYGliXGliXGliXGViWGViWGViWGViWGViWGViWGViWGVmWGVmWGFmWGFqWGFqWGFqWGFuWGFuWGFuXGFyXF1yXF1yXF1yXF1yX",
"G12bG1ybHFybHFubHVqbHlmbHlibH1abIFWaIVOZIVKZIlCXIk6WI0yVI0qTJEiRJEePI0WMIkOJIkKHIUCEID6BID1+Hzx7HTt4HDp2GzpzGjlxGDlwFzlvFjluFTpuFTpuFDtuFDxvFD1xFD9yFEB0FEJ2FEN5",
"FEV7FUZ+FUiAFkmDFkuFF0yIF02KGE6LGE+NGVCPGVGQGlGSGlKTGlKUGlKUG1OVG1OVG1OWG1OWG1OWG1OWG1OWG1OWG1OWG1OWG1OWG1OVG1OVG1OVG1OVG1OVG1OVG1OVG1OVG1OVG1KVG1KUG1KUG1KUG1GT",
"G1GSG1CSG0+QG0+PG02OG0yNG0uLG0mKHEiIHEeHHUWGHkSFH0KEIEGDIUCDIj+DIz6DJT2EJjyFKDyGKTyIKzyJLDyLLjyNLzyPMD2RMT2TMj6VMj+WMkCYMkGZMkKaMkSbMUWbMEabL0icLkmcLEucK0ycKk2c",
"KE+cJ1CbJVGbJFKbIlObIVSaIFWaH1WaHlaZHVaZHFaYHFaXG1aXGlaWGlaWGlaVGVaVGVaUGVaUGVaUGFaTGFaTGFaTGFaTGFaTF1aTF1aTF1aTF1eTF1eUF1eUF1iUF1iUF1iUF1mUF1mUF1mVF1mVF1mVF1qV",
"HFubHFqbHFmbHVibHleaH1aaH1WaIFOZIVKYIlCXIk6WI0yVJEuTJEmRJEePJEWNJEOKJEGHIz+EIj2BITx+IDp7Hzh3Hjd1HDZxGzVvGjVsGTRqFzRpFjRnFTRmFDVmFDVmEzZnEzhoEzlpEjprEzxtEz1vEz9y",
"E0F0FEJ3FER6FEZ8FUd/FUmBFkqEFkuGF0yIF02KF06MGE+NGFCOGVCPGVGQGVGRGVGRGVKSGVKSGVKSGVKSGVKSGVKSGVKSGVKSGVKSGVKRGVGRGVGRGVGRGVGRGVGRGVGRGVGRGVGRGVGRGVGRGVGRGVGRGVGR",
"GVGQGVCQGVCPGU+OGk6OGk2NGkyLGkuKGkqJG0mIG0iHHEaGHUWFHkSFH0OEIEGEIUGFIkCFJD+GJT+HJz6JKD6KKj6MKz6OLD+QLkCSL0CTL0GVMEKXMEOYMESZMEWbMEabL0ecLkidLUmdLEudK0ydKk2dKE+d",
"J1CcJVCcJFGbIlKbIVOaIFOaH1SZHlWYHVWYHFWXG1WWG1WVGlWUGlSUGVSTGVSSGFSRGFORF1OQF1OQF1OQF1OPF1OPF1OPF1OPF1OPF1OPF1OPF1SQF1SQF1SQF1WQF1WRF1WRF1aRF1aSF1aSF1aSF1aSF1eT",
"HVmbHlibH1eaH1eaIFWaIVSZIVOZIlGYI1CXI06VJEyUJUqTJUiRJUaOJkSMJUKJJT+GJT6DJDyAIzp8Ijh5ITZ1IDVyHjNvHTJsGzJpGjFmGDBkFzBiFjBhFTBgFDFfFDFfEzJgEjRhEjVjEjZlEjhnEjppEjts",
"Ez1uEz9xFEF0FEN3FUR5FUZ8Fkd/FkmBFkqDF0uFF0yHF02JGE6KGE+LGE+MGFCNGFCNGFCOGFCOGFGOGFGOGFGOGFGOGFCOGFCOGFCOGFCOGFCNGFCNGFCNGFCNGFCNGFCNGFCOGFCOGFGOGFGOGFGOGFGOGFGP",
"GVGPGVGPGVCOGVCOGVCOGk+NGk6MGk2LGk2LG0yKG0uJG0mIHEiIHUeHHkaHH0WHIESHIUSII0OIJEOJJkKKJ0KMKEKOKkKQK0ORLEOTLUSVLkSXLkWYL0aaL0ebL0icLkmdLkqeLUueLEyeK02eKk6eKFCeJ1Ge",
"JlGdJFKcI1OcIlObIVOaIFSZH1SYHVSXHVSWHFSVG1SUGlOTGlOSGVORGVOQGFKPGFKOGFGNF1GNF1GMF1GMF1GMF1GLF1GLF1GLF1GLF1GLF1GMF1GMF1KMF1KNF1KNF1KNF1OOF1OOF1OOGFOPGFSPGFSQGFSQ",
"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",
"H0aJIEWIIESIIUOHIUKGIkCFIj+DIz2CIzuAIzl9JDd7JDV4IzN1IzFyIi5uIixrISpnIChjHiZfHSVbHCNXGiFTGSBQFx9MFh5JFR1HExxEEhxCERtBEBs/Dxs+Dxw+Dhw+DR0/DR4/DR9BDSBCDSFEDSNGDSRJ",
"DSZLDihODipRDytTDy1WDy9ZEDFbEDJeEDRgETVjETZlEThnETloETppEjprEjtsEjxsEjxtEjxtEjxtEjxuEjxtEjxtEjxtEjxtEjxtEjxsEjtsEjtsEjtsEjtsEjxtEjxtEjxuEj1uEj5vEj5xEj9yE0BzE0J1",
"FEN3FER5FEV7FEZ9FUd+FUiAFUmCFUuEFkyFFkyGFk2IF02JF06KF06LGE6MGU6NGk6NGk+PG0+QHE+QHE+RHU+SHk+UH0+VIFCWIFCXIVCYIVGaIlGaIlGbIlKcIlKcIlKcIVKcIVKcIFKbIFKaH1KYHlKXHVGV",
"HFGUG1CSG0+PGk6NGU2KGEyIF0qFFkiCFkeAFUZ9FUR7FEN4FEJ2FEB0Ez9yEj5xEj1vEjxuEjxtEjtsEjtrEjpqETpqETpqEjpqEjpqEjpqEjtrEjtrEjtsEjtsEjxtEzxuEzxuFDxvFD1wFD1wFD1xFD1xFT1y",
"H0KDH0GDIECCID+CIT6AIT1/Ijt+Ijl8Ijd6IjV3IzN1IjFyIi9vIi1sIStoIClkHydhHiVdHSNZGyJVGiBSGB5OFx1KFhxIFBtFExtCEhpAEBk+EBk8Dxk7Dhk6DRk6DRo6DBo6DBs7DBw8DB0+DB4/DCBBDCFE",
"DSNGDSRIDSZLDShNDilQDytSDy1VDy5YDzBaEDFcEDJeEDNgEDRhEDVjETZkETdlETdlETdmEThmEThnEThnEThnEThmEThmETdmETdmETdmETdlETdlETdlETdlETdmEThmEThnETloETlpETpqEjtsEjxtEj5v",
"Ej9xEkBzE0J1FEN4FEV6FEZ8FEd+FUmAFUqDFUuFFkyGFk2IFk6JF06LF0+MGE+NGFCOGVGQGlGRG1GSG1GTHFGUHFGVHVKWHlKXH1KYH1KZIFOaIFObIFObIFOcIFScIFSbH1SbH1SaHlOZHVOYHVKWHFKVG1GT",
"G1CQGk6OGU2LGEyJF0qGFkmDFkeAFUZ9FUR6FEJ4FEF1Ez9yEj5wEjxuEjtsETpqETloEThnETdmETdlETZkETZkEDZjEDVjETVjETVjETZkETZkETZlETZlETdmETdmEjdnEjhoEjhoEjhpEzhqEzlqFDlqFDlr",
"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",
"FyNQFyJQFyJPFyFPFyFOFyBNFx9MFx5KFh1JFhxHFhtFFRpEFRlCFBhAExc+Ehc8EhY6ERU4EBQ2DxM0DhMyDhIxDRIwDBIvDBEtDBEsCxEsCxErCxErChArChAqChAqChEqChEqChErChErChErChErChIsChIs",
"ChMtChMuChMvCxQwCxUwCxUxCxYyCxczCxc0Cxg1Cxg2Cxg2Cxk3DBk3DBo4DBo4DBo5DBo5DBo5DBo5DBo5DBo5DBo5DBo5DBo5DBo5DBo5DBo4DBo4DBo5DBo5DBo5DBs5DBs6DBw6DBw8DB09DB0+DB4/DR9B",
"DSFDDSJFDSRIDiZKDihNDilQDytTEC5XEDBaETJeETVhETdlEjloEjtsEz5vE0ByFEJ2FER4FUV7FUd9FUh/FkmBFkqDFkuEFkuFFkuFFkuFFkuFFkuFFkqEFkqCFkmBFkd/FUZ8FUR6FUN3FEF1Ez9xEzxuEjpq",
"EjhnETVjETNfEDFcEC9YECxVDypRDihODiZLDiRIDSNGDSFDDSBBDB4/DB0+DB08DBw7DBs6DBo5DBo5DBo4DBk4DBk4DBk3DBk3DBk3DBk4DBk4DBo4DBo4DBo5DBo5DBo5DBo6DRs6DRs7DRs7DRs7DRs8DRs8",
"FR9KFR9JFR5JFR5IFR1HFR1GFRxFFBtEFBpDFBlBExlAExg+Ehc9EhY7ERY5ERU3EBQ2DxM0DhMzDhIxDRIwDRIvDBEuDBEtCxEsCxErCxArCxAqChAqChAqChAqChAqChAqChAqChAqChAqChEqChErChErChEr",
"ChIsChIsChItChMtChMuChQvCxQwCxQwCxUxCxUyCxYyCxYzCxczCxc0Cxc0Cxc1Cxg1Cxg1Cxg1Cxg1Cxg1Cxg1Cxg1Cxg1Cxg1Cxg1Cxc1Cxc1Cxc1Cxc1Cxc1Cxg1Cxg1Cxg2Cxg2Cxk3DBo4DBo5DBs6DBw8",
"DB0+DR9ADSBCDSJEDSRHDiZKDihNDipQDyxUEC5XEDBaETJeETVhEjdlEjloEjtsEz1vEz9yE0F0FEJ3FER5FUV7FUZ8FUd+FUd+FUd/FUd/FUd/FUd+FUZ9FUZ8FUV6FUN4FEJ2E0BzEz5wEzxtEjpqEjhnETVj",
"ETNfEDFcEC9YECxVDypRDihODiZLDiRIDSJFDSFCDR9ADB4+DB08DBw6DBo5DBo4Cxk3Cxg2Cxg1Cxc1Cxc0Cxc0Cxc0Cxc0Cxc0Cxc0Cxc0Cxc0Cxc0Cxc1Cxc1DBc1DBg1DBg2DBg2DBg2DBg3DBg3DBg3DBg3",
"ExxEExxEExtDExtDExpCExpCExlBEhlAEhg+Ehc9Ehc8ERY6ERU5EBQ4EBQ2DxM1DhM0DhIyDRIxDRIwDBEvDBEuCxEtCxEsCxAsCxArChArChArChArChAqChAqChAqChAqChAqChAqChAqChArChArChErChEr",
"ChEsChEsChEsChItChItChIuChMuChMvChMvCxQwCxQxCxQxCxUxCxUyCxUyCxUyCxUyCxUzCxYzCxYzCxYzCxYzCxYzCxUzCxUzCxUyCxUyCxUyCxUyCxUyCxUyCxUzCxYzCxYzCxY0Cxc1Cxc1Cxg2Cxg3DBk5",
"DBo6DBw8DB0+DB5ADSBDDSJFDSRIDiZLDihODypRDyxVEC5YEDBbETJfETViETdmEjlpEjtsEzxuEz5xEz9zE0F1FEF2FEJ3FEN4FEN5FEN5FEN5FEJ4FEJ3FEF2E0B0Ez9yEz1wEjttEjlqEjdnETVkETNgEDFd",
"EC9ZECxWDypTDihPDiZMDiRJDSJGDSFDDR9BDB0/DBw8DBs7DBo5Cxg3Cxg2Cxc1Cxc0CxYzCxYzCxUyCxUyCxUyCxUyCxUyCxUyCxUyCxUyCxUyCxUyCxUyCxUyCxUzCxUzCxUzCxYzDBY0DBY0DBY0DBY0DBY1",
"ERk/ERk+ERg+ERg9ERg9ERc8ERc7ERc7ERY6EBU5EBU4DxQ3DxQ2DhM0DhMzDRIyDRIxDRIwDBEvDBEuDBEtCxEtCxAsCxAsChArChArChArChAqChAqChAqChAqChAqChAqChAqChAqChAqChAqChAqChArChAr",
"ChErChErChErChEsChEsChEsChItChItChItChIuChMuChMvChMvChMvChMvChMwChQwCxQwCxQwCxQwCxQwCxQwCxQwCxQwCxQwChQwChMwChMwChMwChMwChMwCxQwCxQwCxQxCxQxCxUxCxUyCxYzCxY0Cxc1",
"Cxg2Cxk4DBo6DBw8DB0+DB5ADSBDDSJFDSRIDiZLDihODypRDyxVEC5YEDBbETJfETRiETZlEjhnEjlqEjtsEjxuEz1vEz5wEz5xEz5yEz5yEz5xEz5xEz1wEzxuEjtsEjprEjhoETdmETVjETNgEDFcEC9ZECxW",
"DypTDihPDiZMDiRJDSJGDSFDDR9BDB0+DBw8DBo6Cxk4Cxg3Cxc1Cxc0CxYzCxUyCxQxCxQxCxQwChMwChMvChMvChMvChMvChMvChMvChMvCxMvCxMvCxMwCxMwCxMwCxQwCxQxCxQxCxQxCxQxCxQxCxQxCxQy",
"EBc6EBc5EBY5EBY5EBY4DxU4DxU3DxU3DxQ2DhQ1DhM0DhMzDhMyDRIxDRIxDRIwDBEvDBEuDBEtCxEtCxAsCxAsCxArChArChArChAqChAqChAqChAqChAqChAqChAqChAqChAqChAqChAqChAqChAqChAqChAq",
"ChAqChArChArChErChErChErChEsChEsChEsChEsChItChItChItChItChItChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChIuChMuChMvChMvChMwCxQwCxQxCxUy",
"CxYzCxc1Cxg2Cxk4DBo6DBw8DB0+DB5ADSBDDSJGDSRIDiZLDihODypRDyxVEC5XEC9bEDFdETNgETRiETZkETdmEjhoEjlpEjlqEjlqEjpqEjlqEjlpEjhoEjdnETZlETVjETNgETJeEDBbEC5YECxWDypSDihP",
"DiZMDiRJDSJHDSFEDR9BDB0+DBw8DBo6Cxk4Cxg2Cxc1CxYzCxUyCxQxCxQwChMwChMvChMuChIuChIuChItChItChItChItChItChItChItChItChItChIuChIuChIuChIuCxIuCxIuCxIvCxMvCxMvCxMvCxMv",
"DhU3DhU3DhQ2DhQ2DhQ2DhQ1DhM1DhM0DRM0DRMzDRIyDRIyDRIxDBIwDBEwDBEvCxEuCxEuCxAtCxAtCxAsChAsChAsChAsChArChArChArChArChArChArChArChArChArChArChArChArChArChArChArChAr",
"ChArChArChArChArChAsChAsChAsChEsChEsChEsChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChIuChIuChIuChIvChMvChMwChMx",
"CxQyCxUzCxY0Cxc1Cxg3Cxk5DBo7DBw9DB0/DB5BDSBEDSJHDSRJDiZMDihPDilSDytVECxXEC5aEDBcEDFeETJgETNhETRiETRjETRjETRjETRjETRiETNhETJgEDFeEDBcEC9aEC1YDytVDypSDihQDiZNDiRK",
"DSNIDSFFDR9CDB1ADBw9DBo7Cxk5Cxg3Cxc2CxY0CxUzCxQyChMxChMwChMvChIvChIuChIuChItChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEtChEuChEuChEuChIuChIuCxIuCxIu",
"DRQzDRQzDRQzDRQzDRMzDRMyDRMyDRMyDBMxDBMxDBIwDBIwDBIvDBIuCxIuCxItCxEtCxEtCxEsChEsChEsChEsChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChEr",
"ChErChErChErChErChErChErChErChErChEsChEsChEsChEsChEsChEsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChIsChItChItChItChIuChMuChMv",
"ChMvChQwCxUyCxUzCxY0Cxc1Cxk3Cxo5DBs7DBw9DB4/DR9BDSFEDSNGDSRJDiZLDidODilQDypSDyxVDy1XEC5YEC9ZEDBaEDBbEDBcEDBcEDBbEDBbEC9aEC5YEC1XDyxVDytTDilRDihPDiZMDSVKDSNHDSFF",
"DSBCDB5ADB0+DBs8DBo5Cxk4Cxg2Cxc0CxYzCxUyChQxChQwChMvChMuChIuChItChItChItChIsChIsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChIsChIsChIsChIsChItChItChItChItChItChIt",
"DBMxDBMxDBMxDBMwDBMwDBMwDBIwDBIvDBIvDBIvCxIuCxIuCxItCxItCxEtCxEtChEsChEsChEsChEsChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChEr",
"ChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChErChEsChEsChEsChEsChEsChEsChEsChEsChEsChErChErChErChErChErChErChEsChEsChEsChEsChIsChIsChItChItChIt",
"ChMuChMuChQvChQwCxUyCxYzCxc0Cxg2Cxk3Cxo5DBs7DB09DB4/DB9BDSFDDSJGDSRIDSVKDiZMDidODilQDipRDipSDytTDytUDyxUDyxUDytUDytTDytSDipRDilQDihODidMDiVLDSRIDSNGDSFEDSBCDB5A",
"DB0+DBw8DBo6Cxk4Cxg2Cxc0CxYzCxUyChQxChQwChMvChMuChItChItChItChIsChIsChEsChEsChEsChErChErChErChErChErChErChErChErChErChErChEsChEsChEsChEsChEsChEsChEsChEsChEsChEs",
"CxIwCxIwCxIvCxIvCxIvCxIvCxIvCxIvCxIuCxIuCxEuCxEuCxEtChEtChEtChEtChEtChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEs",
"ChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEtChEtChItChIt",
"ChIuChIuChMvChMwChQwChQxCxUzCxY0Cxc1Cxg3Cxk4Cxo6DBs8DB0+DB5ADB9BDSBDDSFFDSNHDSRIDSRKDiVLDiZMDiZNDidODidODidODidODidNDiZNDiZMDSVKDSRJDSNHDSJGDSBEDB9CDB5ADB0+DBs8",
"DBo6Cxk5Cxg3Cxc1CxY0CxUzChQyChQxChMwChMvChIuChIuChItChItChEtChEtChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEsChEs",
"DBIuDBIuDBIuDBIuDBIuCxEuCxEuCxEuCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEs",
"CxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEtCxEt",
"CxItCxItCxIuCxIuCxMvCxMwCxQwCxQyCxUzDBY0DBc1DBg3DBk4DBo6DBs7DRw9DR0+DR5ADR9CDSBDDSFEDSFFDiJGDiJHDiNHDiNIDiNIDiNHDiNHDiJGDiJGDSFEDSBDDR9CDR5ADR0/DRw9DBs8DBo6DBk4",
"DBg3DBc1DBY0CxUzCxUyCxQxCxMwCxMvCxMuCxIuCxIuCxItCxEtCxEtCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEs",
"CxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEs",
"CxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEs",
"CxEtCxEtCxItCxItCxIuCxIuCxMvCxMwCxQxCxQyDBUzDBY0DBc1DBg2DBg4DBk5DRo6DRs7DRw9DR0+DR0/DR5ADR5BDR9BDR9CDR9CDR9CDR9CDR9CDR5BDR5ADR4/DR0+DRw9DRs8DRo7DBk5DBk4DBg3DBc1",
"DBY0DBUzCxUyCxQxCxMwCxMvCxMvCxIuCxIuCxItCxEtCxEtCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEsCxEs",
"CxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEt",
"CxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEt",
"CxEtCxEtCxEuCxEuCxIuCxIuCxIvCxIvCxMwCxMxCxQyCxQzDBU0DBY0DBY1DBc2DBg4DBk5DBk6DBo7DRo8DRs8DRs9DRw9DRw+DRw+DRw+DRw+DRw9DRs9DRs8DRo8DBo7DBk6DBk5DBg4DBc3DBc2DBY1DBU0",
"CxQzCxQyCxMxCxMwCxMwCxIvCxIvCxIuCxEuCxEuCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEt",
"CxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEt",
"CxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEt",
"CxEtCxEtCxEtCxEtCxEuCxIuCxIuCxIvCxIvCxMvCxMwCxQxCxQxCxUyDBUzDBY0DBY1DBc2DBc2DBg3DBg4DBk5DBk5DBk5DBk6DBk6DBk6DBk6DBk6DBk5DBk5DBg4DBg3DBg3DBc2DBY1DBY0DBUzCxUyCxQy",
"CxQxCxMwCxMwCxMvCxIvCxIuCxIuCxEuCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEtCxEt",
"CxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxIt",
"CxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxIt",
"CxItCxItCxItCxItCxItCxItCxIuCxIuCxMuCxMvCxMvCxMvCxQwCxQwCxQxCxUyCxUyDBYzDBY0DBY0DBc1DBc1DBg2DBg2DBg2DBg2DBg2DBg2DBg2DBg2DBc1DBc1DBc0DBY0DBYzCxUzCxUyCxUxCxQxCxQw",
"CxQwCxMvCxMvCxMuCxMuCxIuCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxItCxIt",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIvCxIvCxMvCxMvCxMwCxMwCxQxCxQxCxQxCxQyCxUzCxUzCxUzCxU0DBY0DBY0DBY1DBY1DBY1DBY1DBY0DBY0CxY0CxUzCxUzCxUzCxUyCxQyCxQxCxQxCxMwCxMw",
"CxMwCxMvCxMvCxIvCxIvCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIvCxIvCxMvCxMvCxMwCxMwCxMwCxQxCxQxCxQxCxQxCxQyCxQyCxUyCxUyCxUyCxUyCxUyCxUyCxQyCxQyCxQxCxQxCxQxCxQxCxMwCxMwCxMwCxMvCxMv",
"CxIvCxIvCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIvCxIvCxIvCxMvCxMvCxMvCxMwCxMwCxMwCxMwCxMwCxQxCxQxCxQxCxQxCxQxCxQxCxQwCxMwCxMwCxMwCxMwCxMwCxMvCxMvCxMvCxIvCxIv",
"CxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIuCxIu",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIv",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIv",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIwCxIwCxIwCxIwCxMwCxMwCxMwCxMwCxMwCxMwCxMxCxMxCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxIwCxIwCxIwCxIvCxIvCxIv",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIv",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIv",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIv",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIwCxIwCxIwCxIwCxIwCxIwCxIwCxIwCxIwCxIwCxIwCxIwCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIv",
"CxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIvCxIv",
"CxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMv",
"CxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMv",
"CxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMv",
"CxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMvCxMv",
"CxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMw",
"CxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMw",
"CxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMw",
"CxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMwCxMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMwDBMw",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMxDBMx",
"DBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQx",
"DBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQx",
"DBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQx",
"DBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQxDBQx",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQyDBQy",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
"DBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQzDBQz",
NULL };


static int hr_b64v(int c)
{
    if (c >= 'A' && c <= 'Z') return c - 'A';
    if (c >= 'a' && c <= 'z') return c - 'a' + 26;
    if (c >= '0' && c <= '9') return c - '0' + 52;
    if (c == '+') return 62;
    if (c == '/') return 63;
    return -1;
}

static size_t hr_b64_len(const char *const *lines)
{
    size_t n = 0;
    int i;
    for (i = 0; lines[i]; i++) n += strlen(lines[i]);
    return n * 3 / 4 + 8;
}

static size_t hr_b64_decode(const char *const *lines, uint8_t *out, size_t cap)
{
    size_t n = 0;
    uint32_t acc = 0;
    int bits = 0, i;
    const char *s;
    for (i = 0; lines[i]; i++)
        for (s = lines[i]; *s; s++) {
            int v = hr_b64v((unsigned char)*s);
            if (v < 0) continue;                       /* '=' u otro caracter: no aporta bits */
            acc = (acc << 6) | (uint32_t)v;
            bits += 6;
            if (bits >= 8) {
                bits -= 8;
                if (n < cap) out[n++] = (uint8_t)(acc >> bits);
                acc &= (1u << bits) - 1u;
            }
        }
    return n;
}

static uint32_t hr_rd16(const uint8_t *p) { return (uint32_t)p[0] | ((uint32_t)p[1] << 8); }
static uint32_t hr_rd32(const uint8_t *p) { return (uint32_t)p[0] | ((uint32_t)p[1] << 8) | ((uint32_t)p[2] << 16) | ((uint32_t)p[3] << 24); }

/* 1 = fuentes listas. Todo se valida contra el tamano del bloque: si algo no cuadra, los menus usan el dibujo viejo. */
static int hr_load_faces(void)
{
    size_t cap = hr_b64_len(hr_faces_b64), n, pos = 0;
    int f, i;
    uint8_t *b = (uint8_t *)malloc(cap);
    if (!b) return 0;
    n = hr_b64_decode(hr_faces_b64, b, cap);
    g_hf_blob = b;
    if (n < 1 || b[0] != HF_COUNT) return 0;
    pos = 1;
    for (f = 0; f < HF_COUNT; f++) {
        uint32_t ng, dl;
        HrFace *fc = &g_hf[f];
        if (pos + 8 > n) return 0;
        fc->mid = (int8_t)b[pos]; fc->asc = b[pos + 1];
        ng = hr_rd16(b + pos + 2); dl = hr_rd32(b + pos + 4);
        pos += 8;
        if (pos + (size_t)ng * 11 + dl > n) return 0;
        fc->n = (int)ng;
        fc->g = (HrGlyph *)malloc(sizeof(HrGlyph) * (ng ? ng : 1));
        if (!fc->g) return 0;
        for (i = 0; i < (int)ng; i++) {
            const uint8_t *p = b + pos + (size_t)i * 11;
            fc->g[i].cp = (uint16_t)hr_rd16(p); fc->g[i].adv = p[2]; fc->g[i].xo = (int8_t)p[3]; fc->g[i].yo = (int8_t)p[4];
            fc->g[i].w = p[5]; fc->g[i].h = p[6]; fc->g[i].off = hr_rd32(p + 7);
            if ((size_t)fc->g[i].off + ((size_t)fc->g[i].w * fc->g[i].h + 1) / 2 > dl) return 0;
        }
        pos += (size_t)ng * 11;
        fc->bm = b + pos; fc->bmlen = dl;
        pos += dl;
    }
    return 1;
}

/* ---- primitivas ---- */
static void hr_rect(int x, int y, int w, int h, uint32_t c)
{
    int xx, yy;
    if (x < 0) { w += x; x = 0; }
    if (y < 0) { h += y; y = 0; }
    if (x + w > HR_W) w = HR_W - x;
    if (y + h > HR_H) h = HR_H - y;
    if (w <= 0 || h <= 0) return;
    for (yy = y; yy < y + h; yy++) {
        uint32_t *d = &g_hr[yy * HR_W + x];
        for (xx = 0; xx < w; xx++) d[xx] = c;
    }
}

static uint32_t hr_mix(uint32_t dv, uint32_t c, int a)      /* a = 0..255 (cuanto de c) */
{
    uint32_t r, g, b, t;
    t = ((c >> 16) & 255) * (uint32_t)a + ((dv >> 16) & 255) * (uint32_t)(255 - a) + 128; r = (t + (t >> 8)) >> 8;
    t = ((c >> 8) & 255) * (uint32_t)a + ((dv >> 8) & 255) * (uint32_t)(255 - a) + 128;   g = (t + (t >> 8)) >> 8;
    t = (c & 255) * (uint32_t)a + (dv & 255) * (uint32_t)(255 - a) + 128;                 b = (t + (t >> 8)) >> 8;
    return 0xFF000000u | (r << 16) | (g << 8) | b;
}

static void hr_rect_a(int x, int y, int w, int h, uint32_t c, int a)
{
    int xx, yy;
    if (a <= 0) return;
    if (x < 0) { w += x; x = 0; }
    if (y < 0) { h += y; y = 0; }
    if (x + w > HR_W) w = HR_W - x;
    if (y + h > HR_H) h = HR_H - y;
    if (w <= 0 || h <= 0) return;
    for (yy = y; yy < y + h; yy++) {
        uint32_t *d = &g_hr[yy * HR_W + x];
        for (xx = 0; xx < w; xx++) d[xx] = hr_mix(d[xx], c, a);
    }
}

static void hr_px(int x, int y, uint32_t c)
{
    if (x >= 0 && x < HR_W && y >= 0 && y < HR_H) g_hr[y * HR_W + x] = c;
}

static void hr_line(int x0, int y0, int x1, int y1, int lw, uint32_t c)
{
    int dx, sx, dy, sy, err, e2, h = lw / 2;
    if (y0 == y1) { hr_rect(x0 < x1 ? x0 : x1, y0 - h, (x0 < x1 ? x1 - x0 : x0 - x1) + 1, lw, c); return; }
    if (x0 == x1) { hr_rect(x0 - h, y0 < y1 ? y0 : y1, lw, (y0 < y1 ? y1 - y0 : y0 - y1) + 1, c); return; }
    dx = x1 > x0 ? x1 - x0 : x0 - x1; sx = x0 < x1 ? 1 : -1;
    dy = y1 > y0 ? y0 - y1 : y1 - y0; sy = y0 < y1 ? 1 : -1;
    err = dx + dy;
    for (;;) {
        hr_rect(x0 - h, y0 - h, lw, lw, c);
        if (x0 == x1 && y0 == y1) break;
        e2 = 2 * err;
        if (e2 >= dy) { err += dy; x0 += sx; }
        if (e2 <= dx) { err += dx; y0 += sy; }
    }
}

static uint32_t hr_isqrt(uint32_t v)
{
    uint32_t r = 0, b = 1u << 30;
    while (b > v) b >>= 2;
    while (b) {
        if (v >= r + b) { v -= r + b; r = (r >> 1) + b; } else r >>= 1;
        b >>= 2;
    }
    return r;
}

/* disco y anillo con borde suave: la distancia al centro se mide en 1/256 de pixel */
static void hr_blend_px(int x, int y, uint32_t c, int a)
{
    if (a <= 0 || x < 0 || x >= HR_W || y < 0 || y >= HR_H) return;
    if (a >= 255) g_hr[y * HR_W + x] = c; else g_hr[y * HR_W + x] = hr_mix(g_hr[y * HR_W + x], c, a);
}

static void hr_disc(int cx, int cy, int r, uint32_t c)
{
    int x, y;
    for (y = cy - r - 1; y <= cy + r + 1; y++)
        for (x = cx - r - 1; x <= cx + r + 1; x++) {
            int d = (int)hr_isqrt((uint32_t)((x - cx) * (x - cx) + (y - cy) * (y - cy)) * 65536u), a = (r * 256 + 128 - d);
            if (a >= 256) a = 255;
            hr_blend_px(x, y, c, a);
        }
}

static void hr_ring(int cx, int cy, int r, int lw, uint32_t c)
{
    int x, y, ri = r - lw;
    for (y = cy - r - 1; y <= cy + r + 1; y++)
        for (x = cx - r - 1; x <= cx + r + 1; x++) {
            int d = (int)hr_isqrt((uint32_t)((x - cx) * (x - cx) + (y - cy) * (y - cy)) * 65536u);
            int ao = r * 256 + 128 - d, ai = d - (ri * 256 - 128), a;
            if (ao > 256) ao = 256;
            if (ai > 256) ai = 256;
            if (ao <= 0 || ai <= 0) continue;
            a = ao * ai / 256;
            hr_blend_px(x, y, c, a > 255 ? 255 : a);
        }
}

static int hr_rr_in(int px, int py, int x0, int y0, int x1, int y1, int r)
{
    int cx, cy, dx, dy;
    if (px < x0 || px > x1 || py < y0 || py > y1) return 0;
    cx = px < x0 + r ? x0 + r : (px > x1 - r ? x1 - r : px);
    cy = py < y0 + r ? y0 + r : (py > y1 - r ? y1 - r : py);
    dx = px - cx; dy = py - cy;
    return dx * dx + dy * dy <= r * r;
}

static void hr_rr_out(int x0, int y0, int x1, int y1, int r, int lw, uint32_t c)
{
    int x, y, ri = r - lw < 0 ? 0 : r - lw;
    for (y = y0; y <= y1; y++)
        for (x = x0; x <= x1; x++)
            if (hr_rr_in(x, y, x0, y0, x1, y1, r) && !hr_rr_in(x, y, x0 + lw, y0 + lw, x1 - lw, y1 - lw, ri)) hr_px(x, y, c);
}

static void hr_rr_fill(int x0, int y0, int x1, int y1, int r, uint32_t c)
{
    int x, y;
    for (y = y0; y <= y1; y++)
        for (x = x0; x <= x1; x++)
            if (hr_rr_in(x, y, x0, y0, x1, y1, r)) hr_px(x, y, c);
}

/* triangulo: dir 0 = apunta arriba, 1 = abajo, 2 = izquierda, 3 = derecha; (cx,cy) = centro, s = tamano */
static void hr_tri(int cx, int cy, int s, int dir, uint32_t c)
{
    int i;
    for (i = 0; i < s; i++) {
        int half = i * s / (2 * s) + (i + 1) / 2;       /* ancho crece de 0 a ~s en s pasos */
        if (dir == 0) hr_rect(cx - half, cy - s / 2 + i, half * 2 + 1, 1, c);
        else if (dir == 1) hr_rect(cx - half, cy + s / 2 - i, half * 2 + 1, 1, c);
        else if (dir == 2) hr_rect(cx - s / 2 + i, cy - half, 1, half * 2 + 1, c);
        else hr_rect(cx + s / 2 - i, cy - half, 1, half * 2 + 1, c);
    }
}

/* ---- texto ---- */
static int hr_u8next(const char **ps)
{
    const unsigned char *s = (const unsigned char *)*ps;
    int c = s[0];
    if (c == 0) return 0;
    if (c < 0x80) { *ps += 1; return c; }
    if ((c & 0xE0) == 0xC0 && (s[1] & 0xC0) == 0x80) { *ps += 2; return ((c & 0x1F) << 6) | (s[1] & 0x3F); }
    if ((c & 0xF0) == 0xE0 && (s[1] & 0xC0) == 0x80 && (s[2] & 0xC0) == 0x80) { *ps += 3; return ((c & 0x0F) << 12) | ((s[1] & 0x3F) << 6) | (s[2] & 0x3F); }
    if ((c & 0xF8) == 0xF0 && (s[1] & 0xC0) == 0x80 && (s[2] & 0xC0) == 0x80 && (s[3] & 0xC0) == 0x80) { *ps += 4; return '?'; }
    *ps += 1;
    return '?';
}

static const HrGlyph *hr_find(const HrFace *f, int cp)
{
    int i;
    for (i = 0; i < f->n; i++) if (f->g[i].cp == cp) return &f->g[i];
    return NULL;
}

/* glifo para cp; si la cara no lo trae prueba la mayuscula y luego '?' */
static const HrGlyph *hr_glyph(const HrFace *f, int cp)
{
    const HrGlyph *g = hr_find(f, cp);
    if (g) return g;
    if ((cp >= 'a' && cp <= 'z') || (cp >= 0xE0 && cp <= 0xFE && cp != 0xF7)) { g = hr_find(f, cp - 32); if (g) return g; }
    if (cp == '_') { g = hr_find(f, '-'); if (g) return g; }
    if (cp == '[') { g = hr_find(f, '('); if (g) return g; }
    if (cp == ']') { g = hr_find(f, ')'); if (g) return g; }
    return hr_find(f, '?');
}

static int hr_tw(int face, const char *s, int sp)
{
    const HrFace *f = &g_hf[face];
    int w = 0, cnt = 0, cp;
    while ((cp = hr_u8next(&s)) != 0) {
        const HrGlyph *g = hr_glyph(f, cp);
        w += (g ? g->adv : 6) + sp;
        cnt++;
    }
    return cnt ? w - sp : 0;
}

/* anc: [0] = 'l' izquierda, 'c' centro, 'r' derecha; [1] = 'm' (y = linea media del texto) o 't' (y = tope: linea del ascendente) */
static void hr_text(int face, int x, int y, const char *s, uint32_t col, const char *anc, int sp)
{
    const HrFace *f = &g_hf[face];
    int base, cp;
    if (anc[0] == 'c') x -= hr_tw(face, s, sp) / 2;
    else if (anc[0] == 'r') x -= hr_tw(face, s, sp);
    base = anc[1] == 't' ? y + f->asc : y + f->mid;
    while ((cp = hr_u8next(&s)) != 0) {
        const HrGlyph *g = hr_glyph(f, cp);
        if (!g) { x += 6 + sp; continue; }
        if (g->w && g->h) {
            const uint8_t *bm = f->bm + g->off;
            int gx = x + g->xo, gy = base + g->yo, r, cc;
            for (r = 0; r < g->h; r++) {
                int py = gy + r;
                if (py < 0 || py >= HR_H) continue;
                for (cc = 0; cc < g->w; cc++) {
                    int px = gx + cc, i = r * g->w + cc, nib, a;
                    if (px < 0 || px >= HR_W) continue;
                    nib = (i & 1) ? (bm[i >> 1] & 15) : (bm[i >> 1] >> 4);
                    if (!nib) continue;
                    a = nib * 17;
                    g_hr[py * HR_W + px] = hr_mix(g_hr[py * HR_W + px], col, a);
                }
            }
        }
        x += g->adv + sp;
    }
}

/* Copia src en dst acortando con "..." para que quepa en maxw pixeles con la cara 'face' */
static void hr_fit(int face, const char *src, int maxw, char *dst, size_t cap)
{
    size_t n = strlen(src), k;
    if (cap == 0) return;
    if (n >= cap) n = cap - 1;
    memcpy(dst, src, n); dst[n] = 0;
    if (hr_tw(face, dst, 0) <= maxw) return;
    k = n;
    while (k > 0) {
        k--;
        while (k > 0 && (((unsigned char)dst[k]) & 0xC0) == 0x80) k--;       /* no cortar en medio de un caracter UTF-8 */
        if (k + 4 > cap) continue;
        memcpy(dst, src, k);
        memcpy(dst + k, "...", 4);
        if (hr_tw(face, dst, 0) <= maxw) return;
    }
    snprintf(dst, cap, "...");
}

/* Reparte texto en lineas de hasta maxw pixeles (por palabras). Devuelve cuantas lineas escribio en out[i] (cap caracteres cada una). */
static int hr_wrap(int face, const char *src, int maxw, char out[][64], int maxlines)
{
    int nl = 0;
    char cur[64];
    const char *p = src;
    cur[0] = 0;
    while (*p && nl < maxlines) {
        char word[48];
        int wl = 0;
        char trial[128];
        while (*p == ' ') p++;
        while (*p && *p != ' ' && wl < (int)sizeof word - 1) word[wl++] = *p++;
        word[wl] = 0;
        if (!wl) break;
        if (cur[0]) snprintf(trial, sizeof trial, "%s %s", cur, word); else snprintf(trial, sizeof trial, "%s", word);
        if (hr_tw(face, trial, 0) <= maxw || !cur[0]) snprintf(cur, sizeof cur, "%s", trial);
        else { snprintf(out[nl++], 64, "%s", cur); snprintf(cur, sizeof cur, "%s", word); }
    }
    if (cur[0] && nl < maxlines) snprintf(out[nl++], 64, "%s", cur);
    return nl;
}

/* ---- fondo: cielo (160x90 ampliado), estrellas y montanas ---- */
static uint32_t hr_rng(uint32_t *s) { *s = *s * 1664525u + 1013904223u; return *s >> 8; }

static void hr_ridge(uint32_t *buf, int y0, int amp, uint32_t col, uint32_t seed)
{
    uint32_t s = seed;
    int px = 0, py = y0 - (int)(hr_rng(&s) % (uint32_t)(amp + 1));
    while (px < HR_W) {
        int nx = px + 40 + (int)(hr_rng(&s) % 51u), ny = y0 - (int)(hr_rng(&s) % (uint32_t)(amp + 1)), x;
        for (x = px; x < nx && x < HR_W; x++) {
            int yy = py + (ny - py) * (x - px) / (nx - px), y;
            if (yy < 0) yy = 0;
            for (y = yy; y < HR_H; y++) buf[y * HR_W + x] = col;
        }
        px = nx; py = ny;
    }
}

static int hr_build_sky(void)
{
    size_t cap = hr_b64_len(hr_sky_b64), n;
    uint8_t *lo = (uint8_t *)malloc(cap);
    static int xi[HR_W], xf[HR_W];
    int x, y, i;
    uint32_t seed = 11;
    if (!lo) return 0;
    n = hr_b64_decode(hr_sky_b64, lo, cap);
    if (n < 160 * 90 * 3) { free(lo); return 0; }
    for (x = 0; x < HR_W; x++) {
        float sx = ((float)x + 0.5f) * 160.0f / (float)HR_W - 0.5f;
        if (sx < 0.0f) sx = 0.0f;
        xi[x] = (int)sx; if (xi[x] > 158) xi[x] = 158;
        xf[x] = (int)((sx - (float)xi[x]) * 256.0f); if (xf[x] > 256) xf[x] = 256;
    }
    for (y = 0; y < HR_H; y++) {
        float sy = ((float)y + 0.5f) * 90.0f / (float)HR_H - 0.5f;
        int iy, fy;
        const uint8_t *r0, *r1;
        if (sy < 0.0f) sy = 0.0f;
        iy = (int)sy; if (iy > 88) iy = 88;
        fy = (int)((sy - (float)iy) * 256.0f); if (fy > 256) fy = 256;
        r0 = lo + (size_t)iy * 160 * 3; r1 = r0 + 160 * 3;
        for (x = 0; x < HR_W; x++) {
            int c, v[3];
            for (c = 0; c < 3; c++) {
                int a = r0[xi[x] * 3 + c] * (256 - xf[x]) + r0[(xi[x] + 1) * 3 + c] * xf[x];
                int b = r1[xi[x] * 3 + c] * (256 - xf[x]) + r1[(xi[x] + 1) * 3 + c] * xf[x];
                v[c] = (a * (256 - fy) + b * fy + 32768) >> 16;
                if (v[c] > 255) v[c] = 255;
            }
            g_hr_sky[y * HR_W + x] = 0xFF000000u | ((uint32_t)v[0] << 16) | ((uint32_t)v[1] << 8) | (uint32_t)v[2];
        }
    }
    free(lo);
    for (i = 0; i < 220; i++) {
        int sx = (int)(hr_rng(&seed) % HR_W), sy = (int)(hr_rng(&seed) % 504), b = 100 + (int)(hr_rng(&seed) % 156);
        g_hr_sky[sy * HR_W + sx] = 0xFF000000u | ((uint32_t)b << 16) | ((uint32_t)b << 8) | 255u;
        if (hr_rng(&seed) % 100 < 6) {
            int k;
            for (k = -3; k <= 3; k++) {
                if (sx + k >= 0 && sx + k < HR_W) g_hr_sky[sy * HR_W + sx + k] = 0xFFD2E1FFu;
                if (sy + k >= 0 && sy + k < HR_H) g_hr_sky[(sy + k) * HR_W + sx] = 0xFFD2E1FFu;
            }
        }
    }
    hr_ridge(g_hr_sky, 640, 50, 0xFF0E1A3Cu, 1u);
    hr_ridge(g_hr_sky, 672, 36, 0xFF060A1Eu, 2u);
    return 1;
}

/* Prepara fuentes y fondo la primera vez. 1 = listo. Si falla, nunca se vuelve a intentar (se usa el dibujo viejo). */
static int hr_prepare(void)
{
    if (g_hr_ready) return 1;
    if (g_hr_fail) return 0;
    if (!hr_load_faces() || !hr_build_sky()) { g_hr_fail = 1; logf_("AVISO: no pude preparar los menus a 1280x720: uso el dibujo de siempre"); return 0; }
    g_hr_ready = 1;
    logf_("menus 1280x720: fuentes y fondo listos");
    return 1;
}

static int hr_platform_ok(void);          /* PS3: render por CPU y pantalla >= 640x360; PC: siempre */
static int hr_usable(void) { return hr_platform_ok() && hr_prepare(); }

static void hr_begin(void)
{
    memcpy(g_hr, g_hr_sky, sizeof g_hr);
    g_hr_on = 1;
}

/* Copia g_hr al buffer de pantalla (dw x dh). A 1280x720 es una copia directa; con otra resolucion se escala sin deformar. */
static void hr_blit_display(uint32_t *dst, int dw, int dh) __attribute__((unused));
static void hr_blit_display(uint32_t *dst, int dw, int dh)
{
    int y;
    if (dw == HR_W && dh == HR_H) { memcpy(dst, g_hr, sizeof g_hr); return; }
    {
        int oh = dh, ow = dh * 16 / 9, ox, x;
        static int cm[2048];
        if (ow > dw) { ow = dw; oh = dw * 9 / 16; }
        if (ow > 2048) ow = 2048;
        ox = (dw - ow) / 2;
        memset(dst, 0, (size_t)dw * (size_t)dh * 4);
        for (x = 0; x < ow; x++) cm[x] = x * HR_W / ow;
        for (y = 0; y < oh; y++) {
            const uint32_t *src = &g_hr[(y * HR_H / oh) * HR_W];
            uint32_t *d = dst + (size_t)(y + (dh - oh) / 2) * dw + ox;
            for (x = 0; x < ow; x++) d[x] = src[cm[x]];
        }
    }
}

/* ---- elementos de interfaz ---- */
static void hr_glow(int x, int y, int w, int h, uint32_t col)
{
    int k;
    for (k = 22; k >= 1; k--) {
        int a = 72 * (22 - k) * (22 - k) / (22 * 22);
        hr_rect_a(x - k, y - k, w + 2 * k, 1, col, a);                 /* arriba */
        hr_rect_a(x - k, y + h + k - 1, w + 2 * k, 1, col, a);         /* abajo */
        hr_rect_a(x - k, y - k + 1, 1, h + 2 * k - 2, col, a);         /* izquierda */
        hr_rect_a(x + w + k - 1, y - k + 1, 1, h + 2 * k - 2, col, a); /* derecha */
    }
}

/* tarjeta con dos esquinas cortadas (arriba a la izquierda y abajo a la derecha) */
static void hr_card(int x, int y, int w, int h, int c, int sel)
{
    uint32_t fill = sel ? HC_SEL : HC_CARD, line = sel ? HC_CY : HC_LINE;
    int lw = sel ? 3 : 2, dy;
    if (sel) {
        hr_glow(x, y, w, h, HC_CY);
        for (dy = 0; dy < c; dy++) {                      /* las esquinas cortadas tambien reciben el brillo */
            hr_rect_a(x, y + dy, c - dy, 1, HC_CY, 46);
            hr_rect_a(x + w - (c - dy) + 0, y + h - dy, c - dy, 1, HC_CY, 46);
        }
    }
    for (dy = 0; dy < h; dy++) {
        int xl = x + (dy < c ? c - dy : 0), xr = x + w - (dy > h - c ? dy - (h - c) : 0);
        hr_rect(xl, y + dy, xr - xl, 1, fill);
    }
    hr_line(x + c, y, x + w, y, lw, line);
    hr_line(x + w, y, x + w, y + h - c, lw, line);
    hr_line(x + w, y + h - c, x + w - c, y + h, lw, line);
    hr_line(x + w - c, y + h, x, y + h, lw, line);
    hr_line(x, y + h, x, y + c, lw, line);
    hr_line(x, y + c, x + c, y, lw, line);
}

typedef struct { int kind; const char *label; } HrBtn;     /* kind: 0 = X (azul), 1 = O (rojo), 2 = START */

static void hr_btns(const HrBtn *b, int n, const char *hint)
{
    int i, x = 140;
    for (i = 0; i < n; i++) {
        int tx;
        if (b[i].kind == 2) {
            hr_rr_fill(x - 12, 660, x + 54, 692, 16, 0xFFFFFFFFu);
            hr_rr_fill(x - 10, 662, x + 52, 690, 14, 0xFF3C4678u);
            hr_text(HF_OM13, x + 21, 676, "START", HC_WHITE, "cm", 0);
            tx = x + 68;
        } else {
            hr_disc(x, 676, 17, HC_WHITE);
            hr_disc(x, 676, 15, b[i].kind == 0 ? HC_BX : HC_BO);
            if (b[i].kind == 0) { hr_line(x - 6, 670, x + 6, 682, 3, HC_WHITE); hr_line(x - 6, 682, x + 6, 670, 3, HC_WHITE); }   /* X */
            else hr_ring(x, 676, 8, 3, HC_WHITE);                                                                              /* O redonda */
            tx = x + 28;
        }
        hr_text(HF_OM16, tx, 676, b[i].label, HC_SIL, "lm", 0);
        x = tx + hr_tw(HF_OM16, b[i].label, 0) + 70;
    }
    if (hint && hint[0]) hr_text(HF_MS13, x, 676, hint, HC_DIM, "lm", 0);
    hr_text(HF_OM14, 1160, 676, "V0.3.2", HC_DIM, "rm", 0);
}

/* encabezado de las pantallas internas: titulo grande con subrayado celeste, subtitulo y marca arriba a la derecha */
static void hr_head(const char *title, const char *sub)
{
    int tw = hr_tw(HF_H1, title, 0);
    hr_text(HF_H1, 120, 64, title, HC_SIL, "lm", 0);
    hr_line(120, 98, 120 + tw, 98, 3, HC_CY);
    if (sub && sub[0]) hr_text(HF_MS15, 120, 122, sub, HC_DIM, "lm", 0);
    hr_text(HF_OB19, 1160, 64, "SILVERSKY", HC_SIL, "rm", 0);
}

/* logo centrado SILVER + SKY con las dos rayas celestes */
static void hr_logo(int ytop)
{
    int w = hr_tw(HF_LOGO, "SILVERSKY", 7), x0 = 640 - w / 2, x = x0, i;
    const char *p = "SILVERSKY";
    char ch[2];
    ch[1] = 0;
    for (i = 0; p[i]; i++) {
        ch[0] = p[i];
        hr_text(HF_LOGO, x, ytop, ch, i < 6 ? HC_SIL : HC_CY, "lt", 0);
        x += hr_tw(HF_LOGO, ch, 0) + 7;
    }
    hr_line(x0 - 60, ytop + 40, x0 - 10, ytop + 40, 2, HC_CY);
    hr_line(x0 + w + 10, ytop + 40, x0 + w + 60, ytop + 40, 2, HC_CY);
}

/* iconos de las tarjetas del menu principal */
enum { HI_CART, HI_PLUS, HI_LINK, HI_PAD, HI_FOUR, HI_GEAR };
static void hr_icon(int kind, int cx, int cy, uint32_t c)
{
    int k;
    switch (kind) {
    case HI_CART:
        hr_rr_out(cx - 26, cy - 30, cx + 26, cy + 30, 8, 4, c);
        hr_rr_out(cx - 16, cy - 20, cx + 16, cy + 2, 0, 3, c);
        hr_rect(cx - 14, cy + 14, 29, 9, c);
        break;
    case HI_PLUS:
        hr_ring(cx, cy, 30, 4, c);
        hr_line(cx - 14, cy, cx + 14, cy, 4, c);
        hr_line(cx, cy - 14, cx, cy + 14, 4, c);
        break;
    case HI_LINK:
        hr_rr_out(cx - 34, cy - 14, cx + 6, cy + 14, 14, 4, c);
        hr_rr_out(cx - 6, cy - 14, cx + 34, cy + 14, 14, 4, c);
        break;
    case HI_PAD:
        hr_rr_out(cx - 34, cy - 18, cx + 34, cy + 20, 16, 4, c);
        hr_line(cx - 20, cy, cx - 8, cy, 4, c);
        hr_line(cx - 14, cy - 6, cx - 14, cy + 6, 4, c);
        hr_disc(cx + 12, cy, 4, c);
        hr_disc(cx + 24, cy - 6, 4, c);
        break;
    case HI_FOUR:
        hr_ring(cx - 18, cy - 18, 9, 4, c); hr_ring(cx + 18, cy - 18, 9, 4, c);
        hr_ring(cx - 18, cy + 18, 9, 4, c); hr_ring(cx + 18, cy + 18, 9, 4, c);
        break;
    default:
        hr_ring(cx, cy, 14, 4, c);
        for (k = 0; k < 8; k++) {
            static const int dxs[8] = { 10, 7, 0, -7, -10, -7, 0, 7 }, dys[8] = { 0, 7, 10, 7, 0, -7, -10, -7 };
            hr_line(cx + dxs[k] * 22 / 10, cy + dys[k] * 22 / 10, cx + dxs[k] * 32 / 10, cy + dys[k] * 32 / 10, 6, c);
        }
        hr_ring(cx, cy, 24, 4, c);
        break;
    }
}

/* ------------------------------------------------------------------ */
/* Plataforma: video, mando                                            */
/* ------------------------------------------------------------------ */
/* ------------------------------------------------------------------ */
/* Audio (v1.5)                                                        */
/* El nucleo entrega PCM de 16 bits estereo. Se re-muestrea a 48 kHz con un ajuste fino de   */
/* velocidad (maximo +-1 %) para seguir el reloj de la consola, y se escribe en el anillo de */
/* bloques de libaudio. Ninguna espera es bloqueante: si algo falla, el juego sigue sin sonido. */
/* ------------------------------------------------------------------ */
#define AU_BLK       256            /* muestras por bloque (AUDIO_BLOCK_SAMPLES) */
#define AU_NBLK      32             /* bloques del anillo (AUDIO_BLOCK_32, ~170 ms) */
#define AU_TARGET    8              /* bloques por delante que intento mantener (~43 ms) */
#define AU_PRIME     6              /* tras un corte, relleno con silencio hasta este nivel */
#define AU_URGENT    2              /* si no hay audio, mantengo al menos esto con silencio */
#define AU_QCAP      8192           /* cola de entrada (cuadros estereo) */
#define AU_OUT_RATE  48000.0
#define AU_FILL_T    (AU_TARGET * AU_BLK + 800.0)

static int      g_au_on;                    /* 1 = audio activo */
static double   g_au_inrate = 48000.0;      /* frecuencia que entrega el nucleo */
static int16_t  g_aq[AU_QCAP * 2];
static unsigned g_aq_head, g_aq_cnt;        /* cola circular de entrada (cuadros) */
static double   g_aq_pos;                   /* posicion fraccionaria respecto a head */
static float    g_au_ll, g_au_lr;           /* ultima muestra emitida (para el fundido a silencio) */
static int      g_au_queued;                /* bloques escritos por delante de la lectura */
static int      g_au_reprime;
static uint32_t g_au_lastrd, g_au_lastpush, g_au_lastpump, g_au_logt;
static uint32_t g_au_blocks, g_au_under, g_au_drop;
static double   g_au_step_s = 1.0;          /* paso suavizado */

#ifdef NESNET_PS3
static u32  g_au_port;
static audioPortConfig g_au_cfg;
static sys_event_queue_t g_au_q;
static sys_ipc_key_t g_au_key;
static int  g_au_init, g_au_portok, g_au_qok, g_au_started;

static uint32_t au_hw_readidx(void) { return (uint32_t)(*(volatile u64 *)(uintptr_t)g_au_cfg.readIndex); }
static float *au_hw_block(uint32_t i) { return (float *)(uintptr_t)g_au_cfg.audioDataStart + (size_t)i * AU_BLK * 2; }
static void au_hw_poll(void) { if (g_au_qok) sysEventQueueDrain(g_au_q); }

static void au_close(void)
{
    g_au_on = 0;
    if (g_au_started) { audioPortStop(g_au_port); g_au_started = 0; }
    if (g_au_qok) { audioRemoveNotifyEventQueue(g_au_key); sysEventQueueDestroy(g_au_q, 0); g_au_qok = 0; }
    if (g_au_portok) { audioPortClose(g_au_port); g_au_portok = 0; }
    if (g_au_init) { audioQuit(); g_au_init = 0; }
}
#else
static uint32_t au_hw_readidx(void) { return 0; }
static float *au_hw_block(uint32_t i) { static float b[AU_BLK * 2]; (void)i; return b; }
static void au_hw_poll(void) {}
static void au_close(void) {}
#endif

/* AUDIO-GENERIC-BEGIN */
static int      g_volume = 100;        /* v1.9: volumen 0..100 (100 = igual que siempre) */
static void au_reset(void)
{
    g_aq_head = 0; g_aq_cnt = 0; g_aq_pos = 0.0;
}

/* Recibe PCM del nucleo (se llama desde retro_run) */
static void au_push(const int16_t *d, size_t frames)
{
    size_t i;
    if (!g_au_on || !frames) return;
    g_au_lastpush = now_ms();
    if (frames > AU_QCAP) { d += (frames - AU_QCAP) * 2; frames = AU_QCAP; }
    if (g_aq_cnt + frames > AU_QCAP) {              /* la cola se llena: descarto lo mas viejo */
        unsigned over = (unsigned)(g_aq_cnt + frames - AU_QCAP);
        if (over > g_aq_cnt) over = g_aq_cnt;
        g_aq_head = (g_aq_head + over) % AU_QCAP;
        g_aq_cnt -= over;
        g_aq_pos -= (double)over;
        if (g_aq_pos < 0.0) g_aq_pos = 0.0;
        g_au_drop++;
    }
    for (i = 0; i < frames; i++) {
        unsigned w = (g_aq_head + g_aq_cnt) % AU_QCAP;
        if (g_volume >= 100) {                      /* volumen normal: las muestras pasan sin tocarse (igual que antes) */
            g_aq[w * 2]     = d[i * 2];
            g_aq[w * 2 + 1] = d[i * 2 + 1];
        } else {                                    /* v1.9: volumen bajado desde OPCIONES > SONIDO */
            g_aq[w * 2]     = (int16_t)((int)d[i * 2]     * g_volume / 100);
            g_aq[w * 2 + 1] = (int16_t)((int)d[i * 2 + 1] * g_volume / 100);
        }
        g_aq_cnt++;
    }
}

/* Paso de lectura de la entrada por cada muestra de salida: nominal +- 1 %, segun cuanto audio
 * hay acumulado (en la cola de salida + en la de entrada) respecto al objetivo. */
static double au_calc_step(void)
{
    double base = g_au_inrate / AU_OUT_RATE;
    double fill = (double)g_au_queued * AU_BLK + (double)g_aq_cnt / base;
    double e = (fill - AU_FILL_T) / AU_FILL_T;
    double s;
    if (e > 1.0) e = 1.0; else if (e < -1.0) e = -1.0;
    s = base * (1.0 + 0.01 * e);
    g_au_step_s += 0.05 * (s - g_au_step_s);
    if (g_au_step_s > base * 1.01) g_au_step_s = base * 1.01;
    if (g_au_step_s < base * 0.99) g_au_step_s = base * 0.99;
    return g_au_step_s;
}

static void au_silence_block(float *o)
{
    int i;
    for (i = 0; i < AU_BLK; i++) {
        g_au_ll *= 0.995f; g_au_lr *= 0.995f;
        if (g_au_ll > -1e-6f && g_au_ll < 1e-6f) g_au_ll = 0.0f;
        if (g_au_lr > -1e-6f && g_au_lr < 1e-6f) g_au_lr = 0.0f;
        o[i * 2] = g_au_ll; o[i * 2 + 1] = g_au_lr;
    }
}

/* Un bloque real: interpolacion lineal entre muestras de entrada. El que llama garantiza que
 * hay suficiente entrada (au_need). */
static int au_need(double step) { return (int)(g_aq_pos + AU_BLK * step) + 2; }

static void au_real_block(float *o, double step)
{
    int i, n;
    for (i = 0; i < AU_BLK; i++) {
        int k = (int)g_aq_pos;
        double fr = g_aq_pos - (double)k;
        unsigned a = (g_aq_head + (unsigned)k) % AU_QCAP, b = (g_aq_head + (unsigned)k + 1) % AU_QCAP;
        double l = (double)g_aq[a * 2]     + ((double)g_aq[b * 2]     - (double)g_aq[a * 2])     * fr;
        double r = (double)g_aq[a * 2 + 1] + ((double)g_aq[b * 2 + 1] - (double)g_aq[a * 2 + 1]) * fr;
        g_au_ll = (float)(l / 32768.0); g_au_lr = (float)(r / 32768.0);
        o[i * 2] = g_au_ll; o[i * 2 + 1] = g_au_lr;
        g_aq_pos += step;
    }
    n = (int)g_aq_pos;
    if (n > (int)g_aq_cnt) n = (int)g_aq_cnt;
    g_aq_head = (g_aq_head + (unsigned)n) % AU_QCAP;
    g_aq_cnt -= (unsigned)n;
    g_aq_pos -= (double)n;
    if (g_aq_pos < 0.0) g_aq_pos = 0.0;
}

/* Se llama muy seguido (desde pump()): repone bloques en el anillo segun avance el reloj de audio */
static void au_pump(void)
{
    uint32_t rd, now;
    int d, idle, guard = 0;
    double step;
    if (!g_au_on) return;
    now = now_ms();
    idle = (uint32_t)(now - g_au_lastpush) > 500;
    au_hw_poll();
    if (g_au_lastpump && (uint32_t)(now - g_au_lastpump) > 120) {
        /* el programa estuvo detenido: el anillo pudo dar la vuelta; lo dejo en silencio y empiezo de nuevo */
        int j;
        for (j = 0; j < AU_NBLK; j++) memset(au_hw_block((uint32_t)j), 0, AU_BLK * 2 * sizeof(float));
        g_au_queued = 0; g_au_reprime = 1;
        g_au_lastrd = au_hw_readidx() % AU_NBLK;
        if (!idle) g_au_under++;
    }
    g_au_lastpump = now;
    rd = au_hw_readidx() % AU_NBLK;
    d = (int)((rd + AU_NBLK - g_au_lastrd) % AU_NBLK);
    if (d > 0) {
        int j;
        for (j = 0; j < d; j++) memset(au_hw_block((g_au_lastrd + (uint32_t)j) % AU_NBLK), 0, AU_BLK * 2 * sizeof(float));
        if (d > g_au_queued) { if (!idle) { g_au_under++; g_au_reprime = 1; } g_au_queued = 0; }
        else g_au_queued -= d;
        g_au_lastrd = rd;
    }
    step = au_calc_step();
    while (g_au_queued < AU_TARGET && guard++ < AU_NBLK) {
        float *o = au_hw_block((rd + 1 + (uint32_t)g_au_queued) % AU_NBLK);
        if (g_au_reprime && g_au_queued < AU_PRIME) {
            au_silence_block(o);
            if (g_au_queued + 1 >= AU_PRIME) g_au_reprime = 0;
        } else if ((int)g_aq_cnt >= au_need(step)) {
            au_real_block(o, step);
            g_au_blocks++;
        } else if (g_au_queued < AU_URGENT) {
            au_silence_block(o);
        } else break;
        g_au_queued++;
    }
    if (!idle && (uint32_t)(now - g_au_logt) >= 2000) {
        g_au_logt = now;
        logf_("audio: bloques=%u cortes=%u descartes=%u cola=%d entrada=%u paso=%d/10000",
              (unsigned)g_au_blocks, (unsigned)g_au_under, (unsigned)g_au_drop,
              g_au_queued, (unsigned)g_aq_cnt, (int)(step * 10000.0));
    }
}
/* AUDIO-GENERIC-END */

#ifdef NESNET_PS3
static void au_open(void)
{
    audioPortParam pr;
    s32 r;
    g_au_on = 0;
    if (!g_cfg.audio) { logf_("audio: apagado (audio=off o R2 al abrir)"); return; }
    logf_("audio: llamando a audioInit...");
    r = audioInit();
    logf_("audio: audioInit=%08x", (unsigned)r);
    if (r != 0) return;
    g_au_init = 1;
    memset(&pr, 0, sizeof pr);
    pr.numChannels = AUDIO_PORT_2CH;
    pr.numBlocks   = AUDIO_BLOCK_32;
    pr.attrib      = AUDIO_PORT_INITLEVEL;
    pr.level       = 1.0f;
    logf_("audio: llamando a audioPortOpen...");
    r = audioPortOpen(&pr, &g_au_port);
    logf_("audio: audioPortOpen=%08x puerto=%u", (unsigned)r, (unsigned)g_au_port);
    if (r != 0) { au_close(); return; }
    g_au_portok = 1;
    r = audioGetPortConfig(g_au_port, &g_au_cfg);
    logf_("audio: config=%08x bloques=%u canales=%u indice=%08x datos=%08x", (unsigned)r,
          (unsigned)g_au_cfg.numBlocks, (unsigned)g_au_cfg.channelCount,
          (unsigned)g_au_cfg.readIndex, (unsigned)g_au_cfg.audioDataStart);
    if (r != 0 || g_au_cfg.numBlocks != AU_NBLK || g_au_cfg.channelCount != 2 ||
        !g_au_cfg.readIndex || !g_au_cfg.audioDataStart) {
        logf_("AVISO: el puerto de audio no tiene el formato esperado; sigo sin sonido");
        au_close(); return;
    }
    r = audioCreateNotifyEventQueue(&g_au_q, &g_au_key);
    logf_("audio: cola de eventos=%08x", (unsigned)r);
    if (r == 0) {
        g_au_qok = 1;
        r = audioSetNotifyEventQueue(g_au_key);
        logf_("audio: audioSetNotifyEventQueue=%08x", (unsigned)r);
        sysEventQueueDrain(g_au_q);
    } else {
        logf_("AVISO: sin cola de eventos de audio; sigo leyendo el indice directamente");
    }
    { int i; for (i = 0; i < AU_NBLK; i++) memset(au_hw_block((uint32_t)i), 0, AU_BLK * 2 * sizeof(float)); }
    g_au_lastrd = au_hw_readidx() % AU_NBLK;
    g_au_queued = 0; g_au_reprime = 1; g_au_lastpush = 0; g_au_lastpump = 0;
    logf_("audio: llamando a audioPortStart...");
    r = audioPortStart(g_au_port);
    logf_("audio: audioPortStart=%08x", (unsigned)r);
    if (r != 0) { au_close(); return; }
    g_au_started = 1;
    g_au_on = 1;
    logf_("audio: listo (anillo de %d bloques)", AU_NBLK);
}
#else
static void au_open(void) {}
#endif

/* v1.8.1: palanca izquierda como cruz. Los ejes van de 0 a 255 con el centro cerca de 128. La zona muerta es
 * amplia (50 de 128) para que un stick flojo o con deriva no mande movimientos sueltos. Funcion pura: se
 * puede probar en PC. Devuelve -1 (izq/arriba), 0 (centro) o +1 (der/abajo) para cada eje. */
#define STICK_DEAD 50
static int stick_axis(unsigned v)
{
    if (v < 128u - STICK_DEAD) return -1;
    if (v > 128u + STICK_DEAD) return 1;
    return 0;
}
static uint16_t stick_nes_bits(unsigned h, unsigned v)
{
    uint16_t b = 0;
    int ax = stick_axis(h), ay = stick_axis(v);
    if (ax < 0) b |= NB_LEFT;
    if (ax > 0) b |= NB_RIGHT;
    if (ay < 0) b |= NB_UP;
    if (ay > 0) b |= NB_DOWN;
    return b;
}

/* ------------------------------------------------------------------ */
/* v1.8.2: OPCIONES - mapeo de botones, turbo y pantalla               */
/* Todo esto es LOCAL. Por la red sigue viajando el estado de los botones del NES (el mensaje no cambia),   */
/* asi que el mapeo de cada jugador no hace falta enviarlo: cada consola traduce sus propios botones antes. */
/* Las funciones de esta seccion son puras (no tocan la PS3), asi que se prueban tal cual en PC.             */
/* ------------------------------------------------------------------ */
enum { PB_CROSS, PB_CIRCLE, PB_SQUARE, PB_TRIANGLE, PB_L1, PB_R1, PB_L2, PB_R2, PB_L3, PB_R3, PB_START, PB_SELECT, PB_COUNT };
#define PB_BIT(b) (1u << (b))

static int      g_screen;              /* 0 = original (pixeles cuadrados), 1 = 4:3 real, 2 = 16:9 estirada */
/* v0.2.6: la opcion de pantalla (g_screen) es solo para la imagen del JUEGO. Todos los menus y avisos (todo lo que se dibuja
 * fuera de una partida) se muestran siempre con MENU_SCREEN, asi no cambian de tamano al mover ORIGINAL / 4:3 / 16:9.
 * g_ingame = 1 solo mientras corre session_loop (el menu de R2 sobre la imagen del juego cuenta como juego). */
#define MENU_SCREEN 2                  /* 2 = 16:9 a pantalla completa (1 = 4:3 centrado, 0 = original) */
static int      g_ingame;
static int      g_netinfo;             /* info de red en partida: 0 = solo al inicio, 1 = siempre, 2 = no */
static char     g_last_rom[ROM_NAMELEN];   /* nombre del archivo de la ultima ROM elegida */
static char     g_last_code[16];           /* v0.2.5.1: ultimo codigo de sala escrito al UNIRSE (10 digitos, o vacio) */

/* Mapeo fijo (v0.1): X = B, CUADRADO = Y, O = A, TRIANGULO = X, L1/L2 = L, R1 = R, R2 = R (menos en el mando 1, donde R2 queda
 * sin funcion; el menu se abre con R3), SELECT y START. Las direcciones (cruz y palanca) ya vienen calculadas en 'dirs'. */
static uint16_t snes_bits(uint32_t btns, uint16_t dirs, int port)
{
    uint16_t b = (uint16_t)(dirs & (NB_UP | NB_DOWN | NB_LEFT | NB_RIGHT));
    if (btns & PB_BIT(PB_CROSS))    b |= NB_B;
    if (btns & PB_BIT(PB_SQUARE))   b |= NB_Y;
    if (btns & PB_BIT(PB_CIRCLE))   b |= NB_A;
    if (btns & PB_BIT(PB_TRIANGLE)) b |= NB_X;
    if (btns & (PB_BIT(PB_L1) | PB_BIT(PB_L2))) b |= NB_L;
    if (btns & PB_BIT(PB_R1))       b |= NB_R;
    if ((btns & PB_BIT(PB_R2)) && port != 0) b |= NB_R;
    if (btns & PB_BIT(PB_SELECT))   b |= NB_SEL;
    if (btns & PB_BIT(PB_START))    b |= NB_START;
    if ((b & NB_UP) && (b & NB_DOWN))    b &= (uint16_t)~NB_DOWN;
    if ((b & NB_LEFT) && (b & NB_RIGHT)) b &= (uint16_t)~NB_RIGHT;
    return b;
}

/* Pantalla: ancho de salida (en pixeles de la TV) para un alto de salida 'oh'.
 *   0 original  = SCR_W * z  (pixeles cuadrados, 768x720 en 720p: lo de siempre)
 *   1 4:3 real  = oh * 4 / 3 (960x720 en 720p: columnas repetidas 3 o 4 veces, el 3,75 no es entero)
 *   2 16:9      = oh * 16 / 9 (1280x720 en 720p: cada columna x5 y cada fila x3, todo entero) */
#define COLMAP_MAX 2048
static const char *const screen_names[3] = { "ORIGINAL", "4:3 REAL", "16:9 ESTIRADA" };
static int screen_out_w(int mode, int dw, int oh, int z)
{
    int w;
    if (mode == 1) w = oh * 4 / 3;
    else if (mode == 2) w = oh * 16 / 9;
    else w = SCR_W * z;
    if (w > dw) w = dw;
    if (w > COLMAP_MAX) w = COLMAP_MAX;
    return w;
}

/* Dibuja el lienzo 256x240 en el buffer de pantalla 'base' (dw x dh, ARGB) centrado, escalado segun 'mode' (vertical entero z).
 * Cada 4 cuadros, DE CADA BUFFER, borra lo que queda fuera de la imagen (residuo del XMB / modo anterior); la imagen se repinta siempre.
 * fcnt = contador de cuadros de ese buffer. Version unica para la PS3 y para las pruebas de PC. */
static void canvas_blit_cpu(uint32_t *base, int dw, int dh, int mode, int z, const uint32_t *fb, unsigned *fcnt)
{
    static uint32_t row[COLMAP_MAX];
    static int cm[COLMAP_MAX];
    static int l_ow = -1;
    int oh = SCR_H * z, ow = screen_out_w(mode, dw, oh, z);
    int ox = (dw - ow) / 2, oy = (dh - oh) / 2, x, y, k;
    uint32_t *dst;
    if (z < 1 || ow < 1 || ox < 0 || oy < 0 || oy + oh > dh) return;
    if (ow != l_ow) { for (x = 0; x < ow; x++) cm[x] = x * SCR_W / ow; l_ow = ow; }
    if (((*fcnt)++ & 3) == 0) {
        int below = dh - oy - oh;
        if (oy > 0) memset(base, 0, (size_t)oy * dw * 4);
        if (below > 0) memset(base + (size_t)(oy + oh) * dw, 0, (size_t)below * dw * 4);
        if (ox > 0) {
            int right = dw - ox - ow;
            for (y = oy; y < oy + oh; y++) {
                memset(base + (size_t)y * dw, 0, (size_t)ox * 4);
                if (right > 0) memset(base + (size_t)y * dw + ox + ow, 0, (size_t)right * 4);
            }
        }
    }
    dst = base + (size_t)oy * dw + ox;
    for (y = 0; y < SCR_H; y++) {
        const uint32_t *src = fb + y * SCR_W;
        for (x = 0; x < ow; x++) row[x] = src[cm[x]];
        for (k = 0; k < z; k++) { memcpy(dst, row, (size_t)ow * 4); dst += dw; }
    }
}

/* Guardado de las opciones: USRDIR/opciones.txt (aparte de config.txt, que el instalador puede reemplazar) */
static void opts_defaults(void)
{
    g_screen = 0;
    g_volume = 100;
    g_netinfo = 0;
    g_last_rom[0] = 0;
    g_last_code[0] = 0;
}

static void opts_save(void)
{
    char path[300], tmp[300];
    FILE *f;
    snprintf(path, sizeof path, "%s/opciones.txt", g_dir);
    snprintf(tmp, sizeof tmp, "%s/opciones.tmp", g_dir);
    f = fopen(tmp, "w");
    if (!f) { logf_("AVISO: no pude guardar opciones.txt"); return; }
    fprintf(f, "# SilverSky - opciones (las cambia el menu OPCIONES)\n");
    fprintf(f, "screen=%d\n", g_screen);
    fprintf(f, "volume=%d\n", g_volume);
    fprintf(f, "netinfo=%d\n", g_netinfo);
    if (g_last_rom[0]) fprintf(f, "rom=%s\n", g_last_rom);
    if (g_last_code[0]) fprintf(f, "code=%s\n", g_last_code);
    fclose(f);
    remove(path);
    if (rename(tmp, path) != 0) logf_("AVISO: no pude renombrar opciones.tmp");
}

static void opts_load(void)
{
    char path[300], line[200];
    FILE *f;
    opts_defaults();
    snprintf(path, sizeof path, "%s/opciones.txt", g_dir);
    f = fopen(path, "r");
    if (!f) { logf_("sin opciones.txt: valores por defecto"); return; }
    while (fgets(line, sizeof line, f)) {
        int v0;
        if (line[0] == '#') continue;
        if (sscanf(line, "screen=%d", &v0) == 1) {
            if (v0 >= 0 && v0 <= 2) g_screen = v0;
        } else if (sscanf(line, "volume=%d", &v0) == 1) {
            if (v0 >= 0 && v0 <= 100) g_volume = v0;
        } else if (sscanf(line, "netinfo=%d", &v0) == 1) {
            if (v0 >= 0 && v0 <= 2) g_netinfo = v0;
        } else if (!strncmp(line, "rom=", 4)) {
            size_t n = strlen(line + 4);
            while (n > 0 && (line[4 + n - 1] == '\n' || line[4 + n - 1] == '\r')) n--;
            if (n > 0 && n < ROM_NAMELEN && !memchr(line + 4, '/', n) && line[4] != '.') { memcpy(g_last_rom, line + 4, n); g_last_rom[n] = 0; }
        } else if (!strncmp(line, "code=", 5)) {
            /* v0.2.5.1: solo se acepta si son exactamente 10 digitos */
            size_t n = strlen(line + 5), k;
            int okc;
            while (n > 0 && (line[5 + n - 1] == '\n' || line[5 + n - 1] == '\r')) n--;
            okc = (n == 10);
            for (k = 0; okc && k < n; k++) if (line[5 + k] < '0' || line[5 + k] > '9') okc = 0;
            if (okc) { memcpy(g_last_code, line + 5, 10); g_last_code[10] = 0; }
        }
    }
    fclose(f);
    logf_("opciones: pantalla=%d volumen=%d info_red=%d", g_screen, g_volume, g_netinfo);
    if (g_last_rom[0]) logf_("opciones: ultima ROM = %s", g_last_rom);
}

#ifdef NESNET_PS3

#define CB_SIZE   0x100000
#define HOST_SIZE (32 * 1024 * 1024)
#define GCM_LABEL_INDEX 255
#define LABEL_TEX0      253          /* 253 y 254: una por textura */

static gcmContextData *g_ctx;
static u32 g_dw, g_dh, g_pitch, g_off[2], g_dpitch, g_doff;
static int hr_platform_ok(void) { return g_cfg.render && g_dw >= 640 && g_dh >= 360; }   /* v0.3.0: menus a 1280x720 solo con render por CPU */
static u32 g_cur, g_first = 1, g_label = 1;
static u32 *g_cbuf[2], *g_dbuf;
static u32 *g_tex[2];
static u32  g_texoff[2];
static int  g_texsel;
static u32  g_texval[2];
static int  g_zoom = 3;
static padData g_pd[2];
static uint16_t g_ui_prev;

static void gpu_wait_finish(void)
{
    rsxSetWriteBackendLabel(g_ctx, GCM_LABEL_INDEX, g_label);
    rsxFlushBuffer(g_ctx);
    {
        int guard = 0;
        while (*(vu32 *)gcmGetLabelAddress(GCM_LABEL_INDEX) != g_label) {
            usleep(30);
            if ((++guard & 0x3FF) == 0) pump();
            if (guard > 100000) { logf_("AVISO: gpu_wait_finish agotó el tiempo (3 s)"); break; }
        }
    }
    ++g_label;
}

static void gpu_wait_idle(void)
{
    rsxSetWriteBackendLabel(g_ctx, GCM_LABEL_INDEX, g_label);
    rsxSetWaitLabel(g_ctx, GCM_LABEL_INDEX, g_label);
    ++g_label;
    gpu_wait_finish();
}

static void gpu_set_target(u32 idx)
{
    gcmSurface sf;
    memset(&sf, 0, sizeof sf);
    sf.colorFormat      = GCM_SURFACE_X8R8G8B8;
    sf.colorTarget      = GCM_SURFACE_TARGET_0;
    sf.colorLocation[0] = GCM_LOCATION_RSX;
    sf.colorOffset[0]   = g_off[idx];
    sf.colorPitch[0]    = g_pitch;
    sf.colorLocation[1] = GCM_LOCATION_RSX;
    sf.colorLocation[2] = GCM_LOCATION_RSX;
    sf.colorLocation[3] = GCM_LOCATION_RSX;
    sf.colorOffset[1]   = 0;
    sf.colorOffset[2]   = 0;
    sf.colorOffset[3]   = 0;
    sf.colorPitch[1]    = 64;
    sf.colorPitch[2]    = 64;
    sf.colorPitch[3]    = 64;
    sf.depthFormat      = GCM_SURFACE_ZETA_Z16;
    sf.depthLocation    = GCM_LOCATION_RSX;
    sf.depthOffset      = g_doff;
    sf.depthPitch       = g_dpitch;
    sf.type             = GCM_SURFACE_TYPE_LINEAR;
    sf.antiAlias        = GCM_SURFACE_CENTER_1;
    sf.width            = g_dw;
    sf.height           = g_dh;
    sf.x                = 0;
    sf.y                = 0;
    rsxSetSurface(g_ctx, &sf);
}

static void gpu_init(void)
{
    videoState state;
    videoConfiguration vconfig;
    videoResolution res;
    void *host_addr = memalign(1024 * 1024, HOST_SIZE);
    int i;

    rsxInit(&g_ctx, CB_SIZE, HOST_SIZE, host_addr);

    videoGetState(0, 0, &state);
    logf_("video: modo de la TV resolucion id=%d", (int)state.displayMode.resolution);
    {
        int rid = (int)state.displayMode.resolution;
        if (g_cfg.res == 720 && rid != VIDEO_RESOLUTION_720) {
            if (videoGetResolutionAvailability(VIDEO_PRIMARY, VIDEO_RESOLUTION_720, VIDEO_ASPECT_AUTO, 0) == 1) {
                rid = VIDEO_RESOLUTION_720;
                logf_("video: forzando 720p (res=720)");
            } else logf_("AVISO: la TV no ofrece 720p, sigo con la resolucion actual");
        }
        videoGetResolution(rid, &res);
        state.displayMode.resolution = (u8)rid;
    }

    memset(&vconfig, 0, sizeof vconfig);
    vconfig.resolution = state.displayMode.resolution;
    vconfig.format     = VIDEO_BUFFER_FORMAT_XRGB;
    vconfig.pitch      = res.width * sizeof(u32);

    gpu_wait_idle();
    videoConfigure(0, &vconfig, NULL, 0);
    videoGetState(0, 0, &state);
    logf_("video: configurado %ux%u", (unsigned)res.width, (unsigned)res.height);

    gcmSetFlipMode(GCM_FLIP_VSYNC);

    g_dw = res.width;
    g_dh = res.height;
    g_pitch = g_dw * sizeof(u32);
    g_cbuf[0] = (u32 *)rsxMemalign(64, g_dh * g_pitch);
    g_cbuf[1] = (u32 *)rsxMemalign(64, g_dh * g_pitch);
    rsxAddressToOffset(g_cbuf[0], &g_off[0]);
    rsxAddressToOffset(g_cbuf[1], &g_off[1]);
    gcmSetDisplayBuffer(0, g_off[0], g_pitch, g_dw, g_dh);
    gcmSetDisplayBuffer(1, g_off[1], g_pitch, g_dw, g_dh);

    g_dpitch = g_dw * sizeof(u32);
    g_dbuf = (u32 *)rsxMemalign(64, (g_dh * g_dpitch) * 2);
    rsxAddressToOffset(g_dbuf, &g_doff);

    for (i = 0; i < 2; i++) {
        g_tex[i] = (u32 *)rsxMemalign(64, SCR_W * SCR_H * 4);
        rsxAddressToOffset(g_tex[i], &g_texoff[i]);
        memset(g_tex[i], 0, SCR_W * SCR_H * 4);
        g_texval[i] = 0;
        *(vu32 *)gcmGetLabelAddress(LABEL_TEX0 + i) = 0;
    }

    g_zoom = (int)(g_dh / SCR_H);
    if (g_cfg.render && g_zoom > 3) g_zoom = 3;      /* escribir a mano en la VRAM es lento: x3 maximo (v1.3; antes x2) */
    if (g_cfg.zoom > 0 && g_cfg.zoom < g_zoom) g_zoom = g_cfg.zoom;
    if (g_zoom < 1) g_zoom = 1;
    if (g_zoom > 4) g_zoom = 4;
    memset(g_cbuf[0], 0, g_dh * g_pitch);
    memset(g_cbuf[1], 0, g_dh * g_pitch);
    logf_("video: zoom x%d  render=%s", g_zoom, g_cfg.render ? "cpu" : "gpu");

    gpu_set_target(g_cur);
}

static void gpu_flip(void)
{
    if (!g_first) {
        int guard = 0;
        unsigned long long pf_a = now_us();
        while (gcmGetFlipStatus() != 0) {
            usleep(200);
            if ((++guard & 0xFF) == 0) pump();
            if (guard > 15000) { logf_("AVISO: el flip no termino en 3 s"); break; }
        }
        pf_wait_cur += now_us() - pf_a;
        gcmResetFlipStatus();
    } else {
        gcmResetFlipStatus();
    }
    gcmSetFlip(g_ctx, g_cur);
    rsxFlushBuffer(g_ctx);
    gcmSetWaitFlip(g_ctx);
    g_cur ^= 1;
    gpu_set_target(g_cur);
    g_first = 0;
}

static void gpu_blit_canvas(void)
{
    gcmTransferScale scale;
    gcmTransferSurface surface;
    int sel = g_texsel;
    float zoom = (float)g_zoom;

    if (g_cfg.render) {
        /* Modo CPU: sin transferencia ni clear ni blend de la GPU; escribo directo en el buffer de pantalla */
        static unsigned cpu_frame[2];     /* un contador por buffer de pantalla (v1.4) */
        if (!g_first) {
            int guard = 0;
            unsigned long long pf_a = now_us();
            while (gcmGetFlipStatus() != 0 && guard++ < 15000) usleep(200);
            pf_wait_cur += now_us() - pf_a;
        }
        g_stage = "cpu-copia";
        /* v1.3: cada 4 cuadros DE CADA BUFFER se limpia lo que queda fuera del juego (bordes) para que no se quede el
         * residuo del XMB (reloj / bateria del mando); el juego mismo se repinta siempre.
         * v1.8.2: el escalado (modo de pantalla elegido en OPCIONES) y esa limpieza viven en canvas_blit_cpu. */
        if (g_hr_on) {                      /* v0.3.0: pantalla de menu a 1280x720 */
            hr_blit_display((uint32_t *)g_cbuf[g_cur], (int)g_dw, (int)g_dh);
            g_hr_on = 0;
            cpu_frame[0] = cpu_frame[1] = 0;   /* el primer cuadro de juego despues limpia los bordes */
            return;
        }
        canvas_blit_cpu((uint32_t *)g_cbuf[g_cur], (int)g_dw, (int)g_dh, g_ingame ? g_screen : MENU_SCREEN, g_zoom, (const uint32_t *)g_fb, &cpu_frame[g_cur & 1]);
        return;
    }

    g_texsel ^= 1;

    /* Esperar a que la GPU termine de leer ESTA textura (la uso cada 2 cuadros) antes de
     * escribirla otra vez; con tope de ~0,5 s para no quedarse esperando para siempre. */
    g_stage = "gpu-espera-textura";
    {
        int guard = 0;
        while (*(vu32 *)gcmGetLabelAddress(LABEL_TEX0 + sel) != g_texval[sel] && guard++ < 16000)
            usleep(30);
        if (guard >= 16000) logf_("AVISO: la GPU no libero la textura %d a tiempo", sel);
    }
    g_stage = "gpu-copia-textura";
    memcpy(g_tex[sel], g_fb, SCR_W * SCR_H * 4);

    rsxSetClearColor(g_ctx, 0x00000000);
    rsxSetClearDepthStencil(g_ctx, 0xffff);
    rsxClearSurface(g_ctx, GCM_CLEAR_R | GCM_CLEAR_G | GCM_CLEAR_B | GCM_CLEAR_A |
                           GCM_CLEAR_S | GCM_CLEAR_Z);

    rsxSetBlendFunc(g_ctx, GCM_SRC_ALPHA, GCM_ONE_MINUS_SRC_ALPHA,
                    GCM_SRC_ALPHA, GCM_ONE_MINUS_SRC_ALPHA);
    rsxSetBlendEquation(g_ctx, GCM_FUNC_ADD, GCM_FUNC_ADD);
    rsxSetBlendEnable(g_ctx, GCM_TRUE);

    memset(&scale, 0, sizeof scale);
    scale.conversion = GCM_TRANSFER_CONVERSION_TRUNCATE;
    scale.format     = GCM_TRANSFER_SCALE_FORMAT_A8R8G8B8;
    scale.origin     = GCM_TRANSFER_ORIGIN_CORNER;
    scale.operation  = GCM_TRANSFER_OPERATION_SRCCOPY_AND;
    scale.interp     = GCM_TRANSFER_INTERPOLATOR_NEAREST;
    scale.clipX = 0;
    scale.clipY = 0;
    scale.clipW = g_dw;
    scale.clipH = g_dh;
    scale.outX  = (g_dw - SCR_W * g_zoom) / 2;
    scale.outY  = (g_dh - SCR_H * g_zoom) / 2;
    scale.outW  = SCR_W * g_zoom;
    scale.outH  = SCR_H * g_zoom;
    scale.ratioX = rsxGetFixedSint32(1.f / zoom);
    scale.ratioY = rsxGetFixedSint32(1.f / zoom);
    scale.inX = rsxGetFixedUint16(0);
    scale.inY = rsxGetFixedUint16(0);
    scale.inW = SCR_W;
    scale.inH = SCR_H;
    scale.offset = g_texoff[sel];
    scale.pitch  = sizeof(u32) * SCR_W;

    surface.format = GCM_TRANSFER_SURFACE_FORMAT_A8R8G8B8;
    surface.pitch  = g_pitch;
    surface.offset = g_off[g_cur];

    g_stage = "gpu-encolar-blit";
    rsxSetTransferScaleMode(g_ctx, GCM_TRANSFER_LOCAL_TO_LOCAL, GCM_TRANSFER_SURFACE);
    rsxSetTransferScaleSurface(g_ctx, &scale, &surface);

    /* la GPU escribe esta marca cuando termine el blit de esta textura */
    g_texval[sel]++;
    rsxSetWriteBackendLabel(g_ctx, LABEL_TEX0 + sel, g_texval[sel]);
}

static void present(void)
{
    unsigned long long pf_a = now_us();
    gpu_blit_canvas();
    g_stage = "gpu-flip";
    gpu_flip();
    g_stage = "ok";
    heartbeat();
    pf_draw_cur += now_us() - pf_a;       /* incluye la espera del vsync; pf_frame_end la descuenta */
}

static void sysutil_cb(u64 status, u64 param, void *usrdata)
{
    (void)param; (void)usrdata;
    if (status == SYSUTIL_EXIT_GAME) g_running = 0;
}

static void pump(void) { sysUtilCheckCallback(); au_pump(); }

static void exit_cb(void)
{
    sysUtilUnregisterCallback(SYSUTIL_EVENT_SLOT0);
    au_close();
    if (g_ctx) { gcmSetWaitFlip(g_ctx); rsxFinish(g_ctx, 1); }
}

static void platform_init(void)
{
    gpu_init();
    atexit(exit_cb);
    sysUtilRegisterCallback(0, sysutil_cb, NULL);
}

static void net_ensure(void)
{
    static int ready;
    if (!ready) { logf_("iniciando red"); netInitialize(); ready = 1; logf_("red lista"); }
}

/* Lee el mando 'port'; conserva el ultimo estado si no hay cambios */
static padData *pad_read(int port)
{
    padInfo pi;
    padData d;
    ioPadGetInfo(&pi);
    /* v1.9: un mando apagado/desconectado (o sin lectura todavia) debe quedar con las palancas en el CENTRO (128).
     * Con 0 la palanca parecia empujada a la izquierda/arriba y el jugador 2 se movia solo (error de la v1.8.1 en adelante). */
    if (!pi.status[port]) { memset(&g_pd[port], 0, sizeof g_pd[port]); g_pd[port].ANA_L_H = g_pd[port].ANA_L_V = g_pd[port].ANA_R_H = g_pd[port].ANA_R_V = 128; return &g_pd[port]; }
    memset(&d, 0, sizeof d);
    ioPadGetData(port, &d);
    if (d.len > 0) g_pd[port] = d;
    else if (!g_pd[port].ANA_L_H && !g_pd[port].ANA_L_V) g_pd[port].ANA_L_H = g_pd[port].ANA_L_V = g_pd[port].ANA_R_H = g_pd[port].ANA_R_V = 128;   /* aun sin lectura valida */
    return &g_pd[port];
}

/* v1.8.2: botones de la PS3 apretados, como mascara PB_BIT (los que se pueden asignar en OPCIONES) */
static uint32_t pad_buttons(const padData *d)
{
    uint32_t m = 0;
    if (d->BTN_CROSS)    m |= PB_BIT(PB_CROSS);
    if (d->BTN_CIRCLE)   m |= PB_BIT(PB_CIRCLE);
    if (d->BTN_SQUARE)   m |= PB_BIT(PB_SQUARE);
    if (d->BTN_TRIANGLE) m |= PB_BIT(PB_TRIANGLE);
    if (d->BTN_L1)       m |= PB_BIT(PB_L1);
    if (d->BTN_R1)       m |= PB_BIT(PB_R1);
    if (d->BTN_L2)       m |= PB_BIT(PB_L2);
    if (d->BTN_R2)       m |= PB_BIT(PB_R2);
    if (d->BTN_L3)       m |= PB_BIT(PB_L3);
    if (d->BTN_R3)       m |= PB_BIT(PB_R3);
    if (d->BTN_START)    m |= PB_BIT(PB_START);
    if (d->BTN_SELECT)   m |= PB_BIT(PB_SELECT);
    return m;
}

static uint16_t pad_nes_bits(int port)
{
    padData *d = pad_read(port);
    uint16_t dirs = 0;
    if (d->BTN_UP)     dirs |= NB_UP;
    if (d->BTN_DOWN)   dirs |= NB_DOWN;
    if (d->BTN_LEFT)   dirs |= NB_LEFT;
    if (d->BTN_RIGHT)  dirs |= NB_RIGHT;
    dirs |= stick_nes_bits(d->ANA_L_H, d->ANA_L_V);       /* palanca izquierda = cruz */
    return snes_bits(pad_buttons(d), dirs, port);
}

static uint16_t ui_edges(void)
{
    padData *d = pad_read(0);
    uint16_t c = 0, e;
    if (d->BTN_UP)     c |= UI_UP;
    if (d->BTN_DOWN)   c |= UI_DOWN;
    if (d->BTN_LEFT)   c |= UI_LEFT;
    if (d->BTN_RIGHT)  c |= UI_RIGHT;
    {   /* v1.8.1: palanca izquierda tambien mueve los menus */
        uint16_t sb = stick_nes_bits(d->ANA_L_H, d->ANA_L_V);
        if (sb & NB_UP)    c |= UI_UP;
        if (sb & NB_DOWN)  c |= UI_DOWN;
        if (sb & NB_LEFT)  c |= UI_LEFT;
        if (sb & NB_RIGHT) c |= UI_RIGHT;
    }
    if (d->BTN_CROSS)  c |= UI_OK;
    if (d->BTN_CIRCLE) c |= UI_CANCEL;
    if (d->BTN_START)  c |= UI_START;
    e = c & ~g_ui_prev;
    g_ui_prev = c;
    return e;
}

/* v0.2.9: R3 (clic de la palanca izquierda) abre el menu en partida (antes R2: un dedo que se escapaba abria el menu y frenaba la
 * partida online). prime=1 solo memoriza el estado actual, para ignorar un R3 que siga apretado al empezar la partida. */
static int exit_pressed(int prime, uint32_t frame)
{
    static int prev;
    padData *d = pad_read(0);
    int now = d->BTN_R3 ? 1 : 0;
    int e = now && !prev;
    (void)frame;
    prev = now;
    return prime ? 0 : e;
}

/* descarta pulsaciones viejas del menu (memoriza lo que esta apretado ahora) */
static void ui_prime(void) { (void)ui_edges(); }

#else /* ------------------------- version de pruebas (PC) ------------- */

static int hr_platform_ok(void) { return getenv("NESNET_NOHR") == NULL; }   /* v0.3.0 (pruebas): NESNET_NOHR=1 usa el dibujo viejo */
static void pump(void) {}
static void present(void);                 /* definida mas abajo (puede volcar capturas de pantalla) */
static void net_ensure(void) {}

/* Pulsaciones simuladas del menu: u d l r = direcciones, x = OK, o = cancelar, s = START.
 * Al agotarse el guion (si habia uno) la app se cierra, para que las pruebas terminen solas. */
static const char *g_ui_script = "";
static int g_ui_has_script;
static uint32_t g_exit_at = 0xFFFFFFFEu;   /* prueba: frame en el que "se aprieta R2" (NESNET_R2) */
static uint32_t g_exit_at2 = 0xFFFFFFFEu;  /* prueba v1.9.1: segundo R2 (NESNET_R2B) */
static uint16_t ui_edges(void)
{
    char c = *g_ui_script;
    if (!c) { if (g_ui_has_script) g_running = 0; return 0; }
    g_ui_script++;
    switch (c) {
    case 'u': return UI_UP;
    case 'd': return UI_DOWN;
    case 'l': return UI_LEFT;
    case 'r': return UI_RIGHT;
    case 'x': return UI_OK;
    case 'o': return UI_CANCEL;
    case 's': return UI_START;
    default:  return 0;
    }
}
static uint16_t pad_nes_bits(int port) { (void)port; return 0; }
static void ui_prime(void) {}
static int exit_pressed(int prime, uint32_t frame) { return !prime && (frame == g_exit_at || frame == g_exit_at2); }

/* Capturas de prueba: NESNET_SHOTDIR=carpeta NESNET_SHOTS=3,40,90 (numeros de present()) */
static void dump_ppm(const char *path);
static uint32_t g_present_n;
static unsigned long long g_fake_draw_us;      /* prueba v0.2.5: NESNET_FAKEDRAW_MS = costo simulado del dibujo */
static void present(void)
{
    const char *dir = getenv("NESNET_SHOTDIR"), *lst = getenv("NESNET_SHOTS");
    if (g_fake_draw_us) { unsigned long long t0 = now_us(); while (now_us() - t0 < g_fake_draw_us) {} pf_draw_cur += now_us() - t0; }
    heartbeat();
    g_present_n++;
    if (dir && lst) {
        const char *p = lst;
        while (*p) {
            if ((uint32_t)atoi(p) == g_present_n) {
                char path[400];
                snprintf(path, sizeof path, "%s/shot_%u.ppm", dir, (unsigned)g_present_n);
                dump_ppm(path);
            }
            while (*p && *p != ',') p++;
            if (*p == ',') p++;
        }
    }
    g_hr_on = 0;
}

/* Mando simulado: determinista por (jugador, frame); cambia cada 6 frames */
static uint16_t script_input(int slot, uint32_t f)
{
    uint32_t x = (f / 6 + 1) * 2654435761u ^ ((uint32_t)(slot + 1) * 40503u * 2246822519u);
    uint16_t b;
    x ^= x >> 15; x *= 2246822519u; x ^= x >> 13; x *= 3266489917u; x ^= x >> 16;
    b = (uint16_t)(x & 0xFFF);            /* 12 botones SNES */
    if ((b & NB_UP) && (b & NB_DOWN))   b &= ~NB_DOWN;
    if ((b & NB_LEFT) && (b & NB_RIGHT)) b &= ~NB_RIGHT;
    return b;
}
#endif

/* ------------------------------------------------------------------ */
/* Nucleo libretro (FCEUmm)                                            */
/* ------------------------------------------------------------------ */
static bool env_cb(unsigned cmd, void *data)
{
    switch (cmd) {
    case RETRO_ENVIRONMENT_SET_PIXEL_FORMAT: {
        enum retro_pixel_format f = *(enum retro_pixel_format *)data;
        if (f == RETRO_PIXEL_FORMAT_RGB565 || f == RETRO_PIXEL_FORMAT_XRGB8888) {
            g_pixfmt = (unsigned)f;
            return true;
        }
        return false;
    }
    case RETRO_ENVIRONMENT_GET_SYSTEM_DIRECTORY:
    case RETRO_ENVIRONMENT_GET_SAVE_DIRECTORY:
        *(const char **)data = g_dir;
        return true;
    case RETRO_ENVIRONMENT_GET_CAN_DUPE:
        *(bool *)data = true;
        return true;
    case RETRO_ENVIRONMENT_GET_INPUT_BITMASKS:
        /* IMPRESCINDIBLE para el multitap: sin esto Snes9x 2010 copia las entradas del jugador 2 en los jugadores 3 a 5
         * (probado en PC: con y sin esta linea). El nucleo pide entonces RETRO_DEVICE_ID_JOYPAD_MASK. */
        return true;
    default:
        return false;
    }
}

static void video_cb(const void *data, unsigned w, unsigned h, size_t pitch)
{
    unsigned x, y, ox, oy, sx = 1, sy = 1, ow, oh;
    uint32_t hsh = 2166136261u;
    unsigned long long pf_a, pf_b;
    if (!data) return;                      /* frame repetido: no hay cambios */
    pf_a = now_us();
    if (w >= 400) sx = 2;                   /* alta resolucion (512 columnas): se toma 1 de cada 2 */
    if (h >= 400) sy = 2;                   /* entrelazado (448 lineas): se toma 1 de cada 2 */
    ow = w / sx; oh = h / sy;
    if (ow > SCR_W) ow = SCR_W;
    if (oh > SCR_H) oh = SCR_H;
    ox = (SCR_W - ow) / 2;
    oy = (SCR_H - oh) / 2;
    for (y = 0; y < SCR_W * SCR_H; y++) g_fb[y] = 0xFF000000;
    for (y = 0; y < oh; y++) {
        const uint8_t *row = (const uint8_t *)data + (size_t)(y * sy) * pitch;
        uint32_t *dst = &g_fb[(oy + y) * SCR_W + ox];
        for (x = 0; x < ow; x++) {
            uint32_t px;
            if (g_pixfmt == RETRO_PIXEL_FORMAT_RGB565) {
                uint32_t p = ((const uint16_t *)row)[x * sx];
                uint32_t r = (p >> 11) & 31, g = (p >> 5) & 63, b = p & 31;
                px = 0xFF000000u | (((r << 3) | (r >> 2)) << 16) |
                     (((g << 2) | (g >> 4)) << 8) | ((b << 3) | (b >> 2));
            } else {
                px = 0xFF000000u | (((const uint32_t *)row)[x * sx] & 0x00FFFFFFu);
            }
            dst[x] = px;
        }
    }
    pf_b = now_us();
    if (g_hash_on) {
        for (y = 0; y < SCR_W * SCR_H; y++) hsh = fnv_u32(hsh, g_fb[y]);
        g_frame_crc = hsh;
    }
    pf_vcb_cur  += pf_b - pf_a;
    pf_hash_cur += now_us() - pf_b;
}

static void audio_cb(int16_t l, int16_t r) { int16_t s2[2]; s2[0] = l; s2[1] = r; au_push(s2, 1); }
static size_t audio_batch_cb(const int16_t *d, size_t frames) { au_push(d, frames); return frames; }
static void input_poll_cb(void) {}
static int16_t input_state_cb(unsigned port, unsigned dev, unsigned idx, unsigned id)
{
    (void)idx;
    if (port > 4u || dev != RETRO_DEVICE_JOYPAD) return 0;
    if (id == RETRO_DEVICE_ID_JOYPAD_MASK) return (int16_t)(g_pad[port] & 0x0FFF);
    if (id > 11) return 0;
    return (int16_t)((g_pad[port] >> id) & 1);
}

static int read_whole_file(const char *path, uint8_t **buf, size_t *size)
{
    FILE *f = fopen(path, "rb");
    long n;
    if (!f) return 0;
    fseek(f, 0, SEEK_END);
    n = ftell(f);
    fseek(f, 0, SEEK_SET);
    if (n <= 0) { fclose(f); return 0; }
    *buf = (uint8_t *)malloc((size_t)n);
    if (!*buf || fread(*buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(*buf); *buf = NULL; return 0; }
    fclose(f);
    *size = (size_t)n;
    return 1;
}

static int hr_inflate_raw(const uint8_t *src, size_t n, uint8_t *out, size_t cap, size_t *outn);   /* definido mas abajo (lector de PNG) */

/* ---- v0.3.2: ROMs dentro de un .zip (igual que Katari v0.2.1). Se usa la primera entrada .sfc / .smc / .swc / .fig
 * (sin cifrar, guardada o deflate). El CRC con el que se emparejan las dos consolas es el de la ROM de dentro, asi que un
 * .zip y la misma ROM suelta se reconocen como el mismo juego (y comparten saves y estados). ---- */
#define ZIP_MAX_FILE  (9u * 1024u * 1024u)
#define ZIP_MAX_ROM   (8u * 1024u * 1024u + 512u)
static uint32_t zp_u16(const uint8_t *p) { return (uint32_t)p[0] | ((uint32_t)p[1] << 8); }
static uint32_t zp_u32(const uint8_t *p) { return zp_u16(p) | (zp_u16(p + 2) << 16); }
static int zp_rom_ext(const char *n, size_t len)
{
    char e[4];
    int i;
    if (len < 5 || n[len - 4] != '.') return 0;
    for (i = 0; i < 3; i++) e[i] = (char)tolower((unsigned char)n[len - 3 + i]);
    e[3] = 0;
    return !strcmp(e, "sfc") || !strcmp(e, "smc") || !strcmp(e, "swc") || !strcmp(e, "fig");
}
/* busca la entrada de la ROM; devuelve 1 y deja la posicion de sus datos, tamanos, metodo y CRC32 */
static int zip_find(const uint8_t *z, size_t n, size_t *dpos, size_t *csize, size_t *usize, int *method, uint32_t *crc, char *inner, size_t icap)
{
    size_t i, lo, cdo, p;
    uint32_t cnt, k;
    if (n < 22) return 0;
    lo = n > 65557 ? n - 65557 : 0;
    for (i = n - 22 + 1; i-- > lo; ) if (zp_u32(z + i) == 0x06054b50u) break;
    if (i + 1 == lo || zp_u32(z + i) != 0x06054b50u) return 0;
    cnt = zp_u16(z + i + 10); cdo = zp_u32(z + i + 16);
    p = cdo;
    for (k = 0; k < cnt; k++) {
        uint32_t flags, meth, comp, unc, nl, el, cl, lho, c32;
        size_t ldn, lde;
        if (p + 46 > n || zp_u32(z + p) != 0x02014b50u) return 0;
        flags = zp_u16(z + p + 8); meth = zp_u16(z + p + 10); c32 = zp_u32(z + p + 16);
        comp = zp_u32(z + p + 20); unc = zp_u32(z + p + 24);
        nl = zp_u16(z + p + 28); el = zp_u16(z + p + 30); cl = zp_u16(z + p + 32); lho = zp_u32(z + p + 42);
        if (p + 46 + nl > n) return 0;
        if (!(flags & 1) && (meth == 0 || meth == 8) && unc >= 32u * 1024u && unc <= ZIP_MAX_ROM &&
            zp_rom_ext((const char *)z + p + 46, nl) && (!inner || nl < icap)) {
            if ((size_t)lho + 30 > n || zp_u32(z + lho) != 0x04034b50u) return 0;
            ldn = zp_u16(z + lho + 26); lde = zp_u16(z + lho + 28);
            *dpos = (size_t)lho + 30 + ldn + lde;
            if (*dpos > n || comp > n - *dpos) return 0;
            *csize = comp; *usize = unc; *method = (int)meth; *crc = c32;
            if (inner) {
                const char *nm = (const char *)z + p + 46;
                size_t b = nl;
                while (b > 0 && nm[b - 1] != '/' && nm[b - 1] != '\\') b--;
                memcpy(inner, nm + b, nl - b); inner[nl - b] = 0;
            }
            return 1;
        }
        p += 46 + nl + el + cl;
    }
    return 0;
}
static int path_is_zip(const char *path)
{
    size_t n = strlen(path);
    return n > 4 && path[n - 4] == '.' && tolower((unsigned char)path[n - 3]) == 'z' && tolower((unsigned char)path[n - 2]) == 'i' && tolower((unsigned char)path[n - 1]) == 'p';
}
/* lee una ROM: archivo normal o la ROM de dentro de un .zip. inner (opcional) recibe el nombre del archivo de dentro. */
static int read_rom_file(const char *path, uint8_t **buf, size_t *size, char *inner, size_t icap)
{
    uint8_t *z = NULL, *out;
    size_t zn = 0, dpos, cs, us, got = 0;
    int meth, ok = 0;
    uint32_t c32;
    char nm[300];
    if (inner && icap) inner[0] = 0;
    if (!path_is_zip(path)) return read_whole_file(path, buf, size);
    if (!read_whole_file(path, &z, &zn)) return 0;
    if (zn > ZIP_MAX_FILE || !zip_find(z, zn, &dpos, &cs, &us, &meth, &c32, nm, sizeof nm)) { free(z); logf_("zip: %s no trae una ROM de SNES valida", path); return 0; }
    out = (uint8_t *)malloc(us);
    if (out) {
        if (meth == 0) { if (cs == us) { memcpy(out, z + dpos, us); ok = 1; } }
        else ok = hr_inflate_raw(z + dpos, cs, out, us, &got) && got == us;
        if (ok && crc32_buf(out, us) != c32) { ok = 0; logf_("zip: CRC de %s no coincide (zip danado)", nm); }
    }
    free(z);
    if (!ok) { free(out); logf_("zip: no pude descomprimir %s", path); return 0; }
    *buf = out; *size = us;
    if (inner && icap) snprintf(inner, icap, "%s", nm);
    return 1;
}

/* ------------------------------------------------------------------ */
/* Selector de ROMs (v1.7): USRDIR/roms/, reconocidas por su cabecera  */
/* ------------------------------------------------------------------ */
typedef struct { char name[ROM_NAMELEN]; uint32_t size; uint32_t crc; int has_crc; } RomEnt;   /* v1.9: tamano y CRC32 (el CRC se calcula al detenerse el cursor) */
static RomEnt g_roms[ROM_MAX];
static int    g_nroms;

static int name_cmp(const char *a, const char *b)
{
    for (;; a++, b++) {
        int x = (unsigned char)*a, y = (unsigned char)*b;
        if (x >= 'a' && x <= 'z') x -= 32;
        if (y >= 'a' && y <= 'z') y -= 32;
        if (x != y) return x < y ? -1 : 1;
        if (!x) return 0;
    }
}

static int rom_cmp(const void *a, const void *b)
{
    return name_cmp(((const RomEnt *)a)->name, ((const RomEnt *)b)->name);
}

/* 1 si el archivo parece una ROM de SNES: archivo normal, tamano razonable y extension .sfc/.smc/.swc/.fig */
static int is_snes_file(const char *path)
{
    struct stat st;
    const char *dot = strrchr(path, '.');
    if (stat(path, &st) != 0 || !S_ISREG(st.st_mode)) return 0;
    if (path_is_zip(path)) return st.st_size >= 100 && (unsigned long long)st.st_size <= ZIP_MAX_FILE;   /* v0.3.2: .zip con una ROM dentro */
    if (st.st_size < 32 * 1024 || st.st_size > 8 * 1024 * 1024 + 512) return 0;
    if (!dot) return 0;
    return !name_cmp(dot, ".SFC") || !name_cmp(dot, ".SMC") || !name_cmp(dot, ".SWC") || !name_cmp(dot, ".FIG");
}

static void roms_scan(void)
{
    char dir[300], path[420];
    DIR *d;
    struct dirent *e;
    g_nroms = 0;
    snprintf(dir, sizeof dir, "%s/roms", g_dir);
    mkdir(dir, 0777);                    /* si no existe, la crea para que se sepa donde van las ROMs */
    { char cdir[420]; snprintf(cdir, sizeof cdir, "%s/covers", g_dir); mkdir(cdir, 0777); }   /* v0.3.1: tambien la de caratulas */
    d = opendir(dir);
    if (!d) { logf_("roms: no pude abrir %s (errno=%d)", dir, errno); return; }
    while ((e = readdir(d)) != NULL && g_nroms < ROM_MAX) {
        if (e->d_name[0] == '.') continue;
        if (strlen(e->d_name) >= ROM_NAMELEN) { logf_("roms: nombre demasiado largo, lo salto"); continue; }
        snprintf(path, sizeof path, "%s/%s", dir, e->d_name);
        if (!is_snes_file(path)) continue;
        snprintf(g_roms[g_nroms].name, ROM_NAMELEN, "%s", e->d_name);
        {
            struct stat st;
            g_roms[g_nroms].size = stat(path, &st) == 0 ? (uint32_t)st.st_size : 0;
            g_roms[g_nroms].crc = 0;
            g_roms[g_nroms].has_crc = 0;
            if (path_is_zip(path)) {              /* v0.3.2: el tamano que se muestra es el de la ROM de dentro */
                uint8_t *zb = NULL;
                size_t zn = 0, dp, cs, us;
                int me, okz = 0;
                uint32_t c32;
                if (read_whole_file(path, &zb, &zn)) {
                    if (zip_find(zb, zn, &dp, &cs, &us, &me, &c32, NULL, 0)) { g_roms[g_nroms].size = (uint32_t)us; okz = 1; }
                    free(zb);
                }
                if (!okz) { logf_("roms: %s no trae una ROM de SNES dentro: no se lista", e->d_name); continue; }
            }
        }
        g_nroms++;
    }
    closedir(d);
    if (g_nroms > 1) qsort(g_roms, (size_t)g_nroms, sizeof g_roms[0], rom_cmp);
    logf_("roms: %d ROM(s) en %s", g_nroms, dir);
}

/* Algunas ROMs traen 512 bytes de cabecera de copiador al inicio (tamano = multiplo de 1024 + 512). Para comparar la ROM
 * entre las dos consolas se calcula el CRC32 SIN esa cabecera: asi un .smc con cabecera y el mismo juego en .sfc sin ella
 * se reconocen como la misma ROM. */
static uint32_t snes_crc(const uint8_t *d, size_t n)
{
    size_t off = (n % 1024u) == 512u ? 512u : 0u;
    return crc32_buf(d + off, n - off);
}

/* 1 si la cabecera dice que el cartucho trae el chip Super FX (GSU). Se miran las dos posiciones habituales de la cabecera
 * (LoROM $7FC0, HiROM $FFC0) y solo se acepta si el checksum de la cabecera es coherente (complemento + suma = $FFFF). */
static int snes_is_superfx(const uint8_t *d, size_t n)
{
    size_t off = (n % 1024u) == 512u ? 512u : 0u, bases[2] = { 0x7FC0u, 0xFFC0u }, k;
    for (k = 0; k < 2; k++) {
        size_t b = off + bases[k];
        unsigned chip, comp, sum;
        if (n < b + 0x20) continue;
        comp = d[b + 0x1C] | ((unsigned)d[b + 0x1D] << 8);
        sum  = d[b + 0x1E] | ((unsigned)d[b + 0x1F] << 8);
        if ((comp ^ sum) != 0xFFFFu) continue;
        chip = d[b + 0x16];
        if ((chip >> 4) == 1 && (chip & 0x0Fu) >= 3) return 1;
    }
    return 0;
}

/* Lee la ROM g_roms[idx] y la deja como la activa (g_rom/g_romcrc). 1 = bien */
static int rom_load(int idx)
{
    char path[420];
    uint8_t *buf = NULL;
    size_t sz = 0;
    char inner[300];
    g_rom_why = "";
    snprintf(path, sizeof path, "%s/roms/%s", g_dir, g_roms[idx].name);
    if (!read_rom_file(path, &buf, &sz, inner, sizeof inner)) { logf_("roms: no pude leer %s", path); if (path_is_zip(path)) g_rom_why = "NO PUDE ABRIR EL .ZIP"; return 0; }
    if (snes_is_superfx(buf, sz)) {
        free(buf);
        g_rom_why = "JUEGO CON CHIP SUPER FX: NO SOPORTADO";
        logf_("roms: %s trae el chip Super FX: no soportado en esta version", g_roms[idx].name);
        return 0;
    }
    free(g_rom);
    g_rom = buf;
    g_romsz = sz;
    g_romcrc = snes_crc(g_rom, g_romsz);
    if (inner[0]) { snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s/roms/%s", g_dir, inner); logf_("roms: ROM dentro del zip: %s", inner); }
    else snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s", path);
    snprintf(g_rom_name, sizeof g_rom_name, "%s", g_roms[idx].name);
    logf_("ROM elegida: %s  %u bytes  crc32=%08X", g_rom_name, (unsigned)g_romsz, (unsigned)g_romcrc);
    return 1;
}

static void core_boot(void)
{
    retro_set_environment(env_cb);
    retro_set_video_refresh(video_cb);
    retro_set_audio_sample(audio_cb);
    retro_set_audio_sample_batch(audio_batch_cb);
    retro_set_input_poll(input_poll_cb);
    retro_set_input_state(input_state_cb);
    retro_init();
}


static void core_log_av(void)
{
    struct retro_system_av_info av;
    memset(&av, 0, sizeof av);
    retro_get_system_av_info(&av);
    if (av.timing.sample_rate >= 8000.0 && av.timing.sample_rate <= 96000.0) g_au_inrate = av.timing.sample_rate;
    logf_("audio: el nucleo entrega %d Hz a %d cuadros/s", (int)g_au_inrate, (int)(av.timing.fps + 0.5));
}

/* SOLO: dos mandos normales (puertos 1 y 2) */
static int core_load(void)
{
    struct retro_game_info gi;
    if (g_core_loaded) return 1;
    memset(&gi, 0, sizeof gi);
    gi.path = g_cfg.rom;
    gi.data = g_rom;
    gi.size = g_romsz;
    if (!retro_load_game(&gi)) { g_err = "EL NUCLEO NO PUDO CARGAR LA ROM"; return 0; }
    retro_set_controller_port_device(0, RETRO_DEVICE_JOYPAD);
    retro_set_controller_port_device(1, RETRO_DEVICE_JOYPAD);
    core_log_av();
    g_core_loaded = 1;
    return 1;
}

/* 2 VS 2: mando normal en el puerto 1 y MULTITAP en el puerto 2 (jugadores 2 a 5 de libretro = puertos 1 a 4).
 * Snes9x 2010 solo reparte las 4 entradas en los juegos de su lista interna (Super Bomberman 3 esta); en los demas el
 * multitap copia al jugador 2. Necesita GET_INPUT_BITMASKS (ver env_cb). */
static int core_load4(void)
{
    struct retro_game_info gi;
    if (g_core_loaded) return 1;
    memset(&gi, 0, sizeof gi);
    gi.path = g_cfg.rom;
    gi.data = g_rom;
    gi.size = g_romsz;
    if (!retro_load_game(&gi)) { g_err = "EL NUCLEO NO PUDO CARGAR LA ROM"; return 0; }
    retro_set_controller_port_device(0, RETRO_DEVICE_JOYPAD);
    retro_set_controller_port_device(1, SNES_DEV_MULTITAP);
    logf_("2 vs 2: puerto 2 con multitap");
    core_log_av();
    g_core_loaded = 1;
    return 1;
}

static void core_unload(void)
{
    if (g_core_loaded) { retro_unload_game(); g_core_loaded = 0; }
}

/* ------------------------------------------------------------------ */
/* v1.9: guardado de bateria (SRAM) - SOLO en el modo SOLO              */
/* Archivo: USRDIR/saves/<CRC32 de la ROM>.srm (asi renombrar la ROM no pierde el guardado).                      */
/* En online NO se carga ni se guarda nada: las dos consolas tienen que empezar con la misma memoria, si no se       */
/* desincronizan, y ademas una partida online no debe pisar tu guardado.                                          */
/* ------------------------------------------------------------------ */
#define SRAM_MAX 0x20000
static uint8_t g_sram_last[SRAM_MAX];     /* lo ultimo escrito en disco (para guardar solo si cambio) */
static size_t  g_sram_lastsz;
static int     g_sram_on;                 /* 1 = esta partida guarda (solo SOLO, y solo si el juego tiene bateria) */

static void sram_path(char *out, size_t cap)
{
    snprintf(out, cap, "%s/saves/%08X.srm", g_dir, (unsigned)g_romcrc);
}

static uint8_t *sram_ptr(size_t *sz)
{
    void *p = retro_get_memory_data(RETRO_MEMORY_SAVE_RAM);
    size_t n = retro_get_memory_size(RETRO_MEMORY_SAVE_RAM);
    if (!p || n == 0 || n > SRAM_MAX) return NULL;
    *sz = n;
    return (uint8_t *)p;
}

/* Llamar justo despues de core_load() en el modo SOLO: carga el guardado si existe */
static void sram_begin(void)
{
    size_t n = 0, fsz = 0;
    uint8_t *p, *buf = NULL;
    char path[420], tmp[440];
    int got;
    g_sram_on = 0; g_sram_lastsz = 0;
    p = sram_ptr(&n);
    if (!p) { logf_("guardado: este juego no usa memoria de bateria"); return; }
    g_sram_on = 1;
    sram_path(path, sizeof path);
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    got = read_whole_file(path, &buf, &fsz);
    if (!got) got = read_whole_file(tmp, &buf, &fsz);          /* si se corto la luz justo al guardar, queda el .tmp completo */
    if (got) {
        if (fsz == n) { memcpy(p, buf, n); logf_("guardado: cargado %s (%u bytes)", path, (unsigned)n); }
        else {
            char old[450];
            snprintf(old, sizeof old, "%s.old", path);
            remove(old);
            rename(path, old);                                   /* no lo borro: queda como .old */
            logf_("AVISO: el guardado tenia %u bytes y el juego pide %u: lo movi a .old y empiezo de cero", (unsigned)fsz, (unsigned)n);
        }
        free(buf);
    } else {
        logf_("guardado: partida nueva (aun no hay %s)", path);
    }
    memcpy(g_sram_last, p, n);
    g_sram_lastsz = n;
}

/* Escribe el guardado si cambio desde la ultima vez (force = siempre). */
static void sram_save(int force)
{
    size_t n = 0;
    uint8_t *p;
    char dir[320], path[420], tmp[440];
    FILE *f;
    int ok;
    if (!g_sram_on) return;
    p = sram_ptr(&n);
    if (!p || n != g_sram_lastsz) return;
    if (!force && !memcmp(p, g_sram_last, n)) return;
    snprintf(dir, sizeof dir, "%s/saves", g_dir);
    mkdir(dir, 0777);
    sram_path(path, sizeof path);
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    f = fopen(tmp, "wb");
    if (!f) { logf_("AVISO: no pude crear %s (errno=%d)", tmp, errno); return; }
    ok = fwrite(p, 1, n, f) == n;
    if (fclose(f) != 0) ok = 0;
    if (!ok) { logf_("AVISO: no pude escribir el guardado"); remove(tmp); return; }
    remove(path);
    if (rename(tmp, path) != 0) { logf_("AVISO: no pude renombrar el guardado (queda %s)", tmp); return; }
    memcpy(g_sram_last, p, n);
    logf_("guardado: escrito %s (%u bytes)", path, (unsigned)n);
}

/* ------------------------------------------------------------------ */
/* v1.9.1: estados guardados (savestates) - SOLO en el modo SOLO         */
/* Archivo: USRDIR/saves/<CRC32 de la ROM>_<ranura 1..3>.sta. En online NO existen (las dos consolas tendrian que     */
/* cargar el mismo estado a la vez y se desincronizarian).                                                         */
/* ------------------------------------------------------------------ */
#define STATE_SLOTS 6                     /* v0.2.8: 6 ranuras (antes 3); las 1 a 3 de antes siguen siendo las mismas */
#define STATE_MAX   0x200000
static int  g_state_slot;                 /* ranura elegida en el menu (0..STATE_SLOTS-1); se recuerda mientras la app esta abierta */
static char g_toast[48];                  /* aviso corto sobre la imagen (guardado, cargado, error) */
static int  g_toast_n;

static void toast(const char *s) { snprintf(g_toast, sizeof g_toast, "%s", s); g_toast_n = 150; }

static void state_path(int slot, char *out, size_t cap)
{
    snprintf(out, cap, "%s/saves/%08X_%d.sta", g_dir, (unsigned)g_romcrc, slot + 1);
}

static int state_exists(int slot)
{
    char path[420];
    FILE *f;
    state_path(slot, path, sizeof path);
    f = fopen(path, "rb");
    if (!f) return 0;
    fclose(f);
    return 1;
}

static int state_save(int slot)
{
    size_t n = retro_serialize_size();
    uint8_t *buf;
    char dir[320], path[420], tmp[440];
    FILE *f;
    int ok;
    if (n == 0 || n > STATE_MAX) { logf_("AVISO: estado: el nucleo pide %u bytes (no valido)", (unsigned)n); return 0; }
    buf = (uint8_t *)malloc(n);
    if (!buf) { logf_("AVISO: estado: sin memoria para %u bytes", (unsigned)n); return 0; }
    if (!retro_serialize(buf, n)) { free(buf); logf_("AVISO: estado: el nucleo no pudo guardar"); return 0; }
    snprintf(dir, sizeof dir, "%s/saves", g_dir);
    mkdir(dir, 0777);
    state_path(slot, path, sizeof path);
    snprintf(tmp, sizeof tmp, "%s.tmp", path);
    f = fopen(tmp, "wb");
    if (!f) { free(buf); logf_("AVISO: no pude crear %s (errno=%d)", tmp, errno); return 0; }
    ok = fwrite(buf, 1, n, f) == n;
    if (fclose(f) != 0) ok = 0;
    if (!ok) { free(buf); remove(tmp); logf_("AVISO: no pude escribir el estado"); return 0; }
    remove(path);
    if (rename(tmp, path) != 0) { free(buf); logf_("AVISO: no pude renombrar el estado (queda %s)", tmp); return 0; }
    logf_("estado: guardado ranura %d (%u bytes, crc %08X)", slot + 1, (unsigned)n, (unsigned)crc32_buf(buf, n));
    free(buf);
    return 1;
}

static int state_load(int slot)
{
    size_t n = retro_serialize_size(), fsz = 0;
    uint8_t *buf = NULL;
    char path[420];
    int ok;
    state_path(slot, path, sizeof path);
    if (!read_whole_file(path, &buf, &fsz)) { logf_("estado: la ranura %d esta vacia", slot + 1); return -1; }
    if (fsz != n) {
        free(buf);
        logf_("AVISO: estado: la ranura %d tiene %u bytes y el nucleo pide %u: no la cargo", slot + 1, (unsigned)fsz, (unsigned)n);
        return 0;
    }
    ok = retro_unserialize(buf, fsz) ? 1 : 0;
    logf_("estado: cargada ranura %d (%u bytes, crc %08X) %s", slot + 1, (unsigned)fsz, (unsigned)crc32_buf(buf, fsz), ok ? "OK" : "FALLO");
    free(buf);
    return ok;
}

/* v0.2.7: lee la ranura a memoria (para mandarsela al amigo en ONLINE). 1 = bien (el que llama libera *buf) */
static int state_read(int slot, uint8_t **buf, size_t *n)
{
    size_t want = retro_serialize_size(), fsz = 0;
    char path[420];
    uint8_t *b = NULL;
    state_path(slot, path, sizeof path);
    if (!read_whole_file(path, &b, &fsz)) { logf_("estado: la ranura %d esta vacia", slot + 1); return 0; }
    if (fsz != want || fsz == 0 || fsz > STATE_MAX) {
        free(b);
        logf_("AVISO: estado: la ranura %d tiene %u bytes y el nucleo pide %u: no la cargo", slot + 1, (unsigned)fsz, (unsigned)want);
        return 0;
    }
    *buf = b;
    *n = fsz;
    return 1;
}

static void step_frame(uint16_t p1, uint16_t p2)
{
    g_pad[0] = p1;
    g_pad[1] = p2;
    retro_run();
}

/* 4 mandos (puerto 1 + multitap del puerto 2) */
static void step_frame4(uint16_t p1, uint16_t p2, uint16_t p3, uint16_t p4)
{
    g_pad[0] = p1;
    g_pad[1] = p2;
    g_pad[2] = p3;
    g_pad[3] = p4;
    g_pad[4] = 0;
    {
        unsigned long long pf_a = now_us();
        retro_run();
        pf_run_cur += now_us() - pf_a;
    }
}

/* ------------------------------------------------------------------ */
/* Red: mensajes de 16 bytes, TCP, poll() con espera propia            */
/* ------------------------------------------------------------------ */
enum { M_HELLO = 1, M_PING, M_PONG, M_CFG, M_START, M_INPUT, M_QUIT, M_REJECT, M_RESET, M_STATE };   /* M_RESET (frame = cuadro en que ambos reinician) */
/* v0.2.7: M_STATE = el host manda un estado guardado: frame = cuadro en que los dos lo cargan, v1 = bytes, v2 = CRC32 de los datos;
 * justo despues de este mensaje de 20 bytes vienen v1 bytes sin marco (ver net_send_raw / net_recv_raw).
 * M_PING durante una partida es solo un "sigo aqui" (el otro lado lo ignora): se manda cada 2 s con el menu de R2 abierto. */

typedef struct {
    uint8_t  type, a;
    uint16_t input;
    uint32_t frame, v1, v2, v3;     /* v3: en M_INPUT, los 2 mandos de la consola (16 bits cada uno) */
} Msg;

static void put32(uint8_t *p, uint32_t v) { p[0] = v >> 24; p[1] = v >> 16; p[2] = v >> 8; p[3] = v; }
static uint32_t get32(const uint8_t *p) { return ((uint32_t)p[0] << 24) | (p[1] << 16) | (p[2] << 8) | p[3]; }

static int net_send(const Msg *m)
{
    uint8_t b[MSG_SIZE];
    int off = 0;
    memset(b, 0, sizeof b);
    b[0] = m->type; b[1] = m->a; b[2] = m->input >> 8; b[3] = m->input & 0xFF;
    put32(b + 4, m->frame); put32(b + 8, m->v1); put32(b + 12, m->v2); put32(b + 16, m->v3);
#ifdef NESNET_HOST
    { const char *j = getenv("NESNET_JITTER_MS"); if (j && atoi(j) > 0) sleep_ms(rand() % (atoi(j) + 1)); }
#endif
    while (off < MSG_SIZE) {
        int n = (int)send(g_net, (const char *)b + off, MSG_SIZE - off, 0);
        if (n <= 0) return 0;
        off += n;
    }
    return 1;
}

/* Espera a que 'fd' tenga evento; 1 = listo, 0 = agotado, -1 = error */
static int fd_wait(int fd, short ev, int timeout_ms)
{
    uint32_t t0 = now_ms();
    for (;;) {
        struct pollfd p;
        int r;
        p.fd = fd; p.events = ev; p.revents = 0;
        r = poll(&p, 1, 0);
        if (r < 0) return -1;
        if (r > 0) return 1;
        if ((int)(now_ms() - t0) >= timeout_ms) return 0;
        pump();
        if (!g_running) return -1;
        sleep_ms(2);
    }
}

/* 1 = mensaje, 0 = tiempo agotado, -1 = error / conexion cerrada */
static int net_recv(Msg *m, int timeout_ms)
{
    uint32_t t0 = now_ms();
    for (;;) {
        if (g_rxlen >= MSG_SIZE) {
            const uint8_t *b = g_rx;
            m->type = b[0]; m->a = b[1]; m->input = (uint16_t)((b[2] << 8) | b[3]);
            m->frame = get32(b + 4); m->v1 = get32(b + 8); m->v2 = get32(b + 12); m->v3 = get32(b + 16);
            memmove(g_rx, g_rx + MSG_SIZE, g_rxlen - MSG_SIZE);
            g_rxlen -= MSG_SIZE;
            return 1;
        }
        {
            int left = timeout_ms - (int)(now_ms() - t0);
            int r = fd_wait(g_net, POLLIN, left > 0 ? left : 0);
            int n;
            if (r < 0) return -1;
            if (r == 0) return 0;
            n = (int)recv(g_net, (char *)g_rx + g_rxlen, (int)sizeof g_rx - g_rxlen, 0);
            if (n <= 0) return -1;
            g_rxlen += n;
        }
    }
}

/* v0.2.7: bloques grandes sin marco (estados guardados), justo despues de un mensaje M_STATE. net_recv_raw primero vacia lo que
 * net_recv ya dejo leido en g_rx (el mensaje y los primeros bytes pueden llegar juntos). Cada espera se renueva con cada trozo
 * recibido o enviado: se rinde solo si pasan 20 s sin avanzar nada. */
static int net_send_raw(const uint8_t *src, size_t len)
{
    size_t off = 0;
    uint32_t t0 = now_ms();
    while (off < len) {
        int r = fd_wait(g_net, POLLOUT, 100), n;
        size_t chunk = len - off > 16384 ? 16384 : len - off;
        if (r < 0) return 0;
        if (r == 0) { if ((int)(now_ms() - t0) > 20000) return 0; continue; }
        n = (int)send(g_net, (const char *)src + off, chunk, 0);
        if (n <= 0) return 0;
        off += (size_t)n;
        t0 = now_ms();
    }
    return 1;
}

static int net_recv_raw(uint8_t *dst, size_t len)
{
    size_t got = 0;
    uint32_t t0 = now_ms();
    if (g_rxlen > 0) {
        size_t k = (size_t)g_rxlen < len ? (size_t)g_rxlen : len;
        memcpy(dst, g_rx, k);
        memmove(g_rx, g_rx + k, (size_t)g_rxlen - k);
        g_rxlen -= (int)k;
        got = k;
    }
    while (got < len) {
        int r = fd_wait(g_net, POLLIN, 200), n;
        size_t want = len - got > 65536 ? 65536 : len - got;
        if (r < 0) return 0;
        if (r == 0) { if ((int)(now_ms() - t0) > 20000) return 0; continue; }
        n = (int)recv(g_net, (char *)dst + got, (int)want, 0);
        if (n <= 0) return 0;
        got += (size_t)n;
        t0 = now_ms();
    }
    return 1;
}

static void sock_nonblock(int fd, int on)
{
#ifdef NESNET_PS3
    int v = on;
    setsockopt(fd, SOL_SOCKET, SO_NBIO, &v, sizeof v);
#else
    int fl = fcntl(fd, F_GETFL, 0);
    fcntl(fd, F_SETFL, on ? (fl | O_NONBLOCK) : (fl & ~O_NONBLOCK));
#endif
}

static void sock_nodelay(int fd)
{
    int one = 1;
    setsockopt(fd, IPPROTO_TCP, TCP_NODELAY, &one, sizeof one);   /* si falla, no pasa nada */
}

/* v1.6: diagnostico de connect. kind: 0 ok, 1 sin respuesta (timeout), 2 rechazado o error de red, 3 sin socket */
static int      g_conn_kind;
static int      g_conn_err;
static uint32_t g_conn_ms;

static int tcp_connect(uint32_t ip, int port, int timeout_ms)
{
    struct sockaddr_in a;
    uint32_t t0 = now_ms();
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    g_conn_kind = 0; g_conn_err = 0; g_conn_ms = 0;
    if (fd < 0) { g_conn_kind = 3; g_conn_err = errno; goto fail; }
    sock_nonblock(fd, 1);
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port);
    a.sin_addr.s_addr = htonl(ip);
    if (connect(fd, (struct sockaddr *)&a, sizeof a) < 0) {
        int err = 0, r;
        socklen_t l = sizeof err;
        r = fd_wait(fd, POLLOUT, timeout_ms);
        if (r <= 0) { g_conn_kind = (r == 0) ? 1 : 2; closesocket(fd); goto fail; }
        if (getsockopt(fd, SOL_SOCKET, SO_ERROR, &err, &l) == 0 && err != 0) {
            g_conn_kind = 2; g_conn_err = err; closesocket(fd); goto fail;
        }
    }
    sock_nonblock(fd, 0);
    sock_nodelay(fd);
    g_conn_ms = now_ms() - t0;
    return fd;
fail:
    g_conn_ms = now_ms() - t0;
    logf_("connect %u.%u.%u.%u:%d FALLO: %s (error=%d) tras %u ms",
          (unsigned)(ip >> 24), (unsigned)((ip >> 16) & 255), (unsigned)((ip >> 8) & 255), (unsigned)(ip & 255), port,
          g_conn_kind == 1 ? "SIN RESPUESTA (timeout)" : g_conn_kind == 3 ? "NO SE PUDO CREAR EL SOCKET" : "RECHAZADO O ERROR DE RED",
          g_conn_err, (unsigned)g_conn_ms);
    return -1;
}

static int tcp_listen(int port)
{
    struct sockaddr_in a;
    int one = 1, rb, rl;
    int fd = socket(AF_INET, SOCK_STREAM, 0);
    if (fd < 0) { logf_("escucha: socket() fallo (errno=%d)", errno); return -1; }
    setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &one, sizeof one);
    memset(&a, 0, sizeof a);
    a.sin_family = AF_INET;
    a.sin_port = htons((uint16_t)port);
    a.sin_addr.s_addr = htonl(INADDR_ANY);
    rb = bind(fd, (struct sockaddr *)&a, sizeof a);
    rl = rb < 0 ? -1 : listen(fd, 1);
    logf_("escucha: puerto TCP %d  bind=%d listen=%d", port, rb, rl);
    if (rb < 0 || rl < 0) { closesocket(fd); return -1; }
    return fd;
}

static int parse_ip(const char *s, uint32_t *out)
{
    unsigned a, b, c, d;
    char tail;
    if (sscanf(s, "%u.%u.%u.%u%c", &a, &b, &c, &d, &tail) < 4) return 0;
    if (a > 255 || b > 255 || c > 255 || d > 255) return 0;
    *out = (a << 24) | (b << 16) | (c << 8) | d;
    return 1;
}

/* IP publica: GET http://api.ipify.org (devuelve solo la IP en texto) */
static int get_public_ip(uint32_t *ip)
{
    static const char req[] =
        "GET / HTTP/1.0\r\nHost: api.ipify.org\r\nConnection: close\r\n\r\n";
    struct hostent *he;
    uint8_t *b;
    char buf[512];
    int fd, n, len = 0;
    char *body;
    uint32_t sip;

    he = gethostbyname("api.ipify.org");
    if (!he || !he->h_addr_list || !he->h_addr_list[0]) return 0;
    b = (uint8_t *)he->h_addr_list[0];
    sip = ((uint32_t)b[0] << 24) | (b[1] << 16) | (b[2] << 8) | b[3];
    fd = tcp_connect(sip, 80, 6000);
    if (fd < 0) return 0;
    if (send(fd, req, (int)sizeof req - 1, 0) <= 0) { closesocket(fd); return 0; }
    while (len < (int)sizeof buf - 1 && fd_wait(fd, POLLIN, 6000) > 0) {
        n = (int)recv(fd, buf + len, (int)sizeof buf - 1 - len, 0);
        if (n <= 0) break;
        len += n;
    }
    closesocket(fd);
    buf[len] = 0;
    body = strstr(buf, "\r\n\r\n");
    if (!body) return 0;
    body += 4;
    while (*body == ' ' || *body == '\r' || *body == '\n') body++;
    return parse_ip(body, ip);
}

/* ------------------------------------------------------------------ */
/* UPnP (v1.6): el host abre su puerto TCP en el router y lee la IP del */
/* router. Los pasos (SSDP -> descripcion del router -> llamadas SOAP)  */
/* siguen el netplay de Melee-PS3 (ps3/net/upnp.c, GPLv2 o posterior),  */
/* que ya conecto entre estas dos casas; aqui es una version propia     */
/* sobre los sockets de NesNet.                                         */
/* ------------------------------------------------------------------ */
typedef struct {
    int      router;      /* un router contesto por UPnP */
    int      opened;      /* el puerto lleva a esta consola */
    int      http;        /* estado HTTP del AddPortMapping (0 = no hubo) */
    int      error;       /* codigo de error UPnP (0 = ninguno) */
    uint32_t public_ip;   /* IP WAN que dice el router (0 = no la dio) */
    uint32_t local_ip;    /* IP de esta consola en la LAN (0 = no se pudo leer) */
} Upnp;

#define UPNP_BUF 12288
static char     g_ubuf[UPNP_BUF];
static uint32_t g_ctl_ip;
static int      g_ctl_port;
static char     g_ctl_path[160], g_ctl_svc[96];
static int      g_upnp_added, g_upnp_port;

#define IP4(ip) (unsigned)((ip) >> 24), (unsigned)(((ip) >> 16) & 255), (unsigned)(((ip) >> 8) & 255), (unsigned)((ip) & 255)

static int ip_privada(uint32_t ip)
{
    return (ip >> 24) == 10 || (ip >> 20) == 0xAC1 || (ip >> 16) == 0xC0A8 || (ip >> 22) == ((100u << 2) | 1) ||
           (ip >> 24) == 127 || (ip >> 16) == 0xA9FE || ip == 0;
}

static void sa_fill(struct sockaddr_in *s, uint32_t ip, int port)
{
    memset(s, 0, sizeof *s);
#ifdef NESNET_PS3
    s->sin_len = sizeof *s;               /* PSL1GHT es BSD: con sin_len=0, sendto falla con ENOENT */
#endif
    s->sin_family = AF_INET;
    s->sin_port = htons((uint16_t)port);
    s->sin_addr.s_addr = htonl(ip);
}

/* IP de esta consola en su red local */
static uint32_t local_ip_get(void)
{
#ifdef NESNET_PS3
    static int loaded;
    union net_ctl_info info;
    if (!loaded) { loaded = 1; sysModuleLoad(SYSMODULE_NETCTL); netCtlInit(); }
    if (netCtlGetInfo(NET_CTL_INFO_IP_ADDRESS, &info) < 0) return 0;
    if (inet_addr(info.ip_address) == INADDR_NONE) return 0;
    return ntohl(inet_addr(info.ip_address));
#else
    const char *e = getenv("NESNET_LOCAL_IP");
    uint32_t ip;
    return (e && parse_ip(e, &ip)) ? ip : 0x7F000001u;
#endif
}

/* Un datagrama UDP y la primera respuesta (en resp). Devuelve los bytes o -1. Sigue atendiendo al sistema (pump). */
static int upnp_udp_ask(uint32_t ip, int port, const char *req, int len, char *resp, int cap, int ms)
{
    struct sockaddr_in s;
    struct timeval tv;
    uint32_t t0;
    int fd, n = -1;
    fd = socket(AF_INET, SOCK_DGRAM, 0);
    if (fd < 0) return -1;
    tv.tv_sec = 0; tv.tv_usec = 100000;
    setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, sizeof tv);
    sa_fill(&s, ip, port);
    if (sendto(fd, req, (size_t)len, 0, (struct sockaddr *)&s, sizeof s) == len) {
        t0 = now_ms();
        for (;;) {
            socklen_t sl = sizeof s;
            int r = (int)recvfrom(fd, resp, (size_t)cap, 0, (struct sockaddr *)&s, &sl);
            if (r > 0) { n = r; break; }
            if ((int)(now_ms() - t0) >= ms) break;
            pump();
            if (!g_running) break;
            sleep_ms(2);
        }
    }
    closesocket(fd);
    return n;
}

/* Pide por HTTP/TCP y deja la respuesta (terminada en 0) en g_ubuf. Devuelve los bytes o -1. */
static int upnp_http(uint32_t ip, int port, const char *req, int ms)
{
    int fd, len = 0, n;
    fd = tcp_connect(ip, port, ms);
    if (fd < 0) return -1;
    if (send(fd, req, (int)strlen(req), 0) <= 0) { closesocket(fd); return -1; }
    while (len < UPNP_BUF - 1 && fd_wait(fd, POLLIN, ms) > 0) {
        n = (int)recv(fd, g_ubuf + len, UPNP_BUF - 1 - len, 0);
        if (n <= 0) break;
        len += n;
    }
    closesocket(fd);
    g_ubuf[len] = 0;
    return len > 0 ? len : -1;
}

/* Texto entre <name> y </name> a partir de p; devuelve donde acaba o NULL */
static const char *x_tag(const char *p, const char *name, char *out, size_t cap)
{
    char open[64], close_[64];
    const char *s, *e;
    size_t n;
    snprintf(open, sizeof open, "<%s>", name);
    snprintf(close_, sizeof close_, "</%s>", name);
    s = strstr(p, open);
    if (!s) return NULL;
    e = strstr(s, close_);
    if (!e) return NULL;
    s += strlen(open);
    n = (size_t)(e - s) < cap - 1 ? (size_t)(e - s) : cap - 1;
    memcpy(out, s, n);
    out[n] = 0;
    return e;
}

/* "http://a.b.c.d[:puerto]/ruta" */
static int x_url(const char *url, uint32_t *ip, int *port, char *path, size_t cap)
{
    unsigned a, b, c, d, pt = 80;
    const char *slash;
    if (strncmp(url, "http://", 7) != 0 || sscanf(url + 7, "%u.%u.%u.%u", &a, &b, &c, &d) != 4) return 0;
    if (a > 255 || b > 255 || c > 255 || d > 255) return 0;
    slash = strchr(url + 7, '/');
    sscanf(url + 7, "%*[0-9.]:%u", &pt);
    *ip = (a << 24) | (b << 16) | (c << 8) | d;
    *port = (int)pt;
    snprintf(path, cap, "%s", slash ? slash : "/");
    return 1;
}

static int ci_prefix(const char *s, const char *pre)
{
    for (; *pre; s++, pre++) {
        char x = *s, y = *pre;
        if (x >= 'A' && x <= 'Z') x = (char)(x + 32);
        if (y >= 'A' && y <= 'Z') y = (char)(y + 32);
        if (x != y) return 0;
    }
    return 1;
}

/* Busca el router (SSDP), lee su descripcion y guarda la URL de control. 1 = encontrado */
static int upnp_discover(void)
{
    static const char search[] =
        "M-SEARCH * HTTP/1.1\r\nHOST: 239.255.255.250:1900\r\nMAN: \"ssdp:discover\"\r\nMX: 2\r\n"
        "ST: urn:schemas-upnp-org:device:InternetGatewayDevice:1\r\n\r\n";
    char url[192], path[160], req[360], type[96], ctl[160];
    uint32_t dip = 0;
    int dport = 0, n;
    const char *p;
    url[0] = 0;
#ifdef NESNET_HOST
    if (getenv("NESNET_UPNP_URL")) snprintf(url, sizeof url, "%s", getenv("NESNET_UPNP_URL"));
#endif
    if (!url[0]) {
        n = upnp_udp_ask(0xEFFFFFFAu, 1900, search, (int)sizeof search - 1, g_ubuf, UPNP_BUF - 1, 2000);
        if (n <= 0) { logf_("upnp: SSDP sin respuesta en 2 s (el router no tiene UPnP o lo bloquea)"); return 0; }
        g_ubuf[n] = 0;
        p = g_ubuf;
        while (p && !ci_prefix(p, "location:")) { p = strchr(p, '\n'); p = p ? p + 1 : NULL; }
        if (!p || sscanf(p + 9, " %191s", url) != 1) { logf_("upnp: la respuesta SSDP no trae LOCATION"); return 0; }
    }
    if (!x_url(url, &dip, &dport, path, sizeof path)) { logf_("upnp: URL de descripcion no valida: %s", url); return 0; }
    snprintf(req, sizeof req, "GET %s HTTP/1.0\r\nHost: %u.%u.%u.%u:%d\r\nConnection: close\r\n\r\n", path, IP4(dip), dport);
    if (upnp_http(dip, dport, req, 3000) <= 0) { logf_("upnp: no pude leer la descripcion del router (%s)", url); return 0; }
    for (p = g_ubuf; (p = x_tag(p, "serviceType", type, sizeof type)) != NULL;) {
        if ((strstr(type, "WANIPConnection") || strstr(type, "WANPPPConnection")) && x_tag(p, "controlURL", ctl, sizeof ctl)) {
            snprintf(g_ctl_svc, sizeof g_ctl_svc, "%s", type);
            g_ctl_ip = dip; g_ctl_port = dport;
            if (ctl[0] == '/') { snprintf(g_ctl_path, sizeof g_ctl_path, "%s", ctl); return 1; }
            if (!strncmp(ctl, "http://", 7)) return x_url(ctl, &g_ctl_ip, &g_ctl_port, g_ctl_path, sizeof g_ctl_path);
            snprintf(g_ctl_path, sizeof g_ctl_path, "/%s", ctl);
            return 1;
        }
    }
    logf_("upnp: el router no ofrece WANIPConnection/WANPPPConnection");
    return 0;
}

/* Una llamada SOAP al router: estado HTTP (o -1); respuesta en g_ubuf; error UPnP en *err */
static int upnp_soap(const char *action, const char *args, int *err)
{
    static char body[1024], req[1792];
    char code[16], status[8];
    snprintf(body, sizeof body,
             "<?xml version=\"1.0\"?>\r\n<s:Envelope xmlns:s=\"http://schemas.xmlsoap.org/soap/envelope/\" "
             "s:encodingStyle=\"http://schemas.xmlsoap.org/soap/encoding/\"><s:Body><u:%s xmlns:u=\"%s\">%s</u:%s>"
             "</s:Body></s:Envelope>\r\n", action, g_ctl_svc, args, action);
    snprintf(req, sizeof req,
             "POST %s HTTP/1.0\r\nHost: %u.%u.%u.%u:%d\r\nContent-Type: text/xml; charset=\"utf-8\"\r\n"
             "Content-Length: %d\r\nSOAPAction: \"%s#%s\"\r\nConnection: close\r\n\r\n%s",
             g_ctl_path, IP4(g_ctl_ip), g_ctl_port, (int)strlen(body), g_ctl_svc, action, body);
    *err = 0;
    if (upnp_http(g_ctl_ip, g_ctl_port, req, 3000) <= 0 || sscanf(g_ubuf, "HTTP/%*s %7s", status) != 1) return -1;
    if (x_tag(g_ubuf, "errorCode", code, sizeof code)) *err = atoi(code);
    return atoi(status);
}

/* Abre el puerto TCP en el router hacia esta consola y lee la IP del router */
static void upnp_open(int port, Upnp *u)
{
    char args[640], ip[20], value[40];
    unsigned a, b, c, d;
    int status, err = 0, lease = 7200;

    memset(u, 0, sizeof *u);
    u->local_ip = local_ip_get();
    logf_("upnp: IP local de la consola = %u.%u.%u.%u", IP4(u->local_ip));
    if (!upnp_discover()) return;
    u->router = 1;
    logf_("upnp: router en %u.%u.%u.%u:%d servicio=%s", IP4(g_ctl_ip), g_ctl_port, g_ctl_svc);
    if (upnp_soap("GetExternalIPAddress", "", &err) == 200 && x_tag(g_ubuf, "NewExternalIPAddress", value, sizeof value) &&
        sscanf(value, "%u.%u.%u.%u", &a, &b, &c, &d) == 4 && a < 256 && b < 256 && c < 256 && d < 256) {
        u->public_ip = (a << 24) | (b << 16) | (c << 8) | d;
        logf_("upnp: IP WAN del router = %u.%u.%u.%u%s", IP4(u->public_ip), ip_privada(u->public_ip) ? "  (PRIVADA: CGNAT o doble NAT)" : "");
    } else {
        logf_("upnp: el router no dio su IP WAN (error=%d)", err);
    }
    if (!u->local_ip) { logf_("upnp: no conozco la IP local, no abro el puerto"); return; }
    snprintf(ip, sizeof ip, "%u.%u.%u.%u", IP4(u->local_ip));
    for (;;) {
        snprintf(args, sizeof args,
                 "<NewRemoteHost></NewRemoteHost><NewExternalPort>%d</NewExternalPort><NewProtocol>TCP</NewProtocol>"
                 "<NewInternalPort>%d</NewInternalPort><NewInternalClient>%s</NewInternalClient><NewEnabled>1</NewEnabled>"
                 "<NewPortMappingDescription>SilverSky</NewPortMappingDescription><NewLeaseDuration>%d</NewLeaseDuration>",
                 port, port, ip, lease);
        status = upnp_soap("AddPortMapping", args, &err);
        if (err == 725 && lease != 0) { lease = 0; continue; }      /* el router solo acepta reglas permanentes */
        break;
    }
    u->http = status; u->error = err;
    if (status == 200) {
        u->opened = 1; g_upnp_added = 1; g_upnp_port = port;
    } else if (err == 718) {
        /* ya existia una regla: sirve si lleva a esta consola */
        snprintf(args, sizeof args,
                 "<NewRemoteHost></NewRemoteHost><NewExternalPort>%d</NewExternalPort><NewProtocol>TCP</NewProtocol>", port);
        u->opened = upnp_soap("GetSpecificPortMappingEntry", args, &err) == 200 &&
                    x_tag(g_ubuf, "NewInternalClient", value, sizeof value) && !strcmp(value, ip);
    }
    logf_("upnp: AddPortMapping TCP %d -> %s: http=%d error=%d abierto=%d", port, ip, status, u->error, u->opened);
}

/* Quita la regla que puso upnp_open (si puso alguna) */
static void upnp_close(void)
{
    char args[256];
    int err = 0;
    if (!g_upnp_added) return;
    g_upnp_added = 0;
    snprintf(args, sizeof args,
             "<NewRemoteHost></NewRemoteHost><NewExternalPort>%d</NewExternalPort><NewProtocol>TCP</NewProtocol>", g_upnp_port);
    upnp_soap("DeletePortMapping", args, &err);
    logf_("upnp: regla del puerto %d quitada del router (error=%d)", g_upnp_port, err);
}

/* v1.9.1: Codigo = IP publica del host como numero, en decimal de 10 digitos (con ceros a la izquierda).
 * El puerto ya NO viaja en el codigo: los dos usan el de config.txt (7777 por defecto). */
static void code_encode(uint32_t ip, int port, char *out)
{
    uint32_t v = ip;
    int i;
    (void)port;
    for (i = 9; i >= 0; i--) { out[i] = (char)('0' + (int)(v % 10)); v /= 10; }
    out[10] = 0;
}

static int code_decode(const char *code, uint32_t *ip, int *port)
{
    uint64_t v = 0;
    int i, n = 0;
    for (i = 0; code[i]; i++) {
        if (code[i] < '0' || code[i] > '9') continue;     /* ignora espacios y guiones */
        v = v * 10 + (uint64_t)(code[i] - '0');
        n++;
        if (n > 10) return 0;
    }
    if (n != 10 || v >= (1ULL << 32)) return 0;
    *ip = (uint32_t)v;
    *port = g_cfg.port;
    return *port > 0 && *ip != 0;
}

/* "1234567890" -> "123 456 7890" (solo para mostrarlo en pantalla) */
static void code_pretty(const char *code, char *out)
{
    int i, k = 0;
    for (i = 0; code[i] && i < 10; i++) {
        if (i == 3 || i == 6) out[k++] = ' ';
        out[k++] = code[i];
    }
    out[k] = 0;
}

/* ------------------------------------------------------------------ */
/* Handshake                                                           */
/* ------------------------------------------------------------------ */
static int cmp_u32(const void *a, const void *b)
{
    uint32_t x = *(const uint32_t *)a, y = *(const uint32_t *)b;
    return x < y ? -1 : x > y;
}

static int clamp_i(int v, int lo, int hi) { return v < lo ? lo : v > hi ? hi : v; }



/* v1.8: COPIA de handshake_host / handshake_client para el modo de 4 (protocolo PROTO_VER4). Misma logica. */
static int handshake_host4(int *outD)
{
    Msg m;
    uint32_t rtt[5];
    int i, D, r;

    r = net_recv(&m, 10000);
    if (r <= 0 || m.type != M_HELLO) { g_err = "EL AMIGO NO RESPONDIO"; return 0; }
    if (m.frame != (uint32_t)g_proto) {
        memset(&m, 0, sizeof m); m.type = M_REJECT; m.v1 = 1; net_send(&m);
        g_err = "AMIGO EN OTRO MODO O VERSION DISTINTA"; return 0;
    }
    if (m.v1 != g_romcrc) {
        memset(&m, 0, sizeof m); m.type = M_REJECT; m.v1 = 2; net_send(&m);
        g_err = "ROM DISTINTA A LA DEL AMIGO"; return 0;
    }
    memset(&m, 0, sizeof m); m.type = M_HELLO; m.frame = (uint32_t)g_proto; m.v1 = g_romcrc;
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }

    for (i = 0; i < 5; i++) {
        uint32_t t0 = now_ms();
        memset(&m, 0, sizeof m); m.type = M_PING; m.v1 = (uint32_t)i;
        if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
        r = net_recv(&m, 5000);
        if (r <= 0 || m.type != M_PONG || m.v1 != (uint32_t)i) { g_err = "FALLO LA MEDICION DE LATENCIA"; return 0; }
        rtt[i] = now_ms() - t0;
    }
    qsort(rtt, 5, sizeof rtt[0], cmp_u32);
    D = g_cfg.delay > 0 ? g_cfg.delay : clamp_i((int)((rtt[2] / 2 + 16) / 17) + 2, 3, 12);
    logf_("RTT mediana %u ms -> delay %d frames", (unsigned)rtt[2], D);

    memset(&m, 0, sizeof m); m.type = M_CFG; m.v1 = (uint32_t)D; m.v2 = rtt[2];
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
    memset(&m, 0, sizeof m); m.type = M_START;
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
    *outD = D;
    return 1;
}

static int handshake_client4(int *outD)
{
    Msg m;
    int r, D = 0, haveD = 0;
    uint32_t t0;

    memset(&m, 0, sizeof m); m.type = M_HELLO; m.frame = (uint32_t)g_proto; m.v1 = g_romcrc;
    if (!net_send(&m)) { g_err = "SE CORTO LA CONEXION"; return 0; }
    r = net_recv(&m, 10000);
    if (r <= 0) { g_err = "EL HOST NO RESPONDIO"; return 0; }
    if (m.type == M_REJECT) { g_err = (m.v1 == 2) ? "ROM DISTINTA A LA DEL HOST" : "ESA SALA NO ES DE SILVERSKY (O VERSION DISTINTA)"; return 0; }
    if (m.type != M_HELLO) { g_err = "RESPUESTA INVALIDA DEL HOST"; return 0; }

    t0 = now_ms();
    while (now_ms() - t0 < 20000) {
        r = net_recv(&m, 2000);
        if (r < 0) { g_err = "SE CORTO LA CONEXION"; return 0; }
        if (r == 0) continue;
        if (m.type == M_PING) {
            Msg p; memset(&p, 0, sizeof p); p.type = M_PONG; p.v1 = m.v1;
            if (!net_send(&p)) { g_err = "SE CORTO LA CONEXION"; return 0; }
        } else if (m.type == M_CFG) {
            D = (int)m.v1; haveD = 1;
        } else if (m.type == M_START && haveD) {
            *outD = clamp_i(D, 1, 20);
            return 1;
        }
    }
    g_err = "TIEMPO AGOTADO EN EL INICIO";
    return 0;
}

/* ------------------------------------------------------------------ */
/* Bucle de partida                                                    */
/* ------------------------------------------------------------------ */
static uint32_t g_run_hash, g_frames_done;
static uint32_t g_maxframes;              /* 0 = sin limite (solo la version de pruebas lo usa) */
static int      g_desyncs;
static uint32_t g_first_desync;


/* v1.7: mini menu de salida (se abre con R2). Devuelve 1 si confirma salir (X), 0 si sigue jugando (O).
 * Dibuja encima de la imagen del juego y la restaura al cerrar. */
static uint32_t g_fb_save[SCR_W * SCR_H];

static int exit_menu(int online) __attribute__((unused));
static int exit_menu(int online)
{
    int r = -1, x, y;
    memcpy(g_fb_save, g_fb, sizeof g_fb);
    g_stage = "menu-salir";
    ui_prime();
    while (g_running && r < 0) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_OK) r = 1;
        else if (e & UI_CANCEL) r = 0;
        for (y = 76; y < 164; y++)
            for (x = 20; x < 236; x++)
                g_fb[y * SCR_W + x] = (y < 78 || y >= 162 || x < 22 || x >= 234) ? 0xFFFFFFFF : 0xFF101838;
        ui_center(90, "SALIR DE LA PARTIDA?", 1, 0xFFFFFFFF);
        ui_center(116, "X: SI      O: NO", 1, 0xFFFFD040);
        if (online) ui_center(138, "TERMINA LA PARTIDA PARA LOS DOS", 1, 0xFFFFC040);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    memcpy(g_fb, g_fb_save, sizeof g_fb);
    g_stage = "juego";
    return r == 1;
}

enum { MK_CONT, MK_SAVE, MK_LOAD, MK_RESET, MK_EXIT };

/* ---- v0.3.0: menu en partida (R3) a 1280x720: el cuadro del juego queda atenuado al fondo ---- */
static void hr_alt_build(void)
{
    static int cm[960];
    int x, y;
    memcpy(g_hr_alt, g_hr_sky, sizeof g_hr_alt);
    for (x = 0; x < 960; x++) cm[x] = x * SCR_W / 960;
    for (y = 0; y < HR_H; y++) {
        const uint32_t *src = g_fb_save + (y * SCR_H / HR_H) * SCR_W;
        uint32_t *d = &g_hr_alt[y * HR_W + 160];
        for (x = 0; x < 960; x++) {
            uint32_t p = src[cm[x]];
            d[x] = 0xFF000000u | ((((p >> 16) & 255) * 105 / 255) << 16) | ((((p >> 8) & 255) * 105 / 255) << 8) | (((p & 255) * 105 / 255));
        }
    }
}

static void hr_solo_draw(const int *kinds, int nk, int sel, int confirm, int online, const char *note, const int *ex)
{
    int i;
    memcpy(g_hr, g_hr_alt, sizeof g_hr);
    g_hr_on = 1;
    if (confirm >= 0) {
        char t[64];
        const char *b = NULL, *c = NULL;
        uint32_t bc = HC_DIM, cc = HC_DIM;
        if (confirm == MK_RESET) {
            snprintf(t, sizeof t, "¿Reiniciar el juego?");
            if (online) { b = "Se reinicia para los dos"; bc = HC_WARN; } else b = "Lo guardado no se borra";
        } else if (confirm == MK_EXIT) {
            snprintf(t, sizeof t, "¿Salir de la partida?");
            if (online) { b = "Termina la partida para los dos"; bc = HC_WARN; }
        } else if (confirm == MK_SAVE) {
            snprintf(t, sizeof t, "¿Sobrescribir la ranura %d?", g_state_slot + 1);
        } else {
            snprintf(t, sizeof t, "¿Cargar la ranura %d?", g_state_slot + 1);
            b = online ? "Se pierde lo que llevan los dos" : "Se pierde lo que llevas"; bc = HC_WARN;
            if (online) { c = "Se envía al amigo (tarda unos segundos)"; cc = HC_DIM; }
        }
        hr_card(380, 220, 520, 240, 26, 0);
        hr_text(HF_OB19, 640, 290, t, HC_WHITE, "cm", 0);
        if (b) hr_text(HF_MS17, 640, 346, b, bc, "cm", 0);
        if (c) hr_text(HF_MS15, 640, 382, c, cc, "cm", 0);
        {
            HrBtn bt[2] = { { 0, "SÍ" }, { 1, "NO" } };
            hr_btns(bt, 2, NULL);
        }
        return;
    }
    {
        int h = 104 + (nk - 1) * 66 + 54 + 50, ty;
        hr_card(430, 130, 420, h, 26, 0);
        hr_text(HF_H1, 640, 176, "MENÚ", HC_SIL, "cm", 0);
        hr_line(520, 206, 760, 206, 3, HC_CY);
        for (i = 0; i < nk; i++) {
            char l[48];
            int y = 234 + i * 66;
            switch (kinds[i]) {
            case MK_CONT:  snprintf(l, sizeof l, "CONTINUAR"); break;
            case MK_SAVE:  snprintf(l, sizeof l, "GUARDAR ESTADO"); break;
            case MK_LOAD:  snprintf(l, sizeof l, "CARGAR ESTADO%s", ex[g_state_slot] ? "" : " (vacía)"); break;
            case MK_RESET: snprintf(l, sizeof l, "REINICIAR EL JUEGO"); break;
            default:       snprintf(l, sizeof l, "SALIR DE LA PARTIDA"); break;
            }
            hr_card(466, y, 348, 54, 12, i == sel);
            hr_text(i == sel ? HF_OB17 : HF_OM16, 640, y + 27, l, i == sel ? HC_WHITE : HC_SIL, "cm", 0);
        }
        ty = 234 + (nk - 1) * 66 + 54 + 28;
        if (note) hr_text(HF_MS15, 640, ty, note, HC_WARN, "cm", 0);
        else if (kinds[sel] == MK_SAVE || kinds[sel] == MK_LOAD) {
            char l[48];
            snprintf(l, sizeof l, "RANURA  %d / %d   (IZQ / DER)", g_state_slot + 1, STATE_SLOTS);
            hr_text(HF_OM13, 640, ty, l, HC_CY, "cm", 0);
        } else if (online) hr_text(HF_MS14, 640, ty, "Reiniciar y salir valen para los dos", HC_DIM, "cm", 0);
    }
    {
        HrBtn bt[2] = { { 0, "ACEPTAR" }, { 1, "CERRAR MENÚ" } };
        hr_btns(bt, 2, NULL);
    }
}


/* v1.9.1: menu de R2.
 *   SOLO:   CONTINUAR / GUARDAR ESTADO / CARGAR ESTADO / REINICIAR EL JUEGO / SALIR DE LA PARTIDA
 *   ONLINE: CONTINUAR / REINICIAR EL JUEGO / SALIR DE LA PARTIDA (reiniciar y salir valen para los dos; sin estados)
 * Reiniciar, salir, cargar y sobreescribir piden confirmar con X.
 * Devuelve 0 = seguir jugando, 1 = salir, 2 = reiniciar, 10+n = guardar en la ranura n, 20+n = cargar la ranura n (n = 0..2). */
/* v0.3.2: al cerrar el menu R3 (p. ej. la X de "si, cargar estado"), los BOTONES que sigan apretados no llegan al juego hasta
 * soltarlos (si no, el personaje salta al volver). Las flechas no se bloquean. Es solo entrada local: la red no cambia. */
static uint16_t g_swallow[2];
static int      g_swallow_arm;             /* bit 0 = mando 1, bit 1 = mando 2: armar en la proxima lectura */
static uint16_t swallow_filter(int port, uint16_t b)
{
    int p = port ? 1 : 0;
    if (g_swallow_arm & (1 << p)) { g_swallow[p] = (uint16_t)(b & ~(NB_UP | NB_DOWN | NB_LEFT | NB_RIGHT)); g_swallow_arm &= ~(1 << p); }
    g_swallow[p] &= b;
    return (uint16_t)(b & ~g_swallow[p]);
}

static int solo_menu_inner(int online, int host_states);
static int solo_menu(int online, int host_states)
{
    int r = solo_menu_inner(online, host_states);
    g_swallow_arm = 3;                      /* v0.3.2: al cerrar el menu, los botones que sigan apretados no llegan al juego */
    return r;
}
static int solo_menu_inner(int online, int host_states)
{
    int kinds[5], nk = 0, sel = 0, r = -1, confirm = -1, x, y, i;
    int st = !online || host_states;          /* v0.2.7: online, solo el HOST ve guardar/cargar estado */
    uint32_t ka = now_ms();
    int ex[STATE_SLOTS];
    const char *note = NULL;
    kinds[nk++] = MK_CONT;
    if (st) { kinds[nk++] = MK_SAVE; kinds[nk++] = MK_LOAD; }
    kinds[nk++] = MK_RESET; kinds[nk++] = MK_EXIT;
    for (i = 0; i < STATE_SLOTS; i++) ex[i] = st ? state_exists(i) : 0;
    memcpy(g_fb_save, g_fb, sizeof g_fb);
    if (hr_usable()) hr_alt_build();
    g_stage = "menu-solo";
    ui_prime();
    while (g_running && r < 0) {
        uint16_t e;
        int k;
        pump();
        if (online && g_net >= 0 && (uint32_t)(now_ms() - ka) >= 2000) {
            /* v0.2.7: con el menu abierto el otro lado esperaria mi entrada; un "sigo aqui" cada 2 s evita que se rinda a los 15 s */
            Msg kp;
            memset(&kp, 0, sizeof kp);
            kp.type = M_PING;
            net_send(&kp);
            ka = now_ms();
        }
        e = ui_edges();
        if (confirm >= 0) {
            if (e & UI_OK) {
                if (confirm == MK_RESET) r = 2;
                else if (confirm == MK_EXIT) r = 1;
                else if (confirm == MK_SAVE) r = 10 + g_state_slot;
                else r = 20 + g_state_slot;
            } else if (e & UI_CANCEL) confirm = -1;
        } else {
            if (e & UI_UP)   { sel = (sel + nk - 1) % nk; note = NULL; }
            if (e & UI_DOWN) { sel = (sel + 1) % nk; note = NULL; }
            k = kinds[sel];
            if ((k == MK_SAVE || k == MK_LOAD) && (e & (UI_LEFT | UI_RIGHT))) {
                g_state_slot = (g_state_slot + ((e & UI_RIGHT) ? 1 : STATE_SLOTS - 1)) % STATE_SLOTS;
                note = NULL;
            }
            if (e & UI_CANCEL) r = 0;
            else if (e & (UI_OK | UI_START)) {
                if (k == MK_CONT) r = 0;
                else if (k == MK_SAVE) { if (ex[g_state_slot]) confirm = MK_SAVE; else r = 10 + g_state_slot; }
                else if (k == MK_LOAD) { if (ex[g_state_slot]) confirm = MK_LOAD; else note = "ESA RANURA ESTA VACIA"; }
                else confirm = k;
            }
        }
if (hr_usable()) {
            hr_solo_draw(kinds, nk, sel, confirm, online, note, ex);
        } else {
                for (y = 46; y < 198; y++)
            for (x = 20; x < 236; x++)
                g_fb[y * SCR_W + x] = (y < 48 || y >= 196 || x < 22 || x >= 234) ? 0xFFFFFFFF : 0xFF101838;
        if (confirm >= 0) {
            char l[40];
            if (confirm == MK_RESET) {
                ui_center(88, "REINICIAR EL JUEGO?", 1, 0xFFFFFFFF);
                ui_center(108, online ? "SE REINICIA PARA LOS DOS" : "LO GUARDADO NO SE BORRA", 1, online ? 0xFFFFC040 : 0xFFC0C0FF);
            } else if (confirm == MK_EXIT) {
                ui_center(88, "SALIR DE LA PARTIDA?", 1, 0xFFFFFFFF);
                if (online) ui_center(108, "TERMINA LA PARTIDA PARA LOS DOS", 1, 0xFFFFC040);
            } else if (confirm == MK_SAVE) {
                snprintf(l, sizeof l, "SOBREESCRIBIR LA RANURA %d?", g_state_slot + 1);
                ui_center(88, l, 1, 0xFFFFFFFF);
            } else {
                snprintf(l, sizeof l, "CARGAR LA RANURA %d?", g_state_slot + 1);
                ui_center(88, l, 1, 0xFFFFFFFF);
                ui_center(108, online ? "SE PIERDE LO QUE LLEVAN LOS DOS" : "SE PIERDE LO QUE LLEVAS", 1, 0xFFFFC040);
                if (online) ui_center(120, "SE ENVIA AL AMIGO (TARDA UNOS SEGUNDOS)", 1, 0xFFC0C0FF);
            }
            ui_center(136, "X: SI      O: NO", 1, 0xFFFFD040);
        } else {
            ui_center(56, "MENU", 1, 0xFFFFD040);
            for (i = 0; i < nk; i++) {
                char l[48];
                switch (kinds[i]) {
                case MK_CONT:  snprintf(l, sizeof l, "%s", "CONTINUAR"); break;
                case MK_SAVE:  snprintf(l, sizeof l, "GUARDAR ESTADO < %d >", g_state_slot + 1); break;
                case MK_LOAD:  snprintf(l, sizeof l, "CARGAR ESTADO < %d >%s", g_state_slot + 1, ex[g_state_slot] ? "" : " (VACIA)"); break;
                case MK_RESET: snprintf(l, sizeof l, "%s", "REINICIAR EL JUEGO"); break;
                default:       snprintf(l, sizeof l, "%s", "SALIR DE LA PARTIDA"); break;
                }
                {
                    char l2[56];
                    snprintf(l2, sizeof l2, "%s %s", i == sel ? ">" : " ", l);
                    ui_center(76 + i * 16, l2, 1, i == sel ? 0xFFFFFFFF : 0xFF8080A0);
                }
            }
            if (note) ui_center(158, note, 1, 0xFFFFC040);
            ui_center(172, "ARRIBA/ABAJO + X   O: SEGUIR", 1, 0xFF8080A0);
            if (kinds[sel] == MK_SAVE || kinds[sel] == MK_LOAD) ui_center(184, "IZQ/DER: CAMBIAR DE RANURA", 1, 0xFF8080A0);
            else if (online) ui_center(184, "REINICIAR Y SALIR: PARA LOS DOS", 1, 0xFF8080A0);
        }
}
                present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    memcpy(g_fb, g_fb_save, sizeof g_fb);
    g_stage = "juego";
    return r < 0 ? 0 : r;
}

/* role: 0 = host (P1), 1 = cliente (P2), -1 = local directo (2 mandos),
 *       -2 = referencia de pruebas: local con el mismo retraso D     */
/* v1.9: info de red en partida (solo dibujo; no toca la red). Mide cuanto tarda cada cuadro: si el juego tiene que
 * esperar al otro lado, el cuadro tarda mas de 24 ms (a 60 cuadros por segundo lo normal son 17 ms). */
static uint32_t g_ni_last, g_ni_t0, g_ni_n, g_ni_stall, g_ni_fps, g_ni_st;

static void netinfo_tick(void)
{
    uint32_t now = now_ms();
    if (g_ni_last && now - g_ni_last > 24 && now - g_ni_last < 1000) g_ni_stall++;   /* >1 s = menu abierto, no cuenta */
    g_ni_last = now;
    g_ni_n++;
    if (g_ni_t0 == 0 || now - g_ni_t0 >= 1000) {
        if (g_ni_t0) { g_ni_fps = g_ni_n; g_ni_st = g_ni_stall; }
        g_ni_n = 0; g_ni_stall = 0; g_ni_t0 = now;
    }
}

static int netinfo_show(uint32_t frame)
{
    if (g_desyncs) return 1;                 /* el aviso rojo de desync siempre sale */
    if (g_netinfo == 2) return 0;
    if (g_netinfo == 1) return 1;
    return frame < 300;                      /* por defecto: como siempre, los primeros ~5 s */
}

/* v1.9.1: reinicios sincronizados. Quien pide reiniciar manda M_RESET con frame = F (= su cuadro actual + D) ANTES de su
 * entrada de ese cuadro; por el orden del TCP el otro lado lo lee antes de poder pasar del cuadro F, asi los dos llaman a
 * retro_reset() justo antes de emular el cuadro F. Si piden los dos a la vez, cada reinicio tiene su propio F. */
#define RST_MAX 4
static void rst_add(uint32_t *rst, uint32_t f)
{
    int k;
    for (k = 0; k < RST_MAX; k++) if (rst[k] == f) return;
    for (k = 0; k < RST_MAX; k++) if (rst[k] == NO_FRAME) { rst[k] = f; return; }
}
static int rst_due(uint32_t *rst, uint32_t frame)
{
    int k, due = 0;
    for (k = 0; k < RST_MAX; k++) if (rst[k] == frame) { rst[k] = NO_FRAME; due = 1; }
    return due;
}
#ifdef NESNET_HOST
static uint32_t g_ref_reset[2] = { NO_FRAME, NO_FRAME };   /* pruebas: cuadros en que la referencia reinicia (NESNET_RESET_REF=a,b) */
#endif


/* ------------------------------------------------------------------ */
/* Bucle de partida (SOLO y 2 vs 2)                                    */
/* Cada consola manda en un solo mensaje sus 2 mandos (v3: 16 bits bajos = mando 1 de esa consola, 16 altos = mando 2).  */
/* Host: jugadores 1 y 2. El que se une: jugadores 3 y 4.                                                              */
/* ------------------------------------------------------------------ */
static uint32_t local_bits_pair(int role, uint32_t frame)
{
#ifdef NESNET_HOST
    int base = role == 1 ? 2 : 0;           /* pruebas: host = jugadores 0 y 1, cliente = jugadores 2 y 3 */
    return (uint32_t)swallow_filter(0, script_input(base, frame)) | ((uint32_t)swallow_filter(1, script_input(base + 1, frame)) << 16);
#else
    (void)role; (void)frame;
    return (uint32_t)swallow_filter(0, pad_nes_bits(0)) | ((uint32_t)swallow_filter(1, pad_nes_bits(1)) << 16);
#endif
}

/* role: 0 = host (P1+P2), 1 = el que se une (P3+P4), -1 = SOLO (2 mandos locales, sin red),
 *       -2 = referencia de pruebas: 4 jugadores locales con retraso D */
static int session_loop(int role, int D, uint32_t maxframes)
{
    uint32_t loc[RING], rem[RING];
    uint8_t  have[RING];
    uint32_t mine_f[RING], mine_c[RING], rem_f[RING], rem_c[RING];
    uint32_t frame = 0, last_rx = now_ms();
    uint32_t rst[RST_MAX];
    int i, ended_ok = 1, peer_gone = 0, peer_quit = 0, user_exit = 0;
    char ov[64];
    /* v0.2.7: estado guardado pendiente de cargar en el cuadro st_in_F (el host lo lee de su ranura; el invitado lo recibe por red) */
    uint8_t *st_in = NULL;
    size_t st_in_n = 0;
    uint32_t st_in_F = NO_FRAME;
    const char *stage0;

    memset(loc, 0, sizeof loc); memset(rem, 0, sizeof rem); memset(have, 0, sizeof have);
    for (i = 0; i < RING; i++) { mine_f[i] = NO_FRAME; rem_f[i] = NO_FRAME; mine_c[i] = rem_c[i] = 0; }
    for (i = 0; i < RST_MAX; i++) rst[i] = NO_FRAME;
    if (role >= 0) for (i = 0; i < D; i++) have[i] = 1;

    g_run_hash = 2166136261u; g_frames_done = 0; g_desyncs = 0; g_first_desync = NO_FRAME;
    g_stage = role == 0 ? "juego-host" : role == 1 ? "juego-cliente" : role == -1 ? "juego-solo" : "juego-ref";
    stage0 = g_stage;
    g_hash_on = (role != -1);               /* v0.2.2: el hash por imagen solo se calcula online (o en la sesion de referencia) */
    g_ingame = 1;                           /* v0.2.6: desde aqui la imagen usa la pantalla elegida en OPCIONES */
    logf_("sesion: rol=%d hash_por_imagen=%s", role, g_hash_on ? "si" : "no (solo)");
    pf_window_reset();
    sk_reset();

#define COMPARE(f) do { uint32_t _f = (f); \
        if (mine_f[_f % RING] == _f && rem_f[_f % RING] == _f && \
            mine_c[_f % RING] != rem_c[_f % RING]) { \
            if (!g_desyncs) { g_first_desync = _f; logf_("DESYNC en frame %u", (unsigned)_f); } \
            g_desyncs++; \
            mine_f[_f % RING] = NO_FRAME; } } while (0)

    (void)exit_pressed(1, 0);               /* ignora un R2 que siga apretado desde antes */

    while (g_running && (maxframes == 0 || frame < maxframes)) {
        uint16_t p1, p2, p3, p4;
        unsigned long long tf0 = now_us(), tfp;
        pump();
        tfp = now_us();
        pf_pump_cur = tfp - tf0;

        /* R3 del mando 1 de esta consola abre el menu: SOLO = continuar / guardar y cargar estado / reiniciar / salir;
         * online = continuar / reiniciar / salir (reiniciar y salir valen para los dos). Se mira antes de mandar la
         * entrada de este cuadro; si el menu sigue abierto, el otro lado simplemente espera como siempre. */
        if (role != -2 && exit_pressed(0, frame) && !(st_in && st_in_F > frame)) {   /* v0.2.7: con un estado por cargarse en unos cuadros no se abre el menu */
            int xr = solo_menu(role >= 0, role == 0);
            if (xr == 1) { user_exit = 1; logf_("salida pedida por el jugador (R2) en frame %u", (unsigned)frame); goto out; }
            if (xr == 2) {
                if (role >= 0) {
                    Msg rq;
                    uint32_t F = frame + (uint32_t)D;
                    memset(&rq, 0, sizeof rq); rq.type = M_RESET; rq.frame = F;
                    if (!peer_gone && !net_send(&rq)) peer_gone = 1;
                    rst_add(rst, F);
                    logf_("reinicio pedido por el jugador (R2) en frame %u: los dos reinician en el frame %u", (unsigned)frame, (unsigned)F);
                } else {
                    retro_reset();
                    logf_("juego reiniciado por el jugador (R2) en frame %u", (unsigned)frame);
                }
            } else if (xr >= 10 && xr < 10 + STATE_SLOTS && (role == -1 || role == 0)) {   /* v0.2.7: el host tambien guarda en ONLINE (solo escribe su ranura: no toca la partida) */
                char tb[40];
                snprintf(tb, sizeof tb, state_save(xr - 10) ? "ESTADO GUARDADO EN RANURA %d" : "NO SE PUDO GUARDAR (RANURA %d)", xr - 9);
                toast(tb);
            } else if (xr >= 20 && xr < 20 + STATE_SLOTS && role == -1) {
                char tb[40];
                int lr = state_load(xr - 20);
                snprintf(tb, sizeof tb, lr > 0 ? "ESTADO CARGADO: RANURA %d" : "NO SE PUDO CARGAR (RANURA %d)", xr - 19);
                toast(tb);
            } else if (xr >= 20 && xr < 20 + STATE_SLOTS && role == 0) {
                /* v0.2.7: el host carga un estado EN ONLINE. Se lo manda al invitado (M_STATE + datos) ANTES de su entrada de este cuadro y los
                 * dos lo cargan justo antes de emular el cuadro F = frame + D (mismo truco que el reinicio sincronizado). Mientras llegan
                 * los datos los dos esperan (el juego se detiene unos segundos); no se pierde ni se adelanta ningun cuadro. */
                uint8_t *sb = NULL;
                size_t sn = 0;
                char tb[40];
                if (!state_read(xr - 20, &sb, &sn)) {
                    snprintf(tb, sizeof tb, "NO SE PUDO CARGAR (RANURA %d)", xr - 19);
                    toast(tb);
                } else {
                    uint32_t F = frame + (uint32_t)D, t0 = now_ms();
                    Msg rq;
                    memset(&rq, 0, sizeof rq);
                    rq.type = M_STATE; rq.frame = F; rq.v1 = (uint32_t)sn; rq.v2 = crc32_buf(sb, sn);
                    g_stage = "enviando-estado";
                    if (!peer_gone && (!net_send(&rq) || !net_send_raw(sb, sn))) peer_gone = 1;
                    g_stage = stage0;
                    logf_("estado: ranura %d (%u bytes, crc %08X) enviado en %u ms; los dos lo cargan en el frame %u (pedido en el %u)",
                          xr - 19, (unsigned)sn, (unsigned)rq.v2, (unsigned)(now_ms() - t0), (unsigned)F, (unsigned)frame);
                    free(st_in);
                    st_in = sb; st_in_n = sn; st_in_F = F;
                }
            }
            last_rx = now_ms();
            pf_cur_reset(); tf0 = now_us();       /* el tiempo con el menu abierto no cuenta */
            sk_reset();
        }

        if (role == -1) {
            uint32_t b = local_bits_pair(0, frame);
            p1 = (uint16_t)(b & 0xFFFF); p2 = (uint16_t)(b >> 16); p3 = p4 = 0;
        } else if (role == -2) {
#ifdef NESNET_HOST
            uint32_t f0 = frame >= (uint32_t)D ? frame - (uint32_t)D : 0;
            int ok0 = frame >= (uint32_t)D;
            p1 = ok0 ? script_input(0, f0) : 0;
            p2 = ok0 ? script_input(1, f0) : 0;
            p3 = ok0 ? script_input(2, f0) : 0;
            p4 = ok0 ? script_input(3, f0) : 0;
#else
            p1 = p2 = p3 = p4 = 0;           /* la referencia solo existe en la version de pruebas (PC) */
#endif
        } else {
            Msg m;
            uint32_t tgt = frame + (uint32_t)D;
            uint32_t bits = local_bits_pair(role, frame);
            unsigned long long tn0 = now_us();
            loc[tgt % RING] = bits;

            memset(&m, 0, sizeof m);
            m.type = M_INPUT; m.v3 = bits; m.frame = tgt;
            if (frame > 0) { m.v1 = frame - 1; m.v2 = mine_c[(frame - 1) % RING]; } else { m.v1 = NO_FRAME; }
            if (!peer_gone && !net_send(&m)) peer_gone = 1;   /* lo decide el bucle de espera */

            for (;;) {
                int r;
                if (peer_gone) {
                    /* el otro lado cerro: seguimos solo mientras queden entradas ya recibidas */
                    if (have[frame % RING]) break;
                    g_err = peer_quit ? "EL AMIGO SALIO DE LA PARTIDA" : "SE PERDIO LA CONEXION";
                    ended_ok = 0; goto out;
                }
                r = net_recv(&m, have[frame % RING] ? 0 : 100);
                if (r < 0) { if (!g_running) goto out; peer_gone = 1; continue; }
                if (r == 0) {
                    if (have[frame % RING]) break;
                    if (!g_running) goto out;
                    if (now_ms() - last_rx > 15000) { g_err = "EL AMIGO NO RESPONDE (15 S)"; ended_ok = 0; goto out; }
                    continue;
                }
                last_rx = now_ms();
                if (m.type == M_INPUT) {
                    rem[m.frame % RING] = m.v3;
                    have[m.frame % RING] = 1;
                    if (m.v1 != NO_FRAME) { rem_f[m.v1 % RING] = m.v1; rem_c[m.v1 % RING] = m.v2; COMPARE(m.v1); }
                } else if (m.type == M_STATE) {
                    /* v0.2.7: el host manda un estado guardado: lo recibo entero y lo cargo en el cuadro m.frame (nunca se pasa de largo:
                     * no puedo emular m.frame sin la entrada del host, que viene DESPUES de este mensaje). Si algo no cuadra, se termina
                     * la partida con aviso: cargar el estado en un solo lado la desincronizaria. */
                    uint8_t *sb;
                    if (m.v1 == 0 || m.v1 > STATE_MAX || (size_t)m.v1 != retro_serialize_size() || m.frame < frame) {
                        g_err = "ESTADO DEL HOST NO VALIDO"; ended_ok = 0; goto out;
                    }
                    sb = (uint8_t *)malloc(m.v1);
                    if (!sb) { g_err = "SIN MEMORIA PARA EL ESTADO"; ended_ok = 0; goto out; }
                    g_stage = "recibiendo-estado";
                    if (!net_recv_raw(sb, m.v1)) { free(sb); if (!g_running) goto out; peer_gone = 1; continue; }
                    g_stage = stage0;
                    if (crc32_buf(sb, m.v1) != m.v2) { free(sb); g_err = "ESTADO RECIBIDO CON ERRORES"; ended_ok = 0; goto out; }
                    free(st_in);
                    st_in = sb; st_in_n = m.v1; st_in_F = m.frame;
                    last_rx = now_ms();
                    logf_("estado recibido del host: %u bytes, crc %08X; lo cargo en el frame %u (voy en el %u)", (unsigned)m.v1, (unsigned)m.v2, (unsigned)m.frame, (unsigned)frame);
                } else if (m.type == M_RESET) {
                    rst_add(rst, m.frame);
                } else if (m.type == M_QUIT) {
                    peer_quit = 1; peer_gone = 1;
                }
            }
            pf_net_cur = now_us() - tn0;
            have[frame % RING] = 0;
            {
                uint32_t mine = loc[frame % RING], theirs = rem[frame % RING];
                uint32_t hb = (role == 0) ? mine : theirs;      /* mandos del host */
                uint32_t cb = (role == 0) ? theirs : mine;      /* mandos del que se une */
                if (g_one) {                                    /* v0.2: 1 vs 1: host = mando 1 (puerto 1), el que se une = mando 2 (puerto 2) */
                    p1 = (uint16_t)(hb & 0xFFFF); p2 = (uint16_t)(cb & 0xFFFF);
                    p3 = p4 = 0;
                } else {
                    p1 = (uint16_t)(hb & 0xFFFF); p2 = (uint16_t)(hb >> 16);
                    p3 = (uint16_t)(cb & 0xFFFF); p4 = (uint16_t)(cb >> 16);
                }
            }
        }

        /* reinicio sincronizado (o, en las pruebas de PC, el de la referencia) justo antes de emular este cuadro */
        {
            int due = rst_due(rst, frame);
#ifdef NESNET_HOST
            if (role == -2 && (frame == g_ref_reset[0] || frame == g_ref_reset[1])) due = 1;
#endif
            if (due) { retro_reset(); logf_("reinicio aplicado en el frame %u", (unsigned)frame); }
        }
        if (st_in && st_in_F == frame) {                  /* v0.2.7: estado del host (el mismo bloque en los dos lados) justo antes de este cuadro */
            int okl = retro_unserialize(st_in, st_in_n) ? 1 : 0;
            logf_("estado cargado en el frame %u: %u bytes, crc %08X %s", (unsigned)frame, (unsigned)st_in_n, (unsigned)crc32_buf(st_in, st_in_n), okl ? "OK" : "FALLO");
            toast(role == 0 ? (okl ? "ESTADO CARGADO" : "NO SE PUDO CARGAR") : "EL HOST CARGO UN ESTADO");
            free(st_in);
            st_in = NULL; st_in_n = 0; st_in_F = NO_FRAME;
        }

#ifdef NESNET_HOST
        { const char *b = getenv("NESNET_BREAK");        /* prueba: corrompe a proposito un cuadro */
          if (b && role == 1 && frame >= (uint32_t)atoi(b) && frame < (uint32_t)atoi(b) + 30) p3 ^= 0xFFF; }
#endif
        step_frame4(p1, p2, p3, p4);

        mine_f[frame % RING] = frame;
        mine_c[frame % RING] = g_frame_crc;
        if (role >= 0) COMPARE(frame);
        g_run_hash = fnv_u32(g_run_hash, g_frame_crc);

        if (role >= 0 && netinfo_show(frame)) {
            if (g_desyncs) snprintf(ov, sizeof ov, "DESYNC EN FRAME %u", (unsigned)g_first_desync);
            else if (g_netinfo == 1) snprintf(ov, sizeof ov, "%s %s DELAY %d (%dMS) FPS %u TRABAS %u", g_one ? "1V1" : "2V2", g_one ? (role == 0 ? "P1" : "P2") : (role == 0 ? "P1+P2" : "P3+P4"), D, D * 17, (unsigned)g_ni_fps, (unsigned)g_ni_st);
            else snprintf(ov, sizeof ov, "SILVERSKY %s  %s  DELAY %d", g_one ? "1V1" : "2V2", g_one ? (role == 0 ? "P1" : "P2") : (role == 0 ? "P1+P2" : "P3+P4"), D);
            ui_text(2, 2, ov, 1, g_desyncs ? 0xFFFF4040 : 0xFFFFFFFF);
        }
        if (g_toast_n > 0) { ui_text(4, 224, g_toast, 1, 0xFFFFFF40); g_toast_n--; }
        {
            /* v0.2.5: si va atrasado, este cuadro no se dibuja (ver sk_should_skip); todo lo demas del cuadro ya se hizo */
            unsigned long long tn = now_us(), part = tn - tf0, tt, idle, wk, drew;
            int skipped;
            part = part > pf_net_cur ? part - pf_net_cur : 0;
            skipped = sk_should_skip(part);
            if (skipped) { g_stage = "ok"; heartbeat(); } else present();
            tn = now_us();
            tt = tn - tf0; idle = pf_wait_cur + pf_net_cur;
            wk = tt > idle ? tt - idle : 0;
            drew = pf_draw_cur > pf_wait_cur ? pf_draw_cur - pf_wait_cur : 0;
            sk_account(wk, drew, skipped);
        }
        pf_frame_end(tf0);
        if (role >= 0 && g_netinfo == 1) netinfo_tick();
        frame++;
        g_frames_done = frame;
        if (role == -1 && (frame % 300) == 0) sram_save(0);      /* guardado de bateria cada ~5 s si cambio (solo SOLO) */
    }
out:
    g_ingame = 0;                           /* v0.2.6: al salir de la partida, los menus vuelven a MENU_SCREEN */
    free(st_in);                            /* v0.2.7: estado pendiente que nunca llego a cargarse */
    st_in = NULL;
    if (role >= 0 && g_net >= 0) {
        Msg q; memset(&q, 0, sizeof q); q.type = M_QUIT; net_send(&q);
        if (user_exit) {
            /* vacia lo que el otro lado alcance a mandar (hasta 300 ms o hasta que cierre), para que
             * al cerrar el socket no se pierda el aviso de salida (cerrar con datos sin leer lo descarta) */
            uint32_t t0 = now_ms();
            while (now_ms() - t0 < 300) { if (net_recv(&q, 20) < 0) break; }
        }
    }
#undef COMPARE
#ifdef NESNET_HOST
    if (getenv("NESNET_RAMDUMP")) {            /* prueba: lo que el juego leyo de los mandos (RAM $20-$2F, ver mkrom.py) */
        const uint8_t *ram = (const uint8_t *)retro_get_memory_data(RETRO_MEMORY_SYSTEM_RAM);
        if (ram) {
            int k;
            printf("RAM role=%d auto:", role);
            for (k = 0x20; k < 0x30; k++) printf(" %02X", ram[k]);
            printf(" | manual par:");
            for (k = 0x40; k < 0x46; k++) printf(" %02X", ram[k]);
            printf(" impar:");
            for (k = 0x48; k < 0x4E; k++) printf(" %02X", ram[k]);
            printf("\n");
        }
    }
#endif
    return ended_ok;
}

/* ------------------------------------------------------------------ */
/* Interfaz                                                            */
/* ------------------------------------------------------------------ */
static void ui_show(const char *l1, const char *l2, const char *l3);
static void ui_message(const char *l1, const char *l2, int frames);
/* ------------------------------------------------------------------ */
/* v0.3.0: caratulas (PNG propio: inflate + filtros) y pantallas a 1280x720                                          */
/* ------------------------------------------------------------------ */
typedef struct { const uint8_t *s; size_t n, p; uint32_t bb; int bc; uint8_t *o; size_t on, oc; int err; } HrInf;
typedef struct { uint16_t cnt[16]; uint16_t sym[288]; } HrHuf;

static int hr_inf_bits(HrInf *z, int n)
{
    int v;
    while (z->bc < n) {
        if (z->p >= z->n) { z->err = 1; return 0; }
        z->bb |= (uint32_t)z->s[z->p++] << z->bc;
        z->bc += 8;
    }
    v = (int)(z->bb & ((1u << n) - 1u));
    z->bb >>= n; z->bc -= n;
    return v;
}

static void hr_huf_build(HrHuf *h, const uint8_t *len, int n)
{
    int i, off[16];
    memset(h->cnt, 0, sizeof h->cnt);
    for (i = 0; i < n; i++) h->cnt[len[i]]++;
    h->cnt[0] = 0;
    off[1] = 0;
    for (i = 1; i < 15; i++) off[i + 1] = off[i] + h->cnt[i];
    for (i = 0; i < n; i++) if (len[i]) h->sym[off[len[i]]++] = (uint16_t)i;
}

static int hr_huf_dec(HrInf *z, const HrHuf *h)
{
    int code = 0, first = 0, index = 0, len;
    for (len = 1; len <= 15; len++) {
        int count;
        code |= hr_inf_bits(z, 1);
        if (z->err) return -1;
        count = h->cnt[len];
        if (code - count < first) return h->sym[index + (code - first)];
        index += count; first += count; first <<= 1; code <<= 1;
    }
    return -1;
}

static int hr_inf_codes(HrInf *z, const HrHuf *lc, const HrHuf *dc)
{
    static const uint16_t lb[29] = { 3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258 };
    static const uint8_t  le[29] = { 0,0,0,0,0,0,0,0,1,1,1,1,2,2,2,2,3,3,3,3,4,4,4,4,5,5,5,5,0 };
    static const uint16_t db[30] = { 1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577 };
    static const uint8_t  de[30] = { 0,0,0,0,1,1,2,2,3,3,4,4,5,5,6,6,7,7,8,8,9,9,10,10,11,11,12,12,13,13 };
    for (;;) {
        int sym = hr_huf_dec(z, lc);
        if (sym < 0 || z->err) return 0;
        if (sym < 256) {
            if (z->on >= z->oc) return 0;
            z->o[z->on++] = (uint8_t)sym;
        } else if (sym == 256) {
            return 1;
        } else {
            int len, dist, ds;
            size_t k;
            sym -= 257;
            if (sym >= 29) return 0;
            len = lb[sym] + hr_inf_bits(z, le[sym]);
            ds = hr_huf_dec(z, dc);
            if (ds < 0 || ds >= 30 || z->err) return 0;
            dist = db[ds] + hr_inf_bits(z, de[ds]);
            if (z->err || (size_t)dist > z->on || z->on + (size_t)len > z->oc) return 0;
            for (k = 0; k < (size_t)len; k++) { z->o[z->on] = z->o[z->on - (size_t)dist]; z->on++; }
        }
    }
}

/* zlib: 1 = bien (z->on bytes escritos) */
static int hr_inflate(const uint8_t *src, size_t n, uint8_t *out, size_t cap, size_t *outn)
{
    if (n < 2 || (src[0] & 15) != 8 || ((src[0] << 8) | src[1]) % 31 != 0 || (src[1] & 32)) return 0;
    return hr_inflate_raw(src + 2, n - 2, out, cap, outn);
}
/* v0.3.2: deflate "crudo" (sin la cabecera zlib): lo usan el PNG (via hr_inflate) y las ROMs en .zip. 1 = bien */
static int hr_inflate_raw(const uint8_t *src, size_t n, uint8_t *out, size_t cap, size_t *outn)
{
    HrInf z;
    static HrHuf lc, dc;
    int last;
    memset(&z, 0, sizeof z);
    z.s = src; z.n = n; z.o = out; z.oc = cap;
    do {
        int type;
        last = hr_inf_bits(&z, 1);
        type = hr_inf_bits(&z, 2);
        if (z.err) return 0;
        if (type == 0) {
            int len, nlen;
            z.bb = 0; z.bc = 0;
            if (z.p + 4 > z.n) return 0;
            len = z.s[z.p] | (z.s[z.p + 1] << 8);
            nlen = z.s[z.p + 2] | (z.s[z.p + 3] << 8);
            z.p += 4;
            if ((len ^ 0xFFFF) != nlen || z.p + (size_t)len > z.n || z.on + (size_t)len > z.oc) return 0;
            memcpy(z.o + z.on, z.s + z.p, (size_t)len);
            z.on += (size_t)len; z.p += (size_t)len;
        } else if (type == 1) {
            uint8_t l[320];
            int i;
            for (i = 0; i < 144; i++) l[i] = 8;
            for (; i < 256; i++) l[i] = 9;
            for (; i < 280; i++) l[i] = 7;
            for (; i < 288; i++) l[i] = 8;
            hr_huf_build(&lc, l, 288);
            for (i = 0; i < 30; i++) l[i] = 5;
            hr_huf_build(&dc, l, 30);
            if (!hr_inf_codes(&z, &lc, &dc)) return 0;
        } else if (type == 2) {
            static const uint8_t order[19] = { 16,17,18,0,8,7,9,6,10,5,11,4,12,3,13,2,14,1,15 };
            uint8_t l[320];
            int nlen = hr_inf_bits(&z, 5) + 257, ndist = hr_inf_bits(&z, 5) + 1, ncode = hr_inf_bits(&z, 4) + 4, i, idx;
            HrHuf cl;
            if (z.err || nlen > 286 || ndist > 30) return 0;
            memset(l, 0, sizeof l);
            for (i = 0; i < ncode; i++) l[order[i]] = (uint8_t)hr_inf_bits(&z, 3);
            if (z.err) return 0;
            hr_huf_build(&cl, l, 19);
            idx = 0;
            memset(l, 0, sizeof l);
            while (idx < nlen + ndist) {
                int sym = hr_huf_dec(&z, &cl);
                if (sym < 0 || z.err) return 0;
                if (sym < 16) l[idx++] = (uint8_t)sym;
                else {
                    int rep, prev = 0;
                    if (sym == 16) { if (idx == 0) return 0; prev = l[idx - 1]; rep = 3 + hr_inf_bits(&z, 2); }
                    else if (sym == 17) rep = 3 + hr_inf_bits(&z, 3);
                    else rep = 11 + hr_inf_bits(&z, 7);
                    if (idx + rep > nlen + ndist) return 0;
                    while (rep--) l[idx++] = (uint8_t)prev;
                }
            }
            hr_huf_build(&lc, l, nlen);
            hr_huf_build(&dc, l + nlen, ndist);
            if (!hr_inf_codes(&z, &lc, &dc)) return 0;
        } else return 0;
    } while (!last);
    *outn = z.on;
    return 1;
}

static int hr_paeth(int a, int b, int c)
{
    int p = a + b - c, pa = p > a ? p - a : a - p, pb = p > b ? p - b : b - p, pc = p > c ? p - c : c - p;
    return (pa <= pb && pa <= pc) ? a : (pb <= pc ? b : c);
}

static uint32_t hr_be32(const uint8_t *p) { return ((uint32_t)p[0] << 24) | ((uint32_t)p[1] << 16) | ((uint32_t)p[2] << 8) | p[3]; }

#define HR_PNG_MAXPIX (4u * 1024u * 1024u)
/* Decodifica un PNG (sin entrelazado). Devuelve NULL si salio bien (*pix = w*h ARGB, con malloc) o el motivo del fallo. */
static const char *hr_png_decode(const uint8_t *f, size_t fn, uint32_t **pix, int *pw, int *ph)
{
    size_t pos = 8, zn = 0, rawn = 0, rb, rawcap;
    uint8_t *z = NULL, *raw = NULL, pal[256][4];
    uint32_t w = 0, h = 0, y, x;
    int depth = 0, ct = -1, il = 0, have_hdr = 0, ch, bpp, npal = 0, i;
    uint32_t *out = NULL;
    const char *err = "PNG DANADO";
    memset(pal, 255, sizeof pal);
    *pix = NULL;
    if (fn < 33 || memcmp(f, "\x89PNG\r\n\x1a\n", 8)) return "NO ES UN PNG";
    z = (uint8_t *)malloc(fn);
    if (!z) return "SIN MEMORIA";
    while (pos + 12 <= fn) {
        uint32_t cl = hr_be32(f + pos);
        const uint8_t *tp = f + pos + 4, *cd = f + pos + 8;
        if ((size_t)cl > fn - pos - 12) { err = "PNG CORTADO"; goto fail; }
        if (!memcmp(tp, "IHDR", 4) && cl >= 13) {
            w = hr_be32(cd); h = hr_be32(cd + 4); depth = cd[8]; ct = cd[9]; il = cd[12];
            if (cd[10] != 0 || cd[11] != 0) { err = "PNG NO SOPORTADO"; goto fail; }
            have_hdr = 1;
        } else if (!memcmp(tp, "PLTE", 4)) {
            npal = (int)(cl / 3); if (npal > 256) npal = 256;
            for (i = 0; i < npal; i++) { pal[i][0] = cd[i * 3]; pal[i][1] = cd[i * 3 + 1]; pal[i][2] = cd[i * 3 + 2]; }
        } else if (!memcmp(tp, "tRNS", 4) && ct == 3) {
            for (i = 0; i < (int)cl && i < 256; i++) pal[i][3] = cd[i];
        } else if (!memcmp(tp, "IDAT", 4)) {
            memcpy(z + zn, cd, cl); zn += cl;
        } else if (!memcmp(tp, "IEND", 4)) break;
        pos += 12 + (size_t)cl;
    }
    if (!have_hdr || !zn) { err = "PNG INCOMPLETO"; goto fail; }
    if (il) { err = "PNG ENTRELAZADO NO SOPORTADO"; goto fail; }
    if (w < 1 || h < 1 || w > 8192 || h > 8192 || (uint64_t)w * h > HR_PNG_MAXPIX) { err = "IMAGEN MUY GRANDE"; goto fail; }
    switch (ct) {
    case 0: ch = 1; if (depth != 1 && depth != 2 && depth != 4 && depth != 8 && depth != 16) { err = "PNG NO SOPORTADO"; goto fail; } break;
    case 2: ch = 3; if (depth != 8 && depth != 16) { err = "PNG NO SOPORTADO"; goto fail; } break;
    case 3: ch = 1; if (depth != 1 && depth != 2 && depth != 4 && depth != 8) { err = "PNG NO SOPORTADO"; goto fail; } break;
    case 4: ch = 2; if (depth != 8 && depth != 16) { err = "PNG NO SOPORTADO"; goto fail; } break;
    case 6: ch = 4; if (depth != 8 && depth != 16) { err = "PNG NO SOPORTADO"; goto fail; } break;
    default: err = "PNG NO SOPORTADO"; goto fail;
    }
    rb = ((size_t)w * (size_t)ch * (size_t)depth + 7) / 8;
    bpp = (ch * depth + 7) / 8;
    rawcap = (rb + 1) * (size_t)h;
    raw = (uint8_t *)malloc(rawcap);
    out = (uint32_t *)malloc((size_t)w * h * 4);
    if (!raw || !out) { err = "SIN MEMORIA"; goto fail; }
    if (!hr_inflate(z, zn, raw, rawcap, &rawn) || rawn < rawcap) { err = "PNG DANADO"; goto fail; }
    free(z); z = NULL;
    for (y = 0; y < h; y++) {
        uint8_t *row = raw + (size_t)y * (rb + 1), *prev = y ? raw + (size_t)(y - 1) * (rb + 1) + 1 : NULL;
        int ft = row[0];
        size_t k;
        uint8_t *d = row + 1;
        if (ft > 4) { err = "PNG DANADO"; goto fail; }
        for (k = 0; k < rb; k++) {
            int a = k >= (size_t)bpp ? d[k - (size_t)bpp] : 0, b = prev ? prev[k] : 0, c = (prev && k >= (size_t)bpp) ? prev[k - (size_t)bpp] : 0, v = d[k];
            switch (ft) {
            case 1: v += a; break;
            case 2: v += b; break;
            case 3: v += (a + b) >> 1; break;
            case 4: v += hr_paeth(a, b, c); break;
            default: break;
            }
            d[k] = (uint8_t)v;
        }
        for (x = 0; x < w; x++) {
            int r, g, bl, al = 255;
            if (ct == 0 || ct == 3) {
                int idx;
                if (depth == 8) idx = d[x];
                else if (depth == 16) idx = d[x * 2];
                else idx = (d[(x * (uint32_t)depth) >> 3] >> (8 - depth - (int)((x * (uint32_t)depth) & 7))) & ((1 << depth) - 1);
                if (ct == 3) { r = pal[idx][0]; g = pal[idx][1]; bl = pal[idx][2]; al = pal[idx][3]; }
                else { if (depth < 8) idx = idx * 255 / ((1 << depth) - 1); r = g = bl = idx; }
            } else if (ct == 2) {
                int st = depth == 16 ? 2 : 1;
                r = d[x * 3 * st]; g = d[x * 3 * st + st]; bl = d[x * 3 * st + 2 * st];
            } else if (ct == 4) {
                int st = depth == 16 ? 2 : 1;
                r = g = bl = d[x * 2 * st]; al = d[x * 2 * st + st];
            } else {
                int st = depth == 16 ? 2 : 1;
                r = d[x * 4 * st]; g = d[x * 4 * st + st]; bl = d[x * 4 * st + 2 * st]; al = d[x * 4 * st + 3 * st];
            }
            if (al != 255) { r = (r * al + 8 * (255 - al)) / 255; g = (g * al + 12 * (255 - al)) / 255; bl = (bl * al + 40 * (255 - al)) / 255; }
            out[(size_t)y * w + x] = 0xFF000000u | ((uint32_t)r << 16) | ((uint32_t)g << 8) | (uint32_t)bl;
        }
    }
    free(raw);
    *pix = out; *pw = (int)w; *ph = (int)h;
    return NULL;
fail:
    free(z); free(raw); free(out);
    return err;
}

/* ---- caratulas: USRDIR/covers/<nombre de la ROM sin extension>.png ---- */
#define HR_COVMAX 600
#define HR_COV_W 312
#define HR_COV_H 280
static char g_cov_names[HR_COVMAX][100];
static int  g_cov_n;
static uint32_t g_cov_pix[HR_COV_W * HR_COV_H];
static int  g_cov_w, g_cov_h, g_cov_state;           /* state: 0 = esperando, 1 = lista, 2 = no hay archivo, 3 = error */
static const char *g_cov_err = "";

static int hr_ieq(const char *a, const char *b)
{
    for (; *a && *b; a++, b++) {
        int x = (unsigned char)*a, y = (unsigned char)*b;
        if (x >= 'A' && x <= 'Z') x += 32;
        if (y >= 'A' && y <= 'Z') y += 32;
        if (x != y) return 0;
    }
    return *a == *b;
}

static void hr_cov_scan(void)
{
    char path[320];
    DIR *d;
    struct dirent *e;
    g_cov_n = 0;
    snprintf(path, sizeof path, "%s/covers", g_dir);
    d = opendir(path);
    if (!d) {
        mkdir(path, 0777);                   /* la crea para que se sepa donde van las caratulas (como en NesNet) */
        d = opendir(path);
        if (!d) { logf_("covers: no existe %s y no pude crearla", path); return; }
        logf_("covers: carpeta creada: %s", path);
    }
    while ((e = readdir(d)) != NULL && g_cov_n < HR_COVMAX) {
        size_t n = strlen(e->d_name);
        if (n > 4 && n < sizeof g_cov_names[0] && hr_ieq(e->d_name + n - 4, ".png")) { memcpy(g_cov_names[g_cov_n], e->d_name, n + 1); g_cov_n++; }
    }
    closedir(d);
    logf_("covers: %d archivos .png en %s", g_cov_n, path);
}

/* nombre de la ROM sin la extension (lo que se busca en covers/) */
static void hr_rom_base(const char *name, char *out, size_t cap)
{
    const char *dot = strrchr(name, '.');
    size_t n = dot && dot > name ? (size_t)(dot - name) : strlen(name);
    if (n >= cap) n = cap - 1;
    memcpy(out, name, n);
    out[n] = 0;
}

static void hr_cov_fit(const uint32_t *src, int sw, int sh)
{
    int dw, dh, dx, dy;
    if ((uint64_t)sw * HR_COV_H > (uint64_t)sh * HR_COV_W) { dw = HR_COV_W; dh = (int)((int64_t)sh * HR_COV_W / sw); }
    else { dh = HR_COV_H; dw = (int)((int64_t)sw * HR_COV_H / sh); }
    if (dw < 1) dw = 1;
    if (dh < 1) dh = 1;
    if (dw > HR_COV_W) dw = HR_COV_W;
    if (dh > HR_COV_H) dh = HR_COV_H;
    for (dy = 0; dy < dh; dy++) {
        int y0 = (int)((int64_t)dy * sh / dh), y1 = (int)((int64_t)(dy + 1) * sh / dh);
        if (y1 <= y0) y1 = y0 + 1;
        if (y1 > sh) y1 = sh;
        for (dx = 0; dx < dw; dx++) {
            int x0 = (int)((int64_t)dx * sw / dw), x1 = (int)((int64_t)(dx + 1) * sw / dw), xx, yy;
            uint32_t r = 0, g = 0, b = 0, cnt;
            if (x1 <= x0) x1 = x0 + 1;
            if (x1 > sw) x1 = sw;
            for (yy = y0; yy < y1; yy++)
                for (xx = x0; xx < x1; xx++) {
                    uint32_t p = src[(size_t)yy * sw + xx];
                    r += (p >> 16) & 255; g += (p >> 8) & 255; b += p & 255;
                }
            cnt = (uint32_t)((y1 - y0) * (x1 - x0));
            g_cov_pix[dy * HR_COV_W + dx] = 0xFF000000u | ((r / cnt) << 16) | ((g / cnt) << 8) | (b / cnt);
        }
    }
    g_cov_w = dw; g_cov_h = dh;
}

static void hr_cov_load(const char *romname)
{
    char base[ROM_NAMELEN], path[460];
    int i, found = -1;
    uint8_t *buf = NULL;
    size_t bs = 0;
    uint32_t *pix = NULL;
    int pw = 0, ph = 0;
    const char *er;
    hr_rom_base(romname, base, sizeof base);
    for (i = 0; i < g_cov_n && found < 0; i++) {
        size_t bl = strlen(base);
        if (strlen(g_cov_names[i]) == bl + 4 && hr_ieq(g_cov_names[i] + bl, ".png")) {
            char t[100];
            memcpy(t, g_cov_names[i], bl); t[bl] = 0;
            if (hr_ieq(t, base)) found = i;
        }
    }
    if (found < 0) { g_cov_state = 2; return; }
    snprintf(path, sizeof path, "%s/covers/%s", g_dir, g_cov_names[found]);
    if (!read_whole_file(path, &buf, &bs)) { g_cov_state = 3; g_cov_err = "NO PUDE LEER LA IMAGEN"; return; }
    if (bs > 16u * 1024u * 1024u) { free(buf); g_cov_state = 3; g_cov_err = "IMAGEN MUY GRANDE"; return; }
    er = hr_png_decode(buf, bs, &pix, &pw, &ph);
    free(buf);
    if (er) { g_cov_state = 3; g_cov_err = er; logf_("covers: %s: %s", path, er); return; }
    hr_cov_fit(pix, pw, ph);
    free(pix);
    g_cov_state = 1;
}

/* ---- pantallas ---- */
static void hr_bar(const char *text)
{
    int x0 = 117, by = 566, y;
    for (y = 0; y < 52; y++) {
        int xl = x0 + 20 - y * 20 / 52, xr = HR_W - x0 - y * 20 / 52;
        hr_rect(xl, by + y, xr - xl, 1, HC_CARD);
    }
    hr_line(x0 + 20, by, HR_W - x0, by, 2, HC_LINE);
    hr_line(x0, by + 52, HR_W - x0 - 20, by + 52, 2, HC_LINE);
    hr_line(x0 + 20, by, x0, by + 52, 2, HC_LINE);
    hr_line(HR_W - x0, by, HR_W - x0 - 20, by + 52, 2, HC_LINE);
    hr_text(HF_MS17, 640, by + 26, text, HC_TXT, "cm", 0);
}

static void hr_show_draw(const char *l1, const char *l2, const char *l3)
{
    char t[100];
    hr_begin();
    hr_logo(110);
    hr_card(340, 250, 600, 220, 24, 0);
    if (l1) { hr_fit(HF_OB19, l1, 540, t, sizeof t); hr_text(HF_OB19, 640, 322, t, HC_CY, "cm", 0); }
    if (l2) { hr_fit(HF_MS17, l2, 540, t, sizeof t); hr_text(HF_MS17, 640, 380, t, HC_TXT, "cm", 0); }
    if (l3) { hr_fit(HF_MS15, l3, 540, t, sizeof t); hr_text(HF_MS15, 640, 424, t, HC_DIM, "cm", 0); }
    hr_text(HF_OM14, 1160, 676, "V0.3.2", HC_DIM, "rm", 0);
}

static void hr_menu_draw(int sel, int has_rom, const char *rom_name)
{
    static const char *const names[6] = { "ELEGIR ROM", "CREAR SALA", "UNIRSE A SALA", "SOLO / 2 JUGADORES", "MULTIJUGADOR 2 VS 2", "OPCIONES" };
    static const char *const descs[6] = { "Busca un juego en tu carpeta de ROMs", "Crea una sala 1 vs 1 y comparte el código", "Entra a la sala de tu amigo con su código",
                                           "Juega en esta PS3, hasta 2 mandos", "Dos jugadores por PS3 en línea", "Pantalla, volumen e información de red" };
    static const int icons[6] = { HI_CART, HI_PLUS, HI_LINK, HI_PAD, HI_FOUR, HI_GEAR };
    int i, cw = 330, ch = 170, gp = 28, x0 = (HR_W - 3 * 330 - 2 * 28) / 2, y0 = 176;
    char t[100];
    hr_begin();
    hr_logo(38);
    hr_text(HF_MS14, 640, 108, "EMULADOR DE SNES CON NETPLAY", HC_DIM, "ct", 4);
    if (has_rom) {
        char nm[ROM_NAMELEN], fit[110];
        hr_rom_base(rom_name, nm, sizeof nm);
        snprintf(t, sizeof t, "ROM:  %s", nm);
        hr_fit(HF_MS15, t, 700, fit, sizeof fit);
        hr_text(HF_MS15, 640, 142, fit, HC_CY, "cm", 0);
    } else hr_text(HF_MS15, 640, 142, "ROM: ninguna (elige una)", HC_WARN, "cm", 0);
    for (i = 0; i < 6; i++) {
        int c = i % 3, r = i / 3, x = x0 + c * (cw + gp), y = y0 + r * (ch + gp);
        int locked = !has_rom && i != 0 && i != 5, s = i == sel;
        uint32_t ic = locked ? (s ? HC_LOCKS : HC_LOCK) : (s ? HC_CY : HC_DIM), tc = locked ? (s ? HC_LOCKS : HC_LOCK) : (s ? HC_WHITE : HC_SIL);
        hr_card(x, y, cw, ch, 24, s);
        hr_icon(icons[i], x + cw / 2, y + 68, ic);
        hr_text(s ? HF_OB17 : HF_OB15, x + cw / 2, y + 134, names[i], tc, "cm", 0);
    }
    hr_bar(!has_rom && sel != 0 && sel != 5 ? "Primero elige una ROM (ELEGIR ROM)" : descs[sel]);
    {
        HrBtn bt[2] = { { 0, "ACEPTAR" }, { 1, "SALIR AL XMB" } };
        hr_btns(bt, 2, NULL);
    }
}

static void hr_menu4_draw(int sel)
{
    static const char *const names[2] = { "CREAR SALA 2 VS 2", "UNIRSE A SALA 2 VS 2" };
    int i;
    hr_begin();
    hr_head("MULTIJUGADOR 2 VS 2", "Dos jugadores por PS3, en línea");
    for (i = 0; i < 2; i++) {
        int x = 230 + i * 440, y = 240, s = i == sel;
        hr_card(x, y, 380, 190, 26, s);
        hr_icon(i == 0 ? HI_PLUS : HI_LINK, x + 190, y + 76, s ? HC_CY : HC_DIM);
        hr_text(s ? HF_OB17 : HF_OB15, x + 190, y + 152, names[i], s ? HC_WHITE : HC_SIL, "cm", 0);
    }
    hr_bar("El host usa los mandos 1 y 2; quien se une, el 3 y el 4");
    {
        HrBtn bt[2] = { { 0, "ACEPTAR" }, { 1, "VOLVER" } };
        hr_btns(bt, 2, NULL);
    }
}

static void hr_opt_draw(int sel)
{
    static const char *const labels[4] = { "PANTALLA", "VOLUMEN", "INFO DE RED EN PARTIDA", "VOLVER" };
    static const char *const nets[3] = { "Solo al inicio (5 s)", "Siempre", "No mostrar" };
    static const char *const scr_desc[3] = { "Original: píxeles cuadrados, como siempre.", "4:3 real: la proporción de las TV de antes.", "16:9 estirada a pantalla ancha." };
    static const char *const net_desc[3] = { "Delay, FPS y trabas se ven los primeros 5 segundos.", "Delay, FPS y trabas en vivo, arriba a la izquierda.", "Solo sale el aviso rojo de desincronización." };
    int i, x0 = 120, y0 = 160, w = 760, h = 62, g = 10;
    char val[40], t[160];
    char lines[6][64];
    int nl;
    hr_begin();
    hr_head("OPCIONES", "Se guardan solas");
    for (i = 0; i < 4; i++) {
        int y = y0 + i * (h + g), s = i == sel;
        hr_card(x0, y, w, h, 14, s);
        hr_text(s ? HF_OB19 : HF_OM18, x0 + 34, y + h / 2, labels[i], s ? HC_WHITE : HC_SIL, "lm", 0);
        if (i == 0) hr_text(HF_MS17B, x0 + w - 30, y + h / 2, screen_names[g_screen], s ? HC_CY : HC_TXT, "rm", 0);
        else if (i == 1) {
            int bx = x0 + w - 30 - 240;
            snprintf(val, sizeof val, "%d %%", g_volume);
            hr_rr_fill(bx, y + h / 2 - 5, bx + 170, y + h / 2 + 5, 5, 0xFF1E285Au);
            if (g_volume > 0) hr_rr_fill(bx, y + h / 2 - 5, bx + 170 * g_volume / 100, y + h / 2 + 5, 5, HC_CY);
            hr_text(HF_MS17B, x0 + w - 30, y + h / 2, val, s ? HC_CY : HC_TXT, "rm", 0);
        } else if (i == 2) hr_text(HF_MS17B, x0 + w - 30, y + h / 2, nets[g_netinfo], s ? HC_CY : HC_TXT, "rm", 0);
    }
    hr_card(920, 160, 240, 4 * (h + g) - g, 22, 0);
    hr_text(HF_OB17, 1040, 196, "CONSEJO", HC_CY, "cm", 0);
    if (sel == 0) snprintf(t, sizeof t, "%s", scr_desc[g_screen]);
    else if (sel == 1) snprintf(t, sizeof t, "%s", g_volume == 0 ? "Silencio." : "100 % es el volumen de siempre. En el menú no suena nada: se oye al jugar.");
    else if (sel == 2) snprintf(t, sizeof t, "%s", net_desc[g_netinfo]);
    else snprintf(t, sizeof t, "Vuelve al menú principal.");
    nl = hr_wrap(HF_MS15, t, 200, lines, 6);
    for (i = 0; i < nl; i++) hr_text(HF_MS15, 1040, 240 + i * 26, lines[i], HC_TXT, "cm", 0);
    if (sel < 3) { hr_text(HF_OM14, 1040, 384, "IZQ / DER", HC_DIM, "cm", 0); hr_text(HF_MS14, 1040, 408, "cambia el valor", HC_DIM, "cm", 0); }
    {
        HrBtn bt[2] = { { 0, "ELEGIR" }, { 1, "VOLVER" } };
        hr_btns(bt, 2, NULL);
    }
}

static void hr_rom_draw(int sel, int top, int vis)
{
    int i, x0 = 120, y0 = 156, w = 620, h = 50, g = 6, fx = 780, fy = 156, fw = 380, fh = 8 * 56 - 6, ax = fx + 34, ay = fy + 40, cy;
    char sub[64], t[200], fit[200], base[ROM_NAMELEN];
    hr_begin();
    snprintf(sub, sizeof sub, "USRDIR/roms  -  %d ROM%s", g_nroms, g_nroms == 1 ? "" : "s");
    hr_head("ELEGIR ROM", sub);
    if (g_nroms == 0) {
        HrBtn bt[1] = { { 1, "VOLVER" } };
        hr_card(260, 190, 760, 280, 28, 0);
        hr_text(HF_OB19, 640, 268, "NO HAY ROMS EN LA CARPETA", HC_WHITE, "cm", 0);
        hr_text(HF_OB17, 640, 322, "SILV00001/USRDIR/roms", HC_CY, "cm", 0);
        hr_text(HF_MS17, 640, 380, "Pon ahí tus ROMs (.sfc, .smc o .zip) y vuelve a entrar.", HC_TXT, "cm", 0);
        hr_btns(bt, 1, NULL);
        return;
    }
    for (i = 0; i < vis && top + i < g_nroms; i++) {
        int k = top + i, y = y0 + i * (h + g), s = k == sel;
        hr_card(x0, y, w, h, 12, s);
        hr_rom_base(g_roms[k].name, base, sizeof base);
        hr_fit(s ? HF_OB17 : HF_OM16, base, w - 60, fit, sizeof fit);
        hr_text(s ? HF_OB17 : HF_OM16, x0 + 30, y + h / 2, fit, s ? HC_WHITE : HC_SIL, "lm", 0);
    }
    if (top > 0) hr_tri(760, y0 + 14, 12, 0, HC_CY);
    if (top + vis < g_nroms) hr_tri(760, y0 + vis * (h + g) - g - 14, 12, 1, HC_CY);
    hr_card(fx, fy, fw, fh, 22, 0);
    hr_rom_base(g_roms[sel].name, base, sizeof base);
    if (g_cov_state == 1) {
        int px = ax + (HR_COV_W - g_cov_w) / 2, py = ay + (HR_COV_H - g_cov_h) / 2, yy, xx;
        hr_rect_a(px + 4, py + 8, g_cov_w, g_cov_h, 0xFF000000u, 120);
        for (yy = 0; yy < g_cov_h; yy++)
            for (xx = 0; xx < g_cov_w; xx++) g_hr[(py + yy) * HR_W + px + xx] = g_cov_pix[yy * HR_COV_W + xx];
    } else if (g_cov_state == 2) {
        hr_text(HF_OM16, ax + HR_COV_W / 2, ay + HR_COV_H / 2 - 12, "SIN CARÁTULA", HC_DIM, "cm", 0);
        hr_text(HF_MS13, ax + HR_COV_W / 2, ay + HR_COV_H / 2 + 16, "Pon un PNG con el nombre de abajo", HC_DIM, "cm", 0);
    } else if (g_cov_state == 3) {
        hr_text(HF_OM14, ax + HR_COV_W / 2, ay + HR_COV_H / 2 - 8, "NO PUDE MOSTRARLA", HC_WARN, "cm", 0);
        hr_fit(HF_MS13, g_cov_err, 300, fit, sizeof fit);
        hr_text(HF_MS13, ax + HR_COV_W / 2, ay + HR_COV_H / 2 + 16, fit, HC_DIM, "cm", 0);
    }
    cy = ay + HR_COV_H + 34;
    hr_fit(HF_OB17, base, fw - 40, fit, sizeof fit);
    hr_text(HF_OB17, fx + fw / 2, cy, fit, HC_WHITE, "cm", 0);
    if (g_roms[sel].has_crc) snprintf(t, sizeof t, "%u KB  -  CRC %08X", (unsigned)((g_roms[sel].size + 512) / 1024), (unsigned)g_roms[sel].crc);
    else snprintf(t, sizeof t, "%u KB  -  CRC ........", (unsigned)((g_roms[sel].size + 512) / 1024));
    hr_text(HF_MS14, fx + fw / 2, cy + 28, t, HC_DIM, "cm", 0);
    snprintf(t, sizeof t, "%d / %d", sel + 1, g_nroms);
    hr_text(HF_OM14, fx + fw / 2, cy + 52, t, HC_CY, "cm", 0);
    snprintf(t, sizeof t, "covers/%s.png", base);
    hr_fit(HF_MS13, t, fw - 40, fit, sizeof fit);
    hr_text(HF_MS13, fx + fw / 2, cy + 78, fit, HC_DIM, "cm", 0);
    {
        HrBtn bt[2] = { { 0, "JUGAR" }, { 1, "VOLVER" } };
        hr_btns(bt, 2, "IZQ / DER: saltar 10");
    }
}

static void hr_code_draw(const int *d, int pos, int saved)
{
    int i, x = 0, pitch = 56, total = 10 * pitch + 2 * 24, sx;
    char t[40];
    hr_begin();
    hr_head("UNIRSE A SALA", "Escribe el código del host");
    hr_card(190, 170, 900, 330, 28, 0);
    hr_text(HF_OM16, 640, 214, "CÓDIGO DE SALA", HC_DIM, "cm", 0);
    sx = 640 - total / 2;
    for (i = 0; i < 10; i++) {
        char c[2];
        int cx;
        c[0] = (char)('0' + d[i]); c[1] = 0;
        x = sx + i * pitch + (i >= 3 ? 24 : 0) + (i >= 6 ? 24 : 0);
        cx = x + pitch / 2 - 4;
        if (i == pos) {
            hr_rr_fill(x, 252, x + pitch - 8, 338, 8, HC_SEL);
            hr_tri(cx, 262, 10, 0, HC_CY);
            hr_tri(cx, 328, 10, 1, HC_CY);
        }
        hr_text(HF_CODE, cx, 296, c, i == pos ? HC_CY : HC_WHITE, "cm", 0);
        if (i == pos) hr_line(x + 4, 344, x + pitch - 12, 344, 3, HC_CY);
    }
    snprintf(t, sizeof t, "Dígito %d de 10", pos + 1);
    hr_text(HF_MS17, 640, 392, t, HC_TXT, "cm", 0);
    if (saved) hr_text(HF_MS15, 640, 432, "Último código usado (START: conectar)", 0xFF80FF80u, "cm", 0);
    else hr_text(HF_MS15, 640, 432, "ARRIBA / ABAJO cambia el dígito  -  IZQ / DER te mueve", HC_DIM, "cm", 0);
    {
        HrBtn bt[2] = { { 2, "CONECTAR" }, { 1, "CANCELAR" } };
        hr_btns(bt, 2, NULL);
    }
}

static void hr_host_draw(const char *code, const char *l2, const char *l3, uint32_t col3, int one)
{
    int i;
    char pc[24], t[80];
    const char *lab[4] = { "JUEGO", "RED", "PUERTO", "ESTADO" };
    char val[4][96];
    uint32_t vc[4];
    hr_begin();
    hr_head(one ? "SALA 1 VS 1" : "SALA 2 VS 2", one ? "Eres el anfitrión - mando 1" : "Eres el anfitrión - mandos 1 y 2");
    hr_card(260, 160, 760, 420, 28, 0);
    hr_text(HF_OM16, 640, 204, "CÓDIGO DE SALA", HC_DIM, "cm", 0);
    code_pretty(code, pc);
    hr_text(HF_CODE, 640, 270, pc, HC_CY, "cm", 0);
    hr_line(330, 326, 950, 326, 1, HC_LINE);
    if (g_rom) { hr_rom_base(g_rom_name, t, sizeof t); snprintf(val[0], sizeof val[0], "%s", t); } else snprintf(val[0], sizeof val[0], "-");
    snprintf(val[1], sizeof val[1], "%s", l3);
    snprintf(val[2], sizeof val[2], "%s", strncmp(l2, "PUERTO TCP ", 11) == 0 ? l2 + 11 : l2);
    snprintf(val[3], sizeof val[3], "Esperando a tu amigo...");
    vc[0] = HC_WHITE; vc[1] = col3; vc[2] = HC_TXT; vc[3] = HC_TXT;
    for (i = 0; i < 4; i++) {
        char fit[100];
        int yy = 366 + i * 42;
        hr_text(HF_OM14, 330, yy, lab[i], HC_DIM, "lm", 0);
        hr_fit(HF_MS18, val[i], 440, fit, sizeof fit);
        hr_text(HF_MS18, 950, yy, fit, vc[i], "rm", 0);
    }
    hr_text(HF_MS15, 640, 548, "Pasa este código a tu amigo para que pulse UNIRSE A SALA.", HC_DIM, "cm", 0);
    {
        HrBtn bt[1] = { { 1, "CERRAR SALA" } };
        hr_btns(bt, 1, NULL);
    }
}

/* ---- pantallas con su propio bucle (se usan en lugar de las de siempre cuando hr_usable()) ---- */
static int ui_rom_select_hr(void)
{
    enum { VIS = 8 };
    int sel = 0, top = 0, i, last_sel = -1, hold = 0;
    g_stage = "elegir-rom";
    roms_scan();
    hr_cov_scan();
    g_cov_state = 0;
    for (i = 0; i < g_nroms; i++) if (g_rom_name[0] && !strcmp(g_roms[i].name, g_rom_name)) sel = i;
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_CANCEL) return 0;
        if (g_nroms > 0) {
            if (e & UI_UP)    sel = (sel + g_nroms - 1) % g_nroms;
            if (e & UI_DOWN)  sel = (sel + 1) % g_nroms;
            if (e & UI_LEFT)  sel = sel - 10 < 0 ? 0 : sel - 10;
            if (e & UI_RIGHT) sel = sel + 10 >= g_nroms ? g_nroms - 1 : sel + 10;
            if (e & (UI_OK | UI_START)) {
                ui_show("CARGANDO ROM...", g_roms[sel].name, NULL);
                if (rom_load(sel)) {
                    snprintf(g_last_rom, sizeof g_last_rom, "%s", g_rom_name);
                    opts_save();
                    return 1;
                }
                ui_message(g_rom_why[0] ? g_rom_why : "NO PUDE LEER LA ROM", g_roms[sel].name, 300);
            }
            if (sel < top) top = sel;
            if (sel >= top + VIS) top = sel - VIS + 1;
            if (sel != last_sel) { last_sel = sel; hold = 0; g_cov_state = 0; }
            else if (hold < 1000) hold++;
            if (hold == 12) {
                if (!g_roms[sel].has_crc) {
                    uint8_t *b = NULL;
                    size_t bs = 0;
                    char rp[420];
                    snprintf(rp, sizeof rp, "%s/roms/%s", g_dir, g_roms[sel].name);
                    if (read_rom_file(rp, &b, &bs, NULL, 0)) { g_roms[sel].crc = snes_crc(b, bs); g_roms[sel].has_crc = 1; free(b); }
                }
                hr_cov_load(g_roms[sel].name);       /* la caratula se carga cuando el cursor se queda quieto (no al pasar rapido) */
            }
        }
        hr_rom_draw(sel, top, VIS);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return 0;
}

static void ui_options_hr(void)
{
    int sel = 0;
    g_stage = "opciones";
    ui_prime();
    while (g_running) {
        uint16_t e;
        int dl = 0;
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + 3) % 4;
        if (e & UI_DOWN) sel = (sel + 1) % 4;
        if (e & UI_CANCEL) break;
        if (e & UI_LEFT) dl = -1;
        if (e & (UI_RIGHT | UI_OK)) dl = 1;
        if (sel == 3) { if (e & (UI_OK | UI_START)) break; }
        else if (dl) {
            if (sel == 0) g_screen = (g_screen + (dl > 0 ? 1 : 2)) % 3;
            else if (sel == 1) { g_volume += dl * 10; if (g_volume < 0) g_volume = 0; if (g_volume > 100) g_volume = 100; }
            else g_netinfo = (g_netinfo + (dl > 0 ? 1 : 2)) % 3;
            opts_save();
        }
        hr_opt_draw(sel);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    logf_("opciones: pantalla=%s volumen=%d info de red=%d", screen_names[g_screen], g_volume, g_netinfo);
}

static int ui_menu4_hr(void)
{
    int sel = 0;
    g_stage = "menu-2vs2";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & (UI_LEFT | UI_UP | UI_RIGHT | UI_DOWN)) sel ^= 1;
        if (e & UI_CANCEL) return -1;
        if (e & (UI_OK | UI_START)) return sel == 0 ? MODE_HOST : MODE_JOIN;
        hr_menu4_draw(sel);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return -1;
}

static int ui_menu_hr(void)
{
    static const int modes6[6] = { MODE_ROM, MODE_HOST1, MODE_JOIN1, MODE_SOLO, -2, MODE_OPT };
    static const int from_old[7] = { 0, 3, 1, 2, 4, 4, 5 };      /* orden de la lista vieja -> tarjeta */
    static const int to_old[6] = { 0, 2, 3, 1, 4, 6 };           /* tarjeta -> orden de la lista vieja (g_menu_sel) */
    int sel = from_old[(g_menu_sel >= 0 && g_menu_sel < 7) ? g_menu_sel : 0];
    g_stage = "menu";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_LEFT)  sel = (sel / 3) * 3 + (sel % 3 + 2) % 3;
        if (e & UI_RIGHT) sel = (sel / 3) * 3 + (sel % 3 + 1) % 3;
        if (e & (UI_UP | UI_DOWN)) sel = (sel + 3) % 6;
        g_menu_sel = to_old[sel];
        if (e & UI_CANCEL) {
            logf_("salida al XMB pedida con O en el menu principal");
            g_running = 0;
            return -1;
        }
        if (e & (UI_OK | UI_START)) {
            if (modes6[sel] != MODE_ROM && modes6[sel] != MODE_OPT && !g_rom) ui_message("PRIMERO ELIGE UNA ROM", "OPCION: ELEGIR ROM", 120);
            else if (modes6[sel] == -2) {
                int m = ui_menu4_hr();
                if (m >= 0) { g_menu_sel = m == MODE_HOST ? 4 : 5; return m; }
                ui_prime();
                g_stage = "menu";
            } else return modes6[sel];
        }
        hr_menu_draw(sel, g_rom != NULL, g_rom_name);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return -1;
}

static void ui_show(const char *l1, const char *l2, const char *l3)
{
    if (hr_usable()) { hr_show_draw(l1, l2, l3); present(); return; }
    ui_clear();
    ui_center(20, "SILVERSKY V0.2", 2, 0xFFFFD040);
    if (l1) ui_center(90, l1, 1, 0xFFFFFFFF);
    if (l2) ui_center(110, l2, 1, 0xFFC0C0FF);
    if (l3) ui_center(130, l3, 1, 0xFFC0C0FF);
    present();
}

static void ui_message(const char *l1, const char *l2, int frames)
{
    int i;
    for (i = 0; i < frames && g_running; i++) {
        uint16_t e;
        pump();
        ui_show(l1, l2, NULL);
        e = ui_edges();
        if (i > 60 && (e & (UI_OK | UI_CANCEL | UI_START))) break;   /* ~1 s minimo en pantalla */
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
}

/* Copia 'src' en 'dst' (cap bytes) acortando con "..." si no cabe en 'maxc' caracteres */
static void fit_name(char *dst, size_t cap, const char *src, int maxc)
{
    size_t n = strlen(src);
    if ((int)n <= maxc && n < cap) { snprintf(dst, cap, "%s", src); return; }
    if ((size_t)maxc >= cap) maxc = (int)cap - 1;
    memcpy(dst, src, (size_t)maxc);
    dst[maxc] = 0;
    if (maxc >= 3) { dst[maxc - 3] = '.'; dst[maxc - 2] = '.'; dst[maxc - 1] = '.'; }
}

/* Selector de ROM: lista de USRDIR/roms. 1 = eligio y cargo una ROM, 0 = volvio sin elegir */
static int ui_rom_select(void)
{
    enum { VIS = 9 };
    if (hr_usable()) return ui_rom_select_hr();
    int sel = 0, top = 0, i, last_sel = -1, hold = 0;
    g_stage = "elegir-rom";
    roms_scan();
    for (i = 0; i < g_nroms; i++) if (g_rom_name[0] && !strcmp(g_roms[i].name, g_rom_name)) sel = i;
    while (g_running) {
        uint16_t e;
        char line[64], nm[48];
        pump();
        e = ui_edges();
        if (e & UI_CANCEL) return 0;
        if (g_nroms > 0) {
            if (e & UI_UP)    sel = (sel + g_nroms - 1) % g_nroms;
            if (e & UI_DOWN)  sel = (sel + 1) % g_nroms;
            if (e & UI_LEFT)  sel = sel - 10 < 0 ? 0 : sel - 10;
            if (e & UI_RIGHT) sel = sel + 10 >= g_nroms ? g_nroms - 1 : sel + 10;
            if (e & (UI_OK | UI_START)) {
                ui_show("CARGANDO ROM...", g_roms[sel].name, NULL);
                if (rom_load(sel)) {
                    snprintf(g_last_rom, sizeof g_last_rom, "%s", g_rom_name);     /* v1.9: la recuerda para la proxima vez */
                    opts_save();
                    return 1;
                }
                ui_message(g_rom_why[0] ? g_rom_why : "NO PUDE LEER LA ROM", g_roms[sel].name, 300);
            }
            if (sel < top) top = sel;
            if (sel >= top + VIS) top = sel - VIS + 1;
            /* v1.9: el CRC32 se calcula cuando el cursor se queda ~0,2 s sobre una ROM (no al pasar rapido) */
            if (sel != last_sel) { last_sel = sel; hold = 0; }
            else if (hold < 1000) hold++;
            if (hold == 12 && !g_roms[sel].has_crc) {
                uint8_t *b = NULL;
                size_t bs = 0;
                char rp[420];
                snprintf(rp, sizeof rp, "%s/roms/%s", g_dir, g_roms[sel].name);
                if (read_rom_file(rp, &b, &bs, NULL, 0)) { g_roms[sel].crc = snes_crc(b, bs); g_roms[sel].has_crc = 1; free(b); }
            }
        }
        ui_clear();
        ui_center(14, "ELEGIR ROM", 2, 0xFFFFD040);
        if (g_nroms == 0) {
            ui_center(80, "NO HAY ROMS EN LA CARPETA:", 1, 0xFFFFFFFF);
            ui_center(100, "SILV00001/USRDIR/ROMS", 1, 0xFFC0C0FF);
            ui_center(124, "PON AHI TUS ROMS (.SFC O .SMC)", 1, 0xFFC0C0FF);
            ui_center(140, "Y VUELVE A ENTRAR AQUI", 1, 0xFFC0C0FF);
        } else {
            snprintf(line, sizeof line, "%d / %d", sel + 1, g_nroms);
            ui_center(38, line, 1, 0xFFC0C0FF);
            for (i = 0; i < VIS && top + i < g_nroms; i++) {
                int k = top + i;
                fit_name(nm, sizeof nm, g_roms[k].name, 38);
                snprintf(line, sizeof line, "%s %s", k == sel ? ">" : " ", nm);
                ui_text(8, 52 + i * 12, line, 1, k == sel ? 0xFFFFFFFF : 0xFF8080A0);
            }
            if (top > 0)              ui_text(244, 52, "^", 1, 0xFFC0C0FF);
            if (top + VIS < g_nroms)  ui_text(244, 52 + (VIS - 1) * 12, "V", 1, 0xFFC0C0FF);
            {
                /* v1.9: nombre completo de la ROM marcada (hasta 2 lineas de 40 letras), tamano y CRC32 */
                const char *full = g_roms[sel].name;
                size_t fl = strlen(full);
                char l1[48], l2[48], l3[64], crc[12];
                snprintf(l1, sizeof l1, "%.40s", full);
                if (fl > 40) fit_name(l2, sizeof l2, full + 40, 40); else l2[0] = 0;
                if (g_roms[sel].has_crc) snprintf(crc, sizeof crc, "%08X", (unsigned)g_roms[sel].crc); else snprintf(crc, sizeof crc, "........");
                snprintf(l3, sizeof l3, "%u KB    CRC32 %s", (unsigned)((g_roms[sel].size + 512) / 1024), crc);
                ui_text(8, 164, l1, 1, 0xFFFFD040);
                if (l2[0]) ui_text(8, 175, l2, 1, 0xFFFFD040);
                ui_text(8, 188, l3, 1, 0xFFC0C0FF);
            }
        }
        if (g_nroms) ui_center(204, "IZQ/DER: SALTAR 10", 1, 0xFF8080A0);
        ui_center(218, g_nroms ? "X: ELEGIR   O: VOLVER" : "O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return 0;
}

/* v1.8.2: OPCIONES > PANTALLA. El modo se aplica en el acto al mover el cursor (esta misma pantalla ya sale con el modo elegido) */
static void ui_opt_screen(void)
{
    static const char *desc[3] = { "PIXELES CUADRADOS (COMO SIEMPRE)", "PROPORCION DE TV 4:3", "ESTIRADA A PANTALLA ANCHA 16:9" };
    int i;
    g_stage = "opciones-pantalla";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   { g_screen = (g_screen + 2) % 3; opts_save(); }
        if (e & UI_DOWN) { g_screen = (g_screen + 1) % 3; opts_save(); }
        if (e & (UI_OK | UI_CANCEL | UI_START)) break;
        ui_clear();
        ui_center(20, "PANTALLA", 2, 0xFFFFD040);
        ui_center(46, "SOLO CAMBIA LA IMAGEN DEL JUEGO", 1, 0xFFC0C0FF);
        for (i = 0; i < 3; i++) {
            char line[48];
            snprintf(line, sizeof line, "%s %s", i == g_screen ? ">" : " ", screen_names[i]);
            ui_center(78 + i * 22, line, 1, i == g_screen ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(150, desc[g_screen], 1, 0xFF80FF80);
        if (!g_cfg.render) ui_center(170, "AVISO: EL MODO GPU NO USA ESTO", 1, 0xFFFFC040);
        ui_center(200, "ARRIBA/ABAJO: ELEGIR", 1, 0xFF8080A0);
        ui_center(214, "X / O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    logf_("opciones: pantalla = %s", screen_names[g_screen]);
}

/* v1.8.2: OPCIONES > MANDOS > MANDO n: un boton de la PS3 por cada boton del NES, y turbo A / turbo B.
 * IZQ/DER cambia el boton de la fila marcada y SALTA los que ya usa otra fila (no mueve botones ajenos). */


/* v1.9: OPCIONES > SONIDO (volumen 0 a 100, de 10 en 10; se guarda solo). En el menu no suena nada: se oye al jugar. */
static void ui_opt_sound(void)
{
    int i;
    g_stage = "opciones-sonido";
    ui_prime();
    while (g_running) {
        uint16_t e;
        char line[48], bar[16];
        pump();
        e = ui_edges();
        if (e & (UI_LEFT | UI_DOWN))  { g_volume = g_volume - 10 < 0 ? 0 : g_volume - 10; opts_save(); }
        if (e & (UI_RIGHT | UI_UP))   { g_volume = g_volume + 10 > 100 ? 100 : g_volume + 10; opts_save(); }
        if (e & (UI_OK | UI_CANCEL | UI_START)) break;
        ui_clear();
        ui_center(20, "SONIDO", 2, 0xFFFFD040);
        snprintf(line, sizeof line, "VOLUMEN  %d%%", g_volume);
        ui_center(76, line, 2, 0xFFFFFFFF);
        for (i = 0; i < 10; i++) bar[i] = (char)(i < g_volume / 10 ? '#' : '-');
        bar[10] = 0;
        ui_center(108, bar, 2, 0xFF80FF80);
        ui_center(140, g_volume == 0 ? "SILENCIO" : "100% ES EL VOLUMEN DE SIEMPRE", 1, 0xFFC0C0FF);
        if (!g_cfg.audio) ui_center(158, "AVISO: SONIDO APAGADO (R2 AL ABRIR)", 1, 0xFFFFC040);
        ui_center(190, "IZQ/DER: BAJAR / SUBIR", 1, 0xFF8080A0);
        ui_center(204, "X / O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    logf_("opciones: volumen = %d", g_volume);
}

/* v1.9: OPCIONES > INFO DE RED: que se ve arriba a la izquierda durante una partida online (no cambia la red, solo lo que se dibuja) */
static void ui_opt_netinfo(void)
{
    static const char *names[3] = { "SOLO AL INICIO (5 S)", "SIEMPRE", "NO MOSTRAR" };
    static const char *desc[3] = { "COMO HASTA AHORA", "DELAY, FPS Y TRABAS EN VIVO", "SOLO SALE EL AVISO ROJO DE DESYNC" };
    int i;
    g_stage = "opciones-info-red";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   { g_netinfo = (g_netinfo + 2) % 3; opts_save(); }
        if (e & UI_DOWN) { g_netinfo = (g_netinfo + 1) % 3; opts_save(); }
        if (e & (UI_OK | UI_CANCEL | UI_START)) break;
        ui_clear();
        ui_center(20, "INFO DE RED", 2, 0xFFFFD040);
        ui_center(46, "EN PARTIDA ONLINE (ARRIBA A LA IZQUIERDA)", 1, 0xFFC0C0FF);
        for (i = 0; i < 3; i++) {
            char line[48];
            snprintf(line, sizeof line, "%s %s", i == g_netinfo ? ">" : " ", names[i]);
            ui_center(84 + i * 22, line, 1, i == g_netinfo ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(156, desc[g_netinfo], 1, 0xFF80FF80);
        ui_center(176, "DELAY = CUADROS DE ESPERA (1 CUADRO = 17 MS)", 1, 0xFF8080A0);
        ui_center(190, "TRABAS = CUADROS LENTOS EN EL ULTIMO SEGUNDO", 1, 0xFF8080A0);
        ui_center(210, "ARRIBA/ABAJO   X / O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    logf_("opciones: info de red = %d", g_netinfo);
}

static void ui_options(void)
{
    if (hr_usable()) { ui_options_hr(); return; }
    static const char *items[4] = { "PANTALLA", "SONIDO (VOLUMEN)", "INFO DE RED EN PARTIDA", "VOLVER" };
    int sel = 0, i;
    g_stage = "opciones";
    ui_prime();
    while (g_running) {
        uint16_t e;
        pump();
        e = ui_edges();
        if (e & UI_UP)   sel = (sel + 3) % 4;
        if (e & UI_DOWN) sel = (sel + 1) % 4;
        if (e & UI_CANCEL) break;
        if (e & (UI_OK | UI_START)) {
            if (sel == 0) { ui_opt_screen(); ui_prime(); g_stage = "opciones"; }
            else if (sel == 1) { ui_opt_sound(); ui_prime(); g_stage = "opciones"; }
            else if (sel == 2) { ui_opt_netinfo(); ui_prime(); g_stage = "opciones"; }
            else break;
        }
        ui_clear();
        ui_center(20, "OPCIONES", 2, 0xFFFFD040);
        ui_center(46, "SE GUARDAN SOLAS", 1, 0xFFC0C0FF);
        for (i = 0; i < 4; i++) {
            char line[40];
            snprintf(line, sizeof line, "%s %s", i == sel ? ">" : " ", items[i]);
            ui_center(76 + i * 20, line, 1, i == sel ? 0xFFFFFFFF : 0xFF8080A0);
        }
        ui_center(200, "ARRIBA/ABAJO + X", 1, 0xFF8080A0);
        ui_center(214, "O: VOLVER", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
}

static int ui_menu(void)
{
    static const char *items[7] = { "ELEGIR ROM", "SOLO - 2 MANDOS", "CREAR SALA 1 VS 1 (HOST)", "UNIRSE A SALA 1 VS 1",
                                    "CREAR SALA 2 VS 2 (HOST)", "UNIRSE A SALA 2 VS 2", "OPCIONES" };
    static const int modes[7] = { MODE_ROM, MODE_SOLO, MODE_HOST1, MODE_JOIN1, MODE_HOST, MODE_JOIN, MODE_OPT };   /* mismo orden que items */
    int i;
    if (hr_usable()) return ui_menu_hr();
    g_stage = "menu";
    ui_prime();
    while (g_running) {
        uint16_t e;
        char l[80], nm[48];
        pump();
        e = ui_edges();
        if (e & UI_UP)   g_menu_sel = (g_menu_sel + 6) % 7;
        if (e & UI_DOWN) g_menu_sel = (g_menu_sel + 1) % 7;
        if (e & UI_CANCEL) {
            /* v0.2.8: O en el menu principal sale al XMB, sin confirmar (igual que la salida del sistema: g_running = 0) */
            logf_("salida al XMB pedida con O en el menu principal");
            g_running = 0;
            return -1;
        }
        if (e & (UI_OK | UI_START)) {
            /* sin ROM elegida el juego queda en stand-by: solo se puede entrar a ELEGIR ROM y a OPCIONES */
            if (modes[g_menu_sel] != MODE_ROM && modes[g_menu_sel] != MODE_OPT && !g_rom) ui_message("PRIMERO ELIGE UNA ROM", "OPCION: ELEGIR ROM", 120);
            else return modes[g_menu_sel];
        }
        ui_clear();
        ui_center(20, "SILVERSKY V0.2", 2, 0xFFFFD040);
        ui_center(46, "SNES CON NETPLAY PARA PS3", 1, 0xFFC0C0FF);
        if (g_rom) {
            fit_name(nm, sizeof nm, g_rom_name, 34);
            snprintf(l, sizeof l, "ROM: %s", nm);
            ui_center(66, l, 1, 0xFF80FF80);
        } else {
            ui_center(66, "ROM: NINGUNA (ELIGE UNA)", 1, 0xFFFFC040);
        }
        for (i = 0; i < 7; i++) {
            char line[40];
            uint32_t col = i == g_menu_sel ? 0xFFFFFFFF : 0xFF8080A0;
            if (!g_rom && modes[i] != MODE_ROM && modes[i] != MODE_OPT) col = i == g_menu_sel ? 0xFFA0A0B0 : 0xFF505068;   /* bloqueadas sin ROM */
            snprintf(line, sizeof line, "%s %s", i == g_menu_sel ? ">" : " ", items[i]);
            ui_center(84 + i * 14, line, 1, col);
        }
        ui_center(184, "1 VS 1: HOST = MANDO 1 / SE UNE = 2", 1, 0xFF80FF80);
        ui_center(197, "2 VS 2: HOST = 1 Y 2 / SE UNE = 3 Y 4", 1, 0xFF80FF80);
        ui_center(210, "EN PARTIDA: R3 = MENU", 1, 0xFF8080A0);
        ui_center(223, "O: SALIR AL XMB", 1, 0xFF8080A0);
        present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return -1;
}

/* v1.8: submenu del modo de 4 jugadores. Devuelve MODE_HOST, MODE_JOIN o -1 (volver). Copia de la idea de ui_menu. */

static int ui_enter_code(char *out)
{
    int d[10], pos = 0, i, saved = 0;
    memset(d, 0, sizeof d);
    /* v0.2.5.1: si hay un codigo guardado de la vez anterior, aparece ya escrito; se confirma con START (no se conecta solo) */
    if (strlen(g_last_code) == 10) {
        for (i = 0; i < 10; i++) d[i] = g_last_code[i] - '0';
        saved = 1;
    }
    while (g_running) {
        uint16_t e;
        char line[40];
        pump();
        e = ui_edges();
        if (e & UI_UP)    { d[pos] = (d[pos] + 1) % 10; saved = 0; }
        if (e & UI_DOWN)  { d[pos] = (d[pos] + 9) % 10; saved = 0; }
        if (e & UI_LEFT)  { if (pos > 0) pos--; }
        if (e & (UI_RIGHT | UI_OK)) { if (pos < 9) pos++; }
        if (e & UI_CANCEL) return 0;
        if (e & UI_START) {
            for (i = 0; i < 10; i++) out[i] = (char)('0' + d[i]);
            out[10] = 0;
            {
                uint32_t vip; int vport;
                if (strcmp(g_last_code, out) != 0 && code_decode(out, &vip, &vport)) {   /* v0.2.5.1: lo recuerda para la proxima vez (aunque se apague la PS3); un codigo invalido no se guarda */
                    snprintf(g_last_code, sizeof g_last_code, "%.10s", out);
                    opts_save();
                    logf_("codigo de sala guardado en opciones.txt");
                }
            }
            return 1;
        }
if (hr_usable()) {
            hr_code_draw(d, pos, saved);
        } else {
                ui_clear();
        ui_center(20, "SILVERSKY V0.2", 2, 0xFFFFD040);
        ui_center(60, "ESCRIBE EL CODIGO DEL HOST", 1, 0xFFFFFFFF);
        for (i = 0; i < 10; i++) {
            char c[2] = { (char)('0' + d[i]), 0 };
            int x = 24 + i * 20 + (i >= 3 ? 8 : 0) + (i >= 6 ? 8 : 0);     /* grupos 3-3-4 */
            ui_text(x, 100, c, 2, i == pos ? 0xFFFFFF40 : 0xFFFFFFFF);
            if (i == pos) ui_text(x, 118, "-", 2, 0xFFFFFF40);
        }
        snprintf(line, sizeof line, "DIGITO %d DE 10", pos + 1);
        ui_center(140, line, 1, 0xFFC0C0FF);
        if (saved) ui_center(154, "ULTIMO CODIGO USADO (START: CONECTAR)", 1, 0xFF80FF80);
        ui_center(170, "ARRIBA/ABAJO: CAMBIAR   IZQ/DER: MOVER", 1, 0xFF8080A0);
        ui_center(184, "START: CONECTAR    O: CANCELAR", 1, 0xFF8080A0);
}
                present();
#ifdef NESNET_HOST
        sleep_ms(16);
#endif
    }
    return 0;
}

/* ------------------------------------------------------------------ */
/* Modos                                                               */
/* ------------------------------------------------------------------ */
static void net_close(void)
{
    if (g_net >= 0) { closesocket(g_net); g_net = -1; }
    g_rxlen = 0;
}





/* v1.8: COPIAS de run_host_inner / run_host / run_client para el modo de 4. El 1vs1 de arriba no se toca. */
/* v1.8: COPIA de run_online() para el modo de 4: carga el nucleo con 4 mandos (Four Score) y corre session_loop4 */
static int run_online4(int is_host, int D)
{
    int ok;
    if (g_one) {                                      /* v0.2: 1 vs 1 = mismos 2 mandos normales que SOLO */
        if (!core_load()) return 0;
        ok = session_loop(is_host ? 0 : 1, D, g_maxframes);
        core_unload();
        net_close();
        return ok;
    }
    g_four = 1;
    if (!core_load4()) { g_four = 0; return 0; }
    ok = session_loop(is_host ? 0 : 1, D, g_maxframes);
    core_unload();
    g_four = 0;
    net_close();
    return ok;
}

static int run_host4_inner(void)
{
    uint32_t ip = 0;
    char code[20], l2[48], l3[48];
    int lfd, D = 0, got_ip = 0, mism = 0;
    uint32_t col3;
    Upnp up;

    net_ensure();
    memset(&up, 0, sizeof up);
    if (g_cfg.upnp) {
        g_stage = "upnp";
        ui_show("CREANDO SALA...", "ABRIENDO EL PUERTO (UPNP)", NULL);
        upnp_open(g_cfg.port, &up);
        if (!g_running) return 1;
    } else {
        logf_("upnp: apagado (upnp=off en config.txt)");
    }
    g_stage = "buscando-ip";
    ui_show("CREANDO SALA...", "BUSCANDO TU IP PUBLICA", NULL);
    if (g_cfg.public_ip[0] && parse_ip(g_cfg.public_ip, &ip)) { got_ip = 1; logf_("IP publica fijada a mano (public_ip=)"); }
    else if (get_public_ip(&ip)) got_ip = 1;
    else logf_("ipify: no pude obtener la IP publica");
    if (!got_ip && up.public_ip && !ip_privada(up.public_ip)) {
        ip = up.public_ip; got_ip = 1;
        logf_("uso la IP WAN que dio el router por UPnP");
    }
    if (!got_ip) { g_err = "NO PUDE OBTENER TU IP PUBLICA"; return 0; }
    if (up.public_ip && up.public_ip != ip) {
        mism = 1;
        logf_("AVISO: la IP del router (%u.%u.%u.%u) es distinta de la que ve internet (%u.%u.%u.%u): "
              "probable CGNAT o doble NAT, desde afuera no se llega al puerto", IP4(up.public_ip), IP4(ip));
    }
    code_encode(ip, g_cfg.port, code);
    logf_("sala %s creada: ip=%u.%u.%u.%u puerto=%d codigo=%s", g_one ? "1 vs 1" : "2 vs 2", IP4(ip), g_cfg.port, code);

    lfd = tcp_listen(g_cfg.port);
    if (lfd < 0) { g_err = "NO PUDE ABRIR EL PUERTO"; return 0; }

    snprintf(l2, sizeof l2, "PUERTO TCP %d", g_cfg.port);
    col3 = 0xFFFFC040;
    if (!g_cfg.upnp)                                   snprintf(l3, sizeof l3, "UPNP APAGADO: ABRE EL PUERTO");
    else if (!up.router)                               snprintf(l3, sizeof l3, "SIN UPNP: ABRE EL PUERTO A MANO");
    else if (up.public_ip && ip_privada(up.public_ip)) snprintf(l3, sizeof l3, "ROUTER SIN IP PUBLICA (CGNAT)");
    else if (mism)                                     snprintf(l3, sizeof l3, "ROUTER E INTERNET: IP DISTINTA");
    else if (up.opened)                              { snprintf(l3, sizeof l3, "UPNP: PUERTO ABIERTO"); col3 = 0xFF80FF80; }
    else                                               snprintf(l3, sizeof l3, "UPNP RECHAZADO: ABRE EL PUERTO");
    logf_("estado en pantalla: %s", l3);
    g_stage = "esperando-amigo";
    for (;;) {
        uint16_t e;
        pump();
        if (!g_running) { closesocket(lfd); return 1; }
        e = ui_edges();
        if (e & UI_CANCEL) { closesocket(lfd); g_err = ""; return 1; }
if (hr_usable()) {
            hr_host_draw(code, l2, l3, col3, g_one);
        } else {
                ui_clear();
        ui_center(20, "SILVERSKY V0.2", 2, 0xFFFFD040);
        ui_center(64, g_one ? "SALA 1 VS 1 - TU CODIGO:" : "SALA 2 VS 2 - TU CODIGO:", 1, 0xFFFFFFFF);
        { char pc[24]; code_pretty(code, pc); ui_center(84, pc, 2, 0xFFFFFF40); }
        ui_center(116, "DASELO A TU AMIGO", 1, 0xFFC0C0FF);
        ui_center(136, l2, 1, 0xFFC0C0FF);
        ui_center(154, l3, 1, col3);
        ui_center(176, "ESPERANDO AL AMIGO...", 1, 0xFFFFFFFF);
        ui_center(200, "O: CANCELAR", 1, 0xFF8080A0);
}
                present();
        {
            int r = fd_wait(lfd, POLLIN, 0);
            if (r > 0) {
                struct sockaddr_in pa;
                socklen_t pl = sizeof pa;
                int c;
                memset(&pa, 0, sizeof pa);
                c = accept(lfd, (struct sockaddr *)&pa, &pl);
                if (c >= 0) {
                    uint32_t pip = ntohl(pa.sin_addr.s_addr);
                    logf_("conexion entrante de %u.%u.%u.%u", IP4(pip));
                    g_net = c; sock_nodelay(c); break;
                }
                logf_("accept fallo (errno=%d)", errno);
            }
#ifdef NESNET_HOST
            sleep_ms(16);
#endif
        }
    }
    closesocket(lfd);
    ui_show("AMIGO CONECTADO", "MIDIENDO LATENCIA...", NULL);
    if (!handshake_host4(&D)) { net_close(); return 0; }
    return run_online4(1, D);
}

static int run_host4(void)
{
    int ok = run_host4_inner();
    upnp_close();
    return ok;
}

static int run_client4(void)
{
    char code[20];
    uint32_t ip;
    int port, D = 0;

    if (g_cfg.code[0]) snprintf(code, sizeof code, "%s", g_cfg.code);
    else if (!ui_enter_code(code)) { g_err = ""; return 1; }

    if (!code_decode(code, &ip, &port)) { logf_("codigo escrito=%s: INVALIDO", code); g_err = "CODIGO INVALIDO"; return 0; }
    logf_("codigo escrito=%s -> destino %u.%u.%u.%u:%d", code, IP4(ip), port);
    net_ensure();
    g_stage = "conectando";
    {
        char l2[48];
        snprintf(l2, sizeof l2, "%u.%u.%u.%u:%d", IP4(ip), port);
        ui_show("CONECTANDO...", l2, NULL);
    }
    g_net = tcp_connect(ip, port, 10000);
    if (g_net < 0) {
        g_err = g_conn_kind == 1 ? "SIN RESPUESTA DEL HOST (10 S)" : "EL HOST RECHAZO LA CONEXION";
        return 0;
    }
    logf_("connect OK en %u ms", (unsigned)g_conn_ms);
    ui_show("CONECTADO", "SINCRONIZANDO...", NULL);
    if (!handshake_client4(&D)) { net_close(); return 0; }
    return run_online4(0, D);
}

static int run_solo(void)
{
    if (!core_load()) return 0;
    sram_begin();                         /* v1.9: carga el guardado de bateria (si el juego lo usa) */
    session_loop(-1, 0, g_maxframes);
    sram_save(0);                         /* v1.9: guarda al salir (si cambio) */
    g_sram_on = 0;
    core_unload();
    return 1;
}

/* ------------------------------------------------------------------ */
/* Programa                                                            */
/* ------------------------------------------------------------------ */
static int g_prepared;
static void app_prepare(const char *argv0)
{
    if (g_prepared) return;
    g_prepared = 1;
    if (argv0) {
        const char *s = strrchr(argv0, '/');
        if (s && s > argv0) {
            size_t n = (size_t)(s - argv0);
            if (n < sizeof g_dir) { memcpy(g_dir, argv0, n); g_dir[n] = 0; }
        }
    }
    {
        char p[300], q[300];
        snprintf(p, sizeof p, "%s/silversky.log", g_dir);
        snprintf(q, sizeof q, "%s/silversky.old.log", g_dir);
        remove(q);
        rename(p, q);                     /* conserva el log de la vez anterior */
        g_log = fopen(p, "w");
    }
    logf_("SilverSky v0.3.2 (ROMs en .zip; al cerrar el menu R3 los botones apretados no llegan al juego; menus nuevos a 1280x720 con caratulas en covers/; menu en partida con R3; 6 ranuras de estado; O sale al XMB desde el menu principal; estados guardados online: guarda y carga el host; menus siempre a pantalla completa; codigo de sala guardado al unirse; salto de dibujo si va atrasado) - dir=%s", g_dir);
    cfg_load();
    logf_("config: res=%d render=%s zoom=%d audio=%s", g_cfg.res, g_cfg.render ? "cpu" : "gpu", g_cfg.zoom, g_cfg.audio ? "on" : "off");
    opts_load();                          /* v1.8.2: pantalla y mandos guardados en opciones.txt */
}

static int app_main(const char *argv0)
{
    int choice = -1, from_cfg;

    app_prepare(argv0);

    /* v1.7: arranca en stand-by, sin ROM. La ROM se elige en el menu (ELEGIR ROM) antes de crear/unirse/jugar */
    logf_("stand-by: sin ROM elegida (roms en %s/roms)", g_dir);

    core_boot();

    /* v1.9: si hay una ultima ROM recordada y el archivo sigue en la carpeta, queda ya elegida (el juego sigue sin arrancar) */
    if (g_last_rom[0]) {
        int i, found = -1;
        roms_scan();
        for (i = 0; i < g_nroms; i++) if (!strcmp(g_roms[i].name, g_last_rom)) found = i;
        if (found >= 0 && rom_load(found)) { logf_("ultima ROM recordada y cargada: %s", g_rom_name); g_menu_sel = 1; }
        else logf_("la ultima ROM recordada (%s) ya no esta o no se pudo leer: stand-by", g_last_rom);
    }

    from_cfg = g_cfg.mode[0] != 0;
    if (from_cfg) { logf_("config.txt trae mode=%s: se ignora, primero hay que elegir ROM en el menu", g_cfg.mode); from_cfg = 0; }
    while (g_running) {
        int ok = 1;
        if (choice < 0) choice = ui_menu();
        if (choice < 0) break;
        if (choice == MODE_ROM) {
            if (ui_rom_select()) g_menu_sel = 2;          /* tras elegir, el cursor pasa a CREAR SALA */
            choice = -1;
            continue;
        }
        if (choice == MODE_OPT) {                         /* v1.8.2: OPCIONES (pantalla y mandos) no necesita ROM */
            ui_options();
            choice = -1;
            continue;
        }
        if (!g_rom) { choice = -1; continue; }             /* seguridad: sin ROM no se arranca nada */
        logf_("modo elegido: %s", choice == MODE_SOLO ? "SOLO (2 mandos)" : choice == MODE_HOST1 ? "CREAR SALA 1 VS 1 (host, mando 1)" :
              choice == MODE_JOIN1 ? "UNIRSE 1 VS 1 (mando 2)" : choice == MODE_HOST ? "CREAR SALA 2 VS 2 (host, mandos 1-2)" : "UNIRSE 2 VS 2 (mandos 3-4)");
        g_err = "";
        if (choice == MODE_SOLO) ok = run_solo();
        else if (choice == MODE_HOST1 || choice == MODE_JOIN1) {      /* v0.2: 1 vs 1 (protocolo propio; el 2 vs 2 no se toca) */
            g_one = 1; g_proto = PROTO_VER2;
            ok = choice == MODE_HOST1 ? run_host4() : run_client4();
            g_one = 0; g_proto = PROTO_VER4;
        }
        else if (choice == MODE_HOST) ok = run_host4();
        else ok = run_client4();
        choice = -1;
#ifdef NESNET_HOST
        if (g_maxframes && !g_ui_has_script) g_running = 0;   /* pruebas: una sola sesion (con guion, sigue hasta que se agote) */
#endif
        if (!ok || g_err[0]) {
            logf_("fin con error: %s", g_err);
            if (g_err[0]) ui_message(g_err, "X: VOLVER AL MENU", 600);
        }
    }
    logf_("salida");
    au_close();
    retro_deinit();
    if (g_log) fclose(g_log);
    return 0;
}

#ifdef NESNET_PS3
int main(int argc, const char *argv[])
{
    app_prepare(argc > 0 ? argv[0] : NULL);
    ioPadInit(7);
    /* Modo seguro sin tocar archivos: mantener L1 al arrancar = forzar 720p; R1 = render por CPU */
    {
        int i;
        for (i = 0; i < 25; i++) {            /* ~0,5 s para que el mando responda */
            padData *d = pad_read(0);
            if (d->BTN_L1) { g_cfg.res = 720; }
            if (d->BTN_R1) { g_cfg.render = 1; }
            if (d->BTN_R2) { g_cfg.audio = 0; }
            usleep(20000);
        }
        if (g_cfg.res || g_cfg.render) logf_("config final: res=%d render=%s", g_cfg.res, g_cfg.render ? "cpu" : "gpu");
    }
    platform_init();
    au_open();
    return app_main(argc > 0 ? argv[0] : NULL);
}
#endif

#ifdef NESNET_HOST
/* Pruebas en PC:
 *   silversky_test ROM local   FRAMES            -> sin retraso, 2 jugadores simulados
 *   silversky_test ROM ref     FRAMES D          -> referencia local con retraso D
 *   silversky_test ROM host    FRAMES PUERTO [D] -> host de red
 *   silversky_test ROM client  FRAMES PUERTO     -> cliente de red (127.0.0.1)
 *   nesnet_test --ui DIR                      -> vuelca pantallas de la interfaz en PPM
 */
static void dump_ppm(const char *path)
{
    FILE *f = fopen(path, "wb");
    int i;
    if (!f) return;
    if (g_hr_on) {
        fprintf(f, "P6\n%d %d\n255\n", HR_W, HR_H);
        for (i = 0; i < HR_W * HR_H; i++) {
            uint8_t px[3] = { (uint8_t)(g_hr[i] >> 16), (uint8_t)(g_hr[i] >> 8), (uint8_t)g_hr[i] };
            fwrite(px, 1, 3, f);
        }
        fclose(f);
        return;
    }
    fprintf(f, "P6\n%d %d\n255\n", SCR_W, SCR_H);
    for (i = 0; i < SCR_W * SCR_H; i++) {
        uint8_t px[3] = { (uint8_t)(g_fb[i] >> 16), (uint8_t)(g_fb[i] >> 8), (uint8_t)g_fb[i] };
        fwrite(px, 1, 3, f);
    }
    fclose(f);
}

int main(int argc, char **argv)
{
    const char *mode;
    uint32_t frames;
    int D = 6, port = 7777, ok = 1;

    if (argc >= 3 && !strcmp(argv[1], "--hr")) {
        /* prueba v0.3.0: dibuja una pantalla de muestra y vuelca g_hr (argv[2] = carpeta) */
        static uint8_t dummy[4];
        int d9[10] = { 1, 9, 0, 2, 4, 5, 3, 1, 8, 7 }, kinds[5] = { MK_CONT, MK_SAVE, MK_LOAD, MK_RESET, MK_EXIT }, ex[STATE_SLOTS] = { 1, 0, 1, 0, 0, 0 }, i, x, y;
        const char *names[] = { "options", "code", "host", "menu4", "solo", "solo_c1", "solo_c2", "show", "solo_n", "menu_norom", "menu_rom" };
        g_rom = dummy; snprintf(g_rom_name, sizeof g_rom_name, "Mega Man X.sfc");
        for (y = 0; y < SCR_H; y++) for (x = 0; x < SCR_W; x++) g_fb_save[y * SCR_W + x] = 0xFF000000u | ((uint32_t)(40 + y / 2) << 16) | ((uint32_t)(90 + x / 3) << 8) | (uint32_t)(200 - y / 3) | (((x / 16 + y / 16) & 1) ? 0x202020u : 0);
        if (!hr_prepare()) { printf("hr_prepare fallo\n"); return 2; }
        g_screen = 1; g_volume = 80; g_netinfo = 1; g_state_slot = 2;
        for (i = 0; i < 11; i++) {
            char path[400];
            FILE *f;
            int k;
            switch (i) {
            case 0: hr_opt_draw(1); break;
            case 1: hr_code_draw(d9, 4, 0); break;
            case 2: hr_host_draw("1902453187", "PUERTO TCP 7777", "UPNP: PUERTO ABIERTO", 0xFF80FF80u, 1); break;
            case 3: hr_menu4_draw(1); break;
            case 4: hr_alt_build(); hr_solo_draw(kinds, 5, 1, -1, 0, NULL, ex); break;
            case 5: hr_alt_build(); hr_solo_draw(kinds, 5, 3, MK_RESET, 1, NULL, ex); break;
            case 6: hr_alt_build(); hr_solo_draw(kinds, 5, 2, MK_LOAD, 1, NULL, ex); break;
            case 7: hr_show_draw("CONECTANDO...", "190.245.31.87:7777", NULL); break;
            case 8: hr_alt_build(); hr_solo_draw(kinds, 3, 2, -1, 1, NULL, ex); break;
            case 9: g_rom = NULL; hr_menu_draw(3, 0, ""); g_rom = dummy; break;
            default: hr_menu_draw(1, 1, g_rom_name); break;
            }
            snprintf(path, sizeof path, "%s/hr_%s.ppm", argv[2], names[i]);
            f = fopen(path, "wb");
            if (!f) return 2;
            fprintf(f, "P6\n%d %d\n255\n", HR_W, HR_H);
            for (k = 0; k < HR_W * HR_H; k++) { uint8_t px[3] = { (uint8_t)(g_hr[k] >> 16), (uint8_t)(g_hr[k] >> 8), (uint8_t)g_hr[k] }; fwrite(px, 1, 3, f); }
            fclose(f);
        }
        return 0;
    }
    if (argc >= 3 && !strcmp(argv[1], "--ui")) {
        char p[300];
        static const char *items[3] = { "SOLO - 2 MANDOS", "CREAR SALA 2 VS 2 (HOST)", "UNIRSE A SALA 2 VS 2" };
        int i;
        ui_clear();
        ui_center(20, "SILVERSKY V0.2", 2, 0xFFFFD040);
        ui_center(46, "SNES CON NETPLAY PARA PS3", 1, 0xFFC0C0FF);
        for (i = 0; i < 3; i++) {
            char line[40];
            snprintf(line, sizeof line, "%s %s", i == 0 ? ">" : " ", items[i]);
            ui_center(90 + i * 22, line, 1, i == 0 ? 0xFFFFFFFF : 0xFF8080A0);
        }
        snprintf(p, sizeof p, "%s/menu.ppm", argv[2]); dump_ppm(p);
        {
            char code[20];
            code_encode(((uint32_t)181 << 24) | (45u << 16) | (200u << 8) | 17u, 7777, code);
            ui_clear();
            ui_center(20, "SILVERSKY V0.2", 2, 0xFFFFD040);
            ui_center(64, "TU CODIGO DE SALA:", 1, 0xFFFFFFFF);
            { char pc[24]; code_pretty(code, pc); ui_center(84, pc, 2, 0xFFFFFF40); }
            ui_center(116, "DASELO A TU AMIGO", 1, 0xFFC0C0FF);
            ui_center(136, "PUERTO 7777", 1, 0xFFC0C0FF);
            ui_center(170, "ESPERANDO AL AMIGO...", 1, 0xFFFFFFFF);
            ui_center(200, "O: CANCELAR", 1, 0xFF8080A0);
            snprintf(p, sizeof p, "%s/host.ppm", argv[2]); dump_ppm(p);
        }
        return 0;
    }

    if (argc < 4) { fprintf(stderr, "uso: %s ROM modo FRAMES [...]\n", argv[0]); return 2; }
    mode = argv[2];
    frames = (uint32_t)atoi(argv[3]);
    if (argc > 4) port = atoi(argv[4]);
    g_maxframes = frames;
    if (getenv("NESNET_UI")) { g_ui_script = getenv("NESNET_UI"); g_ui_has_script = 1; }   /* pruebas del menu de salir */
    if (getenv("NESNET_R2")) g_exit_at = (uint32_t)atoi(getenv("NESNET_R2"));
    if (getenv("NESNET_R2B")) g_exit_at2 = (uint32_t)atoi(getenv("NESNET_R2B"));
    if (getenv("NESNET_NETINFO")) g_netinfo = atoi(getenv("NESNET_NETINFO"));   /* prueba: modo de info de red */
    if (getenv("NESNET_NOSKIP")) sk_on = 0;                                     /* prueba v0.2.5: sin salto de dibujo */
    if (getenv("NESNET_FAKEDRAW_MS")) g_fake_draw_us = (unsigned long long)atoi(getenv("NESNET_FAKEDRAW_MS")) * 1000ULL;
    if (getenv("NESNET_RESET_REF")) {                                            /* prueba v1.9.1: reinicios de la referencia "a" o "a,b" */
        const char *rr = getenv("NESNET_RESET_REF");
        g_ref_reset[0] = (uint32_t)atoi(rr);
        if (strchr(rr, ',')) g_ref_reset[1] = (uint32_t)atoi(strchr(rr, ',') + 1);
    }
    signal(SIGPIPE, SIG_IGN);
    if (!strcmp(mode, "app")) {
        /* flujo real: lee DIR/config.txt y ejecuta app_main (argv[4] = carpeta) */
        char exe[300];
        int rc;
        snprintf(exe, sizeof exe, "%s/EBOOT.BIN", argv[4]);
        if (getenv("NESNET_UI")) { g_ui_script = getenv("NESNET_UI"); g_ui_has_script = 1; }
        if (getenv("NESNET_R2")) g_exit_at = (uint32_t)atoi(getenv("NESNET_R2"));
        rc = app_main(exe);
        printf("RESULT mode=app frames=%u hash=%08X desyncs=%d rc=%d\n", (unsigned)g_frames_done,
               (unsigned)g_run_hash, g_desyncs, rc);
        return rc;
    }
    snprintf(g_cfg.rom, sizeof g_cfg.rom, "%s", argv[1]);
    g_cfg.port = port;
    if (!read_whole_file(argv[1], &g_rom, &g_romsz)) { fprintf(stderr, "no puedo leer la ROM\n"); return 2; }
    g_romcrc = crc32_buf(g_rom, g_romsz);
    snprintf(g_dir, sizeof g_dir, "/tmp");
    core_boot();

    if (!strcmp(mode, "local")) {
        core_load(); session_loop(-1, 0, frames); core_unload();
    } else if (!strcmp(mode, "sticktest")) {
        /* v1.8.1: prueba de la palanca: recorre los 256 valores de cada eje y comprueba direcciones y zona muerta */
        unsigned v, bad = 0;
        for (v = 0; v < 256; v++) {
            uint16_t h = stick_nes_bits(v, 128), w = stick_nes_bits(128, v);
            int exp = v < 78 ? -1 : v > 178 ? 1 : 0;
            if (h != (exp < 0 ? NB_LEFT : exp > 0 ? NB_RIGHT : 0)) bad++;
            if (w != (exp < 0 ? NB_UP : exp > 0 ? NB_DOWN : 0)) bad++;
        }
        if (stick_nes_bits(0, 0) != (NB_LEFT | NB_UP) || stick_nes_bits(255, 255) != (NB_RIGHT | NB_DOWN) ||
            stick_nes_bits(255, 0) != (NB_RIGHT | NB_UP) || stick_nes_bits(0, 255) != (NB_LEFT | NB_DOWN) ||
            stick_nes_bits(128, 128) != 0 || stick_nes_bits(120, 140) != 0) bad++;
        printf("sticktest bad=%u (centro 128, zona muerta 78..178)\n", bad);
        return bad != 0;
    } else if (!strcmp(mode, "screentest")) {
        /* v1.8.2: pruebas del escalado de pantalla (canvas_blit_cpu, la misma funcion que usa la PS3) */
        static const int dims[4][3] = { { 1280, 720, 3 }, { 1920, 1080, 3 }, { 1920, 1080, 4 }, { 720, 480, 2 } };
        unsigned bad = 0;
        int di, md;
        static uint32_t fbuf[SCR_W * SCR_H], buf[1920 * 1080], ref[1920 * 1080];
        int x, y;
        for (y = 0; y < SCR_H; y++) for (x = 0; x < SCR_W; x++) fbuf[y * SCR_W + x] = 0xFF000000u | ((uint32_t)y << 8) | (uint32_t)x;
        for (di = 0; di < 4; di++) {
            int dw = dims[di][0], dh = dims[di][1], z = dims[di][2];
            for (md = 0; md < 3; md++) {
                int oh = SCR_H * z, ow = screen_out_w(md, dw, oh, z);
                int ox = (dw - ow) / 2, oy = (dh - oh) / 2, errs = 0, dx, dy;
                unsigned fc = 0;
                size_t i;
                for (i = 0; i < (size_t)dw * dh; i++) buf[i] = 0xDEADBEEFu;     /* basura previa: lo de fuera de la imagen debe quedar en 0 */
                canvas_blit_cpu(buf, dw, dh, md, z, fbuf, &fc);
                for (dy = 0; dy < dh; dy++)
                    for (dx = 0; dx < dw; dx++) {
                        uint32_t got = buf[(size_t)dy * dw + dx], want = 0;
                        if (dy >= oy && dy < oy + oh && dx >= ox && dx < ox + ow)
                            want = fbuf[((dy - oy) / z) * SCR_W + ((dx - ox) * SCR_W / ow)];
                        if (got != want) errs++;
                    }
                /* modo 0: identico, byte a byte, al escalado de la v1.8.1 (cada pixel repetido z veces) */
                if (md == 0) {
                    for (i = 0; i < (size_t)dw * dh; i++) ref[i] = 0;
                    for (dy = 0; dy < oh; dy++)
                        for (dx = 0; dx < SCR_W * z; dx++)
                            ref[(size_t)(oy + dy) * dw + ox + dx] = fbuf[(dy / z) * SCR_W + dx / z];
                    if (memcmp(buf, ref, (size_t)dw * dh * 4)) errs++;
                }
                /* repeticion de columnas en la primera fila: original a 720p = todas x3; 4:3 = 192 de x4 y 64 de x3; 16:9 = todas x5 */
                if (dw == 1280 && dh == 720) {
                    int run = 1, n3 = 0, n4 = 0, n5 = 0, nx = 0, row = oy * dw + ox;
                    for (dx = 1; dx <= ow; dx++) {
                        if (dx < ow && buf[row + dx] == buf[row + dx - 1]) { run++; continue; }
                        if (run == 3) n3++; else if (run == 4) n4++; else if (run == 5) n5++; else nx++;
                        run = 1;
                    }
                    if (md == 0 && !(ow == 768 && n3 == 256 && !n4 && !n5 && !nx)) errs++;
                    if (md == 1 && !(ow == 960 && n4 == 192 && n3 == 64 && !n5 && !nx)) errs++;
                    if (md == 2 && !(ow == 1280 && n5 == 256 && !n3 && !n4 && !nx)) errs++;
                }
                printf("screentest %dx%d z=%d modo=%d: imagen %dx%d en (%d,%d) errores=%d\n", dw, dh, z, md, ow, oh, ox, oy, errs);
                bad += (unsigned)errs;
            }
        }
        /* cambiar de modo no deja residuo: 16:9 durante 8 cuadros y luego original; a los 4 cuadros los bordes quedan limpios */
        {
            int dw = 1280, dh = 720, z = 3, k, dx, dy, errs = 0;
            unsigned fc = 0;
            size_t i;
            for (i = 0; i < (size_t)dw * dh; i++) buf[i] = 0;
            for (k = 0; k < 8; k++) canvas_blit_cpu(buf, dw, dh, 2, z, fbuf, &fc);
            for (k = 0; k < 4; k++) canvas_blit_cpu(buf, dw, dh, 0, z, fbuf, &fc);
            for (dy = 0; dy < dh; dy++)
                for (dx = 0; dx < dw; dx++)
                    if ((dx < 256 || dx >= 1024) && buf[(size_t)dy * dw + dx] != 0) errs++;
            printf("screentest cambio 16:9 -> original: residuos=%d\n", errs);
            bad += (unsigned)errs;
        }
        /* costo relativo en CPU (solo orientativo, en PC) */
        {
            int dw = 1280, dh = 720, z = 3, k;
            unsigned fc = 0;
            uint32_t t0;
            for (md = 0; md < 3; md++) {
                t0 = now_ms();
                for (k = 0; k < 600; k++) canvas_blit_cpu(buf, dw, dh, md, z, fbuf, &fc);
                printf("screentest tiempo modo %d: %u ms por 600 cuadros (PC)\n", md, (unsigned)(now_ms() - t0));
            }
        }
        printf("screentest TOTAL bad=%u\n", bad);
        return bad != 0;
    } else if (!strcmp(mode, "ref4")) {
        /* v1.8: referencia de 4 jugadores locales con el mismo retraso D */
        D = argc > 4 ? atoi(argv[4]) : 6;
        g_four = 1;
        core_load4(); session_loop(-2, D, frames); core_unload();
        g_four = 0;
    } else if (!strcmp(mode, "host4")) {
        int lfd = tcp_listen(port);
        if (lfd < 0) { fprintf(stderr, "no puedo escuchar\n"); return 2; }
        if (argc > 5) g_cfg.delay = atoi(argv[5]);
        g_net = accept(lfd, NULL, NULL);
        closesocket(lfd);
        sock_nodelay(g_net);
        ok = handshake_host4(&D);
        if (ok) ok = run_online4(1, D);
        if (!ok) fprintf(stderr, "ERROR: %s\n", g_err);
    } else if (!strcmp(mode, "client4")) {
        int tries;
        for (tries = 0; tries < 50 && g_net < 0; tries++) {
            g_net = tcp_connect(0x7F000001u, port, 2000);
            if (g_net < 0) sleep_ms(100);
        }
        if (g_net < 0) { fprintf(stderr, "no pude conectar\n"); return 2; }
        ok = handshake_client4(&D);
        if (ok) ok = run_online4(0, D);
        if (!ok) fprintf(stderr, "ERROR: %s\n", g_err);
    } else if (!strcmp(mode, "codetest")) {
        /* v1.9.1: codigo de 10 digitos (solo la IP); el puerto sale de config.txt */
        char c[20], pc[24]; uint32_t ip; int p, n = 0, bad = 0;
        uint32_t t;
        g_cfg.port = 7777;
        for (t = 0; t < 200000; t++) {
            uint32_t a = t * 2654435761u;
            code_encode(a ? a : 1, 7777, c);
            if (strlen(c) != 10 || !code_decode(c, &ip, &p) || ip != (a ? a : 1) || p != 7777) bad++;
            code_pretty(c, pc);
            if (strlen(pc) != 12 || !code_decode(pc, &ip, &p) || ip != (a ? a : 1)) bad++;      /* con espacios tambien */
            n++;
        }
        code_encode(0xB92DC811u, 7777, c);                                  /* 185.45.200.17 */
        if (strcmp(c, "3106785297")) { bad++; printf("codetest muestra: %s\n", c); }
        code_encode(0x01020304u, 7777, c);
        if (strcmp(c, "0016909060")) { bad++; printf("codetest muestra2: %s\n", c); }
        if (code_decode("12345", &ip, &p) || code_decode("12345678901", &ip, &p) || code_decode("4294967296", &ip, &p) ||
            code_decode("0000000000", &ip, &p) || code_decode("123456789012345", &ip, &p)) { bad++; printf("codetest: acepto un codigo malo\n"); }
        printf("codetest n=%d bad=%d\n", n, bad);
        return bad != 0;
    } else if (!strcmp(mode, "statetest")) {
        /* v1.9.1: guardar y cargar estado. Tras cargar, los siguientes cuadros deben dar exactamente los mismos CRC de video. */
        static uint32_t ca[300], cb[300], cc[300];
        uint32_t f;
        size_t n;
        uint8_t *buf;
        unsigned bad = 0;
        core_load();
        n = retro_serialize_size();
        printf("statetest: el nucleo pide %u bytes de estado\n", (unsigned)n);
        for (f = 0; f < 300; f++) step_frame(script_input(0, f), script_input(1, f));
        buf = (uint8_t *)malloc(n);
        if (!buf || !retro_serialize(buf, n)) { printf("statetest: no pude serializar\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); ca[f - 300] = g_frame_crc; }
        if (!retro_unserialize(buf, n)) { printf("statetest: no pude cargar\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); cb[f - 300] = g_frame_crc; }
        for (f = 0; f < 300; f++) if (ca[f] != cb[f]) bad++;
        printf("statetest memoria: cuadros distintos tras cargar = %u\n", bad);
        /* por archivo: guardar en la ranura 2, seguir, cargar, repetir */
        retro_unserialize(buf, n);
        free(buf);
        mkdir("/tmp/nn_state_test", 0777);
        snprintf(g_dir, sizeof g_dir, "/tmp/nn_state_test");
        if (!state_save(1)) { printf("statetest: no pude guardar archivo\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); ca[f - 300] = g_frame_crc; }
        if (state_load(1) != 1) { printf("statetest: no pude cargar archivo\n"); return 1; }
        for (f = 300; f < 600; f++) { step_frame(script_input(0, f), script_input(1, f)); cc[f - 300] = g_frame_crc; }
        {
            unsigned bad2 = 0;
            for (f = 0; f < 300; f++) if (ca[f] != cc[f]) bad2++;
            printf("statetest archivo: cuadros distintos tras cargar = %u\n", bad2);
            bad += bad2;
        }
        printf("statetest existe(ranura 2)=%d existe(ranura 1)=%d\n", state_exists(1), state_exists(0));
        core_unload();
        return bad != 0;
    }
    printf("RESULT mode=%s frames=%u hash=%08X desyncs=%d D=%d first_desync=%d\n", mode,
           (unsigned)g_frames_done, (unsigned)g_run_hash, g_desyncs, D,
           g_first_desync == NO_FRAME ? -1 : (int)g_first_desync);
    return ok ? 0 : 1;
}
#endif
