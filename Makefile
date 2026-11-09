# SilverSky - SNES con netplay 2 vs 2 para PS3 (PSL1GHT + Snes9x 2010)
# Requiere: PS3DEV y PSL1GHT en el entorno, y el nucleo Snes9x 2010 ya compilado en
# snes9x2010/snes9x2010_libretro_psl1ght.a (lo hace el workflow de GitHub Actions).

TARGET   = SilverSky
TITLE    = SilverSky
APPID    = SILV00001
CONTENTID = UP0001-$(APPID)_00-0000000000000000

LRC      = snes9x2010/libretro/libretro-common

# El nucleo se compila como libreria estatica SIN libretro-common (salvo memory_stream): esas piezas las pone la aplicacion.
LRC_OBJS = $(LRC)/streams/file_stream.o \
           $(LRC)/streams/file_stream_transforms.o \
           $(LRC)/streams/interface_stream.o \
           $(LRC)/streams/rzip_stream.o \
           $(LRC)/streams/trans_stream.o \
           $(LRC)/streams/trans_stream_pipe.o \
           $(LRC)/streams/trans_stream_deflate.o \
           $(LRC)/vfs/vfs_implementation.o \
           $(LRC)/vfs/vfs_hybrid.o \
           $(LRC)/file/file_path.o \
           $(LRC)/file/file_path_io.o \
           $(LRC)/file/rpng_file.o \
           $(LRC)/file/retro_dirent.o \
           $(LRC)/memmap/memalign.o \
           $(LRC)/encodings/encoding_crc32.o \
           $(LRC)/encodings/encoding_deflate.o \
           $(LRC)/encodings/encoding_utf.o \
           $(LRC)/formats/png/rpng.o \
           $(LRC)/formats/png/rpng_encode.o \
           $(LRC)/formats/png/rpng_apng.o \
           $(LRC)/formats/image_transfer.o \
           $(LRC)/formats/webp/rwebp.o \
           $(LRC)/formats/vp8/rvp8.o \
           $(LRC)/formats/dds/rdds.o \
           $(LRC)/compat/compat_strl.o \
           $(LRC)/compat/compat_posix_string.o \
           $(LRC)/compat/compat_strcasestr.o \
           $(LRC)/compat/compat_snprintf.o \
           $(LRC)/compat/fopen_utf8.o \
           $(LRC)/string/stdstring.o \
           $(LRC)/string/rstrtod.o \
           $(LRC)/time/rtime.o \
           $(LRC)/features/features_cpu.o

OFILES   = source/main.o $(LRC_OBJS)

CFLAGS   = -O2 -Wall -std=gnu99 -mcpu=cell $(MACHDEP) -DNESNET_PS3 \
           -I$(PS3DEV)/ppu/include -I$(PSL1GHT)/ppu/include -I$(PSL1GHT)/ppu/include/simdmath \
           -I$(LRC)/include

# Las piezas de libretro-common se compilan con las mismas definiciones que usa el Makefile del nucleo para PS3
$(LRC)/%.o: CFLAGS += -D__LIBRETRO__ -DHAVE_RPNG -DHAVE_RWEBP -DHAVE_RDDS -DINLINE=inline \
                      -D__ppc__ -DMSB_FIRST -D__PS3__ -D__PSL1GHT__ -Wno-unused-function

LDFLAGS  = $(MACHDEP)

LIBS     = snes9x2010/snes9x2010_libretro_psl1ght.a \
           -lrsx -lgcm_sys -lio -laudio -lsysutil -lnetctl -lnet -lsysmodule -lrt -llv2 -lm

# Todo lo que haya en data/ se copia dentro del .pkg (data/USRDIR/config.txt)
PKGFILES = data

BUILDDIR = build

# Icono del XMB (320x176) en la raiz del repo; sin esto PSL1GHT usa uno generico
ICON0    = $(CURDIR)/ICON0.PNG

include $(PSL1GHT)/ppu_rules

# make trae LD=ld por defecto y base_rules solo lo cambia si no existe: forzar ppu-gcc
LD = $(CC)

pkg: $(TARGET).pkg

clean:
	rm -rf $(TARGET)*.pkg $(TARGET).self $(TARGET).elf $(OFILES) $(BUILDDIR)
