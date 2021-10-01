/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -verbose -d reachability -I . -I includes -tmpdir /home/shyuan/2-FMCAD2021/riotboot/out/sources -no-prefix FStarFiles /home/shyuan/2-FMCAD2021/riotboot/out/out.krml -ccopt -O0 mymain.c -add-include "kremlin/internal/compat.h" -bundle LowStar.*,Prims -bundle FStar.* -o /home/shyuan/2-FMCAD2021/riotboot/out/main
  F* version: <unknown>
  KreMLin version: 03ccd42f
 */

#ifndef __Hdr_H
#define __Hdr_H
#include "kremlin/internal/compat.h"
#include "kremlib.h"


#include "Fletcher32.h"
#include "Riotboot.h"

void Hdr_rb_hdr_t2uint16_t(Riotboot_hdr_t s, uint16_t *d);

uint32_t Hdr_rb_hdr_checksum(Riotboot_hdr_t *b);

bool Hdr_riotboot_hdr_validate(Riotboot_hdr_t *riotboot_hdr);


#define __Hdr_H_DEFINED
#endif