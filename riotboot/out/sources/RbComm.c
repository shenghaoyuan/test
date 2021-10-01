/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -verbose -d reachability -I . -I includes -tmpdir /Users/syuan/GoogleDrive/PhD/FstarCode/riotbootAPI/out/sources -no-prefix FStarFiles /Users/syuan/GoogleDrive/PhD/FstarCode/riotbootAPI/out/out.krml -ccopt -O0 mymain.c -add-include "kremlin/internal/compat.h" -bundle LowStar.*,Prims -bundle FStar.* -o /Users/syuan/GoogleDrive/PhD/FstarCode/riotbootAPI/out/main
  F* version: cfb65605
  KreMLin version: 03ccd42f
 */

#include "RbComm.h"

uint32_t RbComm___proj__Mkrb_hdr_t__item__magic_number(RbComm_rb_hdr_t projectee)
{
  return projectee.magic_number;
}

uint32_t RbComm___proj__Mkrb_hdr_t__item__version(RbComm_rb_hdr_t projectee)
{
  return projectee.version;
}

uint32_t RbComm___proj__Mkrb_hdr_t__item__start_addr(RbComm_rb_hdr_t projectee)
{
  return projectee.start_addr;
}

uint32_t RbComm___proj__Mkrb_hdr_t__item__chksum(RbComm_rb_hdr_t projectee)
{
  return projectee.chksum;
}

Prims_int RbComm_rb_slot_numof = (krml_checked_int_t)2;

RbComm_rb_hdr_t
RbComm_rb_slot0 =
  {
    .magic_number = (uint32_t)0x544f4952U,
    .version = (uint32_t)0x1007U,
    .start_addr = (uint32_t)0x00001100U,
    .chksum = (uint32_t)0xbf96bea8U
  };

RbComm_rb_hdr_t
RbComm_rb_slot1 =
  {
    .magic_number = (uint32_t)0x544f4952U,
    .version = (uint32_t)0x14U,
    .start_addr = (uint32_t)0x00010010U,
    .chksum = (uint32_t)0x5deb9dc6U
  };

