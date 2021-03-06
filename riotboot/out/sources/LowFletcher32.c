/* 
  This file was generated by KreMLin <https://github.com/FStarLang/kremlin>
  KreMLin invocation: krml -verbose -d reachability -I . -I includes -tmpdir /Users/syuan/GoogleDrive/PhD/FstarCode/riotbootAPI/out/sources -no-prefix FStarFiles /Users/syuan/GoogleDrive/PhD/FstarCode/riotbootAPI/out/out.krml -ccopt -O0 mymain.c -add-include "kremlin/internal/compat.h" -bundle LowStar.*,Prims -bundle FStar.* -o /Users/syuan/GoogleDrive/PhD/FstarCode/riotbootAPI/out/main
  F* version: cfb65605
  KreMLin version: 03ccd42f
 */

#include "LowFletcher32.h"

K___uint32_t_uint32_t
LowFletcher32_dowhile(uint32_t t, uint32_t tlen, uint16_t *d, uint32_t s1, uint32_t s2)
{
  switch (tlen)
  {
    case 0U:
      {
        return ((K___uint32_t_uint32_t){ .fst = s1, .snd = s2 });
      }
    default:
      {
        uint32_t data = FStar_UInt32_uint_to_t(FStar_UInt16_v(d[t - tlen]));
        uint32_t sum1 = s1 + data;
        uint32_t sum2 = s2 + sum1;
        return LowFletcher32_dowhile(t, tlen - (uint32_t)1U, d, sum1, sum2);
      }
  }
}

K___uint32_t_uint32_t
LowFletcher32_while_t(uint16_t words, uint16_t *data, uint32_t s1, uint32_t s2)
{
  switch (words)
  {
    case 0U:
      {
        return ((K___uint32_t_uint32_t){ .fst = s1, .snd = s2 });
      }
    default:
      {
        uint16_t tlen;
        if (words > (uint16_t)359U)
          tlen = (uint16_t)359U;
        else
          tlen = words;
        uint32_t tlen_32 = (uint32_t)tlen;
        K___uint32_t_uint32_t scrut = LowFletcher32_dowhile(tlen_32, tlen_32, data, s1, s2);
        uint32_t sum1 = scrut.fst;
        uint32_t sum2 = scrut.snd;
        return
          LowFletcher32_while_t(words - tlen,
            data,
            (sum1 & (uint32_t)0xffffU) + (sum1 >> (uint32_t)16U),
            (sum2 & (uint32_t)0xffffU) + (sum2 >> (uint32_t)16U));
      }
  }
}

uint32_t LowFletcher32_fletcher32(uint16_t words, uint16_t *data)
{
  K___uint32_t_uint32_t
  scrut = LowFletcher32_while_t(words, data, (uint32_t)0xffffU, (uint32_t)0xffffU);
  uint32_t s1 = scrut.fst;
  uint32_t s2 = scrut.snd;
  uint32_t sum1 = (s1 & (uint32_t)0xffffU) + (s1 >> (uint32_t)16U);
  uint32_t sum2 = (s2 & (uint32_t)0xffffU) + (s2 >> (uint32_t)16U);
  return sum2 << (uint32_t)16U | sum1;
}

