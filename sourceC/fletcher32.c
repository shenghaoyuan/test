/*
 * Copyright 2015 Eistec AB
 *
 * This file is subject to the terms and conditions of the GNU Lesser
 * General Public License v2.1. See the file LICENSE in the top level
 * directory for more details.
 */

/**
 * @ingroup     sys_checksum_fletcher32
 * @{
 *
 * @file
 * @brief       Fletcher32 implementation
 *
 * @author      Joakim Nohlgård <joakim.nohlgard@eistec.se>
 *
 * @}
 */

#include "unaligned.h"
#include "checksum/fletcher32.h"

uint32_t fletcher32(const uint16_t *data, size_t words)
{
    uint32_t sum1 = 0xffff, sum2 = 0xffff;
    /*unsigned tlen; %declaring here is better*/
    while (words) {
        unsigned tlen = words > 359 ? 359 : words;
        words -= tlen; /* words has type of size_t while tlen has type of unsigned!!!*/
        do {
            sum2 += sum1 += unaligned_get_u16(data++); /* *(data++) = the address+16 e.g. from 0xd300 -> 0x d310 (54016 -> 54032)*/
        } while (--tlen);
        sum1 = (sum1 & 0xffff) + (sum1 >> 16);
        sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    }
    /* Second reduction step to reduce sums to 16 bits */
    sum1 = (sum1 & 0xffff) + (sum1 >> 16);
    sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    return (sum2 << 16) | sum1;
}

/* I believe this one from wiki is better! 
   try to verify it in the future in F* or Coq!!! related work???
   
uint32_t fletcher32(const uint16_t *data, size_t len) {
	uint32_t c0, c1;
	len = (len + 1) & ~1;
	for (c0 = c1 = 0; len > 0; ) {
		size_t blocklen = len;
		if (blocklen > 360*2) {
			blocklen = 360*2;
		}
		len -= blocklen;
		do {
			c0 = c0 + *data++;
			c1 = c1 + c0;
		} while ((blocklen -= 2));
		c0 = c0 % 65535;
		c1 = c1 % 65535;
	}
	return (c1 << 16 | c0);
}
 */
