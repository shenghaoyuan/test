//#include<unistd.h>
#include<stdio.h>
#include<stdint.h>
#include<stdlib.h>
#include<stddef.h>

uint32_t fletcher32(const uint16_t *data, size_t words)
{
    uint32_t sum1 = 0xffff, sum2 = 0xffff, sumt = 0xffff;

    while (words) {
        unsigned tlen = words > 359 ? 359 : words;
        words -= tlen;
        do {
            sumt = sum1;
            sum2 += sum1 += *data++;
            printf("data:0x:%04x 0d:%d\n", (sum1-sumt), (sum1-sumt));
            //printf("dowhile_sum1:0d:%d 0x:%x  dowhile_sum2:0d:%d 0x:%x\n", sum1, sum1, sum2, sum2);
        } while (--tlen);
        sum1 = (sum1 & 0xffff) + (sum1 >> 16);
        sum2 = (sum2 & 0xffff) + (sum2 >> 16);
        //printf("while_sum1:0d:%d 0x:%x  while_sum2:0d:%d 0x:%x\n", sum1, sum1, sum2, sum2);
    }
    /* Second reduction step to reduce sums to 16 bits */
    sum1 = (sum1 & 0xffff) + (sum1 >> 16);
    sum2 = (sum2 & 0xffff) + (sum2 >> 16);
    //printf("re_sum1:0d:%d 0x:%x re_sum2:0d:%d 0x:%x\n", sum1, sum1, sum2, sum2);
    return (sum2 << 16) | sum1;
}

struct rb_hdr_t {
    uint32_t magic_number;
    uint32_t version;
    uint32_t start_addr;
    uint32_t chksum;
};

int main(){
    printf("Hello Testing:\n");
    struct rb_hdr_t h0 = {0x544f4952, 0x1007, 0x00001100, 0xffffffff};
    struct rb_hdr_t h1 = {0x544f4952, 0x14, 0x00010010, 0xffffffff};
    struct rb_hdr_t *p0 = &h0;
    struct rb_hdr_t *p1 = &h1;

    uint32_t c0 = fletcher32((uint16_t *) p0, 0x6);
    printf("c0=0x:%04x 0d:%d\n", c0, c0);
    uint32_t c1 = fletcher32((uint16_t *) p1, 0x6);
    printf("c1=0x:%04x 0d:%d\n", c1, c1);

    printf("End Testing!\n");
    return 0;
}
