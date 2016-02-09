#include <stdio.h>
#include <stdlib.h>

#define M 10	       
#define bigLen  1023

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[bigLen] bigVector;
 

bigVector nondetBV() {
     bigVector bv;
     return bv;
}

int pop(unsigned x)
{
        x = x - ((x >> 1) & 0x55555555);
        x = (x & 0x33333333) + ((x >> 2) & 0x33333333);
        x = (x + (x >> 4)) & 0x0F0F0F0F;
        x = x + (x >> 8);
        x = x + (x >> 16);
        return x & 0x0000003F;
}



int main (int argc, char** argv)

{    

    unsigned int i, j; 

    __CPROVER_bitvector[100] B0 , B1 , B2 , B3 , B4 , B5;

    B0 = 0b1;
    _Bool b1 , b2;

    B1 = nondetBV();

    printf(" The value of the big Bitvector is %d ", B1);
   

    B2 = 0b1110111111111111111111111111111;
 
    
    B3 = 0b1111111111111111111111111111111111111111111111111111111111111;

    B4 = B3 & (B2); 

    b1 = B3 & ( B0 << 45);
    B5 = B3 & ( B0 << 45);

    printf(" B4 = %d", B4);
    printf(" B5 = %d", B5);
    printf(" b1 = %d", b1);


    assert(0);
    return 0; 
}



