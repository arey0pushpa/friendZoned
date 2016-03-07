#include <stdio.h>
#include <stdlib.h>


#define M 4

_Bool nondet_bool();
unsigned int nondet_uint();



typedef unsigned __CPROVER_bitvector[M] bitvector; 


int main ()

{    
    bitvector b1, b2, b3;
    _Bool b;
    unsigned int x,y;

    b1 = 0b1010;
    b2 = 0b1;
    b3 = 0b11;
    y = b3;
    x  = b1 & ( b2  << y);
    
    if ( x == 0) 
        printf("its false ");
    else 
        printf("okay");

    assert(0);
    return 0; 
}



