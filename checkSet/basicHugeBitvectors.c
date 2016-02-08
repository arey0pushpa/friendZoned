#include <stdio.h>
#include <stdlib.h>

//  THIS CODE IS FOR THE Arbitary grah with 3 conncted and 4 conncted added constrint --------------------------------
// Starting with N  = 5

#define M 10	       
#define N 5
#define snareLength 10
#define bigLen  1023

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[snareLength] snareVector; 
typedef unsigned __CPROVER_bitvector[bigLen] bigVector;
 
//Constrine the value between 0 and 1
unsigned int  nondet (){  
  unsigned int num = nondet_uint();
  __CPROVER_assume( num>= 0 && num  <= 1);
   return num;
};

unsigned int zeroTon(unsigned int n) {
    unsigned int result = nondet_uint();
    __CPROVER_assume(result >=0 && result <=n);
    return result ;
};

bigVector nondetBV() {
     bigVector bv;
     return bv;
}

//  Define the Structure of the Container Going to be used -----------------------------------------
struct EdgeBag
 {
   int ith;
   int jth;
   unsigned int count;
   snareVector  vSnare;
   snareVector tSnare;
   snareVector zebra[snareLength];
   snareVector combinedMask; 
};


// Chck which if at index x its 1 or not 
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
     
    bitvector B1 , B2 ;

    bitvector b;

    B1 = nondetBV();

    printf(" The value of the big Bitvector is %d ", B1);
   
    b = 0b10;
    printf(" The value of the small Bitvector is %d ", B1);

    B2 =  B1 & b;
    printf(" The value of the another big Bitvector is %d ", B1);

    if (B2 & ( 1 << 1) ) {

        printf(" Thsi world is mine and i'm mr. crowley!");

    }





    assert(0);
    return 0; 
}



