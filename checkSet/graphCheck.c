#include <stdio.h>
#include <stdlib.h>


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

    int j; 
    unsigned int pos, i, k, l, w, x, y , iVal, jVal , g, g0, lastg, ng ;
    unsigned int edgePos, bagNo = 0, colorNode = 0 , minColor, cPos = 0 , tComp, result;
    unsigned int len = 0, ticks, valj, vali , calc;
    unsigned int connectedArray[N] = {};
    bigVector vSnareChoicet[snareLength] , vSnareChoicef[snareLength] , vt , vf;
    bigVector b1;
    _Bool Ck=0, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5; 

    bitvector Vnodes[N];
    bitvector Tnodes[N] ;

    bitvector  fareTotal, inTotal, outTotal , outVSnareTotal , inVSnareTotal , outTSnareTotal , inTSnareTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, t, f, v2, lastv, lastv2 ,nv, nv2, v0, v02 ;
    snareVector Tedge[N][N], Vedge[N][N] , Vedge2[N][N] , Tedge2[N][N] , fComp , bComp;
    
    //  FriendMatrix is v * t-snare matrix where v snares are rows and T snares are columns
    snareVector friendMatrix[snareLength];     
    //  OnOffMatrix is the N * t-snare matrix where N:nodes are rows and T snares are column  
    snareVector onOffMatrix[N], stCorres , ew;
  
    // Input the graph *******************************************
    unsigned int graph[N][N];
    
    //  Calculate the total required length that is required for our container
    //  Pre calculating the length ( total edges ) .
    for (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
            if(graph[i][j] == 1) {
		         len = len + 1;
             }
            else if(graph[i][j] == 2) {
                len =  len + 2;
             }
         } 
    }
    printf(" lenght is %d " , len);
    __CPROVER_assume(len >= (3 * N ));

    printf("After Cprover lenght is %d " , len);
    
   assert(0);
  return 0; 
}



