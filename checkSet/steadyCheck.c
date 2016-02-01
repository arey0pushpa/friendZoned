#include <stdio.h>
#include <stdlib.h>

//  THIS CODE IS FOR THE N = 3 --------------------------------

#define M 6	       
#define N 3
#define snareLength 6

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[snareLength] snareVector; 

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
    unsigned int edgePos, bagNo = 0, colorNode = 0 , minColor, cPos = 0 , tComp;
    unsigned int len = 0, ticks, valj, vali , vSnareChoicet[snareLength] , vSnareChoicef[snareLength];
    _Bool Ck=0, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5; 

    bitvector Vnodes[N];
    bitvector Tnodes[N] ;

    bitvector  fareTotal, inTotal, outTotal , outVSnareTotal , inVSnareTotal , outTSnareTotal , inTSnareTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, t, f, v2, lastv, lastv2 ,nv, nv2, v0, v02 ;
    snareVector Tedge[N][N], Vedge[N][N] , Vedge2[N][N] , Tedge2[N][N], vt ,vf ;
    
    //  FriendMatrix is v * t-snare matrix where v snares are rows and T snares are columns
    snareVector friendMatrix[snareLength];     
    //  OnOffMatrix is the N * t-snare matrix where N:nodes are rows and T snares are column  
    snareVector onOffMatrix[N], stCorres , ew;
  
    // Input the graph *******************************************
    unsigned int graph[N][N] =  { {1, 1, 1},
								{1, 1, 1}, 
								{1, 1, 1}
                          };
  

    //  Calculate the total required length that is required for our container
    for (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
            if(graph[i][j] == 1) {
		        len = len + 1;
            }
          } 
    }

    //  Define the Container as Basis of our work  --------------------------
     struct EdgeBag edgeBag[len];
     
    //  Fill the Container values with i, j, edgeWeigth, vsnare, tsnare Values.
    edgePos = 0;
    for(i=0; i<N; i++) {
		for(j=0; j<N; j++) {
            if ((graph[i][j] == 1)) {
                  edgeBag[edgePos].ith = i;
                  edgeBag[edgePos].jth = j;
                  __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                  __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0); ;
                  Vedge[i][j] = edgeBag[edgePos].vSnare;
                  Tedge[i][j] = edgeBag[edgePos].tSnare;
                  edgePos = edgePos + 1;
            }
 
         }
    }

    //  Edgeweight is not allowed to be zero : build C0 to represent that :
    C0 = 1; 
    for (j = 0; j < len; j++) {
         C0 = (C0 && (edgeBag[j].vSnare != 0));
     }
    
     
    C1 = 1;
// ====================== BLOCK 1 ==================================================================	
    i = 0;    // For each Edge == Len 
    for (j = 0; i < len ; j++) {       // for each molecule Plz check the code         
          if (j < M) {
            unsigned int big;

            if(edgeBag[i].vSnare & (1 << j)) {     // Present molecules   
                vali = edgeBag[i].ith;
                valj = edgeBag[i].jth;
                __CPROVER_assume( big >= 1 && big <= (N - 1));

                unsigned int path[big];
                for (l = 0; l < big; l++) {           // this is DYNAMIC TOO
                      path[l] = zeroTon(N-1);
                } 

                for (k = 0; k < big; k++)           // THIS IS DYNAMIC   // Molecule come back in cycle s 
                {
				 printf("cbmc");
				   // Logic 
		        }
	        }
        }
          else {
               j = -1;             // reset j to 0 incase  where j = 20
               i = i + 1;   
          }                       
      }
   
//==========================================BLOCK 1 ENDS ===============================     
  
// =======================================BLOCK 2 =======================================  
     i = 0;    // For each Edge == Len 
        for (j = 0; i < len ; j++) {       // for each molecule Plz check the code
          if (j < M) {                
            if(edgeBag[i].tSnare & (1 << j)) {   // All those molecules that are present
                
                unsigned int big2;

                vali = edgeBag[i].ith;
                valj = edgeBag[i].jth;
                __CPROVER_assume( 1 <= big2 && big2 <= (N - 1));

                unsigned int path1[big2];
                for (l = 0; l < big2; l++) {                    // THIS IS DYNAMIC
                      path1[l] = zeroTon(N-1);
                }
                
                for (k = 0; k < big2; k++)           // THIS IS DYNAMIC 
                {
					printf("cbmc");
				 // Logic
                }
             }
           }
          else {
             j = -1;
             i = i + 1;          
          }
    }
// =================================BLOCK 2 ENDS=============================================
    
  __CPROVER_assert(!(C0 && C1), "Graph with steady state exists");  
  return 1; 
}



