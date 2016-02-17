/* Complete Spec implementation of the V Snare - T Snare MOdel
   Github Link
*/


#include <stdio.h>
#include <stdlib.h>


#define M  20          
#define MAX 1023      
#define N 10         
#define snareLength 10

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[20] bitvector; 
typedef unsigned __CPROVER_bitvector[10] snareVector; 

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
   bitvector edgeWeight;
   snareVector  vSnare;
   snareVector tSnare;
   snareVector zebraMask[snareLength];
   snareVector combinedMask; 
};


//  Setweight function allow only subset to out!
    bitvector setWeight( bitvector node) {
         bitvector edge;
         edge = 0b0;
         for(unsigned int k=0; k<M; k++){
             if ((node & (0b1 << k)) == (0b1 << k)) {
                    edge =  (edge |  (nondet() << k));
               } 
         }
         return edge;
    }
	

void main()
 {    
    unsigned int pos , i, j, k, l, v, w, x, y , iVal, jVal;
    unsigned int edgePos, bagNo = 0, colorNode = 0 , minColor, cPos = 0;
    unsigned int len = 0, ticks, valj, vali ;
    _Bool Ck, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5; 
	
    bitvector compartment1 , compartment2, compartment3 , compartment4 , compartment5 ;
    bitvector compartment6 , compartment7 , compartment8 ,compartment9 , compartment10;
    
    bitvector nodes[N] = {compartment1, compartment2, compartment3, compartment4, compartment5, compartment6, compartment7,  compartment8, compartment9, compartment10};
  
    bitvector  fareTotal, inTotal, outTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, t, f;
    
    //  FriendMatrix is v * t-snare matrix where v snares are rows and T snares are columns
    snareVector friendMatrix[snareLength];     
    //  OnOffMatrix is the N * t-snare matrix where N:nodes are rows and T snares are column  
    snareVector onOffMatrix[N], stCorres;
  
    // Input the graph *******************************************
    unsigned int graph[N][N] =  { {0,  0,  0,  0,  0,  0,  2,  0,  0,  0},
                                  {0,  0,  0,  1,  0,  0,  0,  0,  2,  1},
                                  {1,  2,  0,  0,  1,  0,  0,  0,  0,  0},
                                  {0,  0,  0,  0,  0,  1,  0,  0,  0,  2},
                                  {0,  0,  0,  0,  0,  0,  0,  0,  0,  0},
                                  {0,  0,  1,  1,  1,  0,  1,  1,  0,  0},
                                  {1,  0,  0,  0,  0,  1,  0,  0,  1,  0},
                                  {0,  0,  0,  3,  1,  0,  0,  0,  0,  0},
                                  {1,  1,  0,  0,  1,  0,  0,  1,  0,  0},
                                  {0,  0,  1,  0,  0,  0,  0,  0,  1,  0}};
  

    //  Calculate the total required length that is required for our container
    for (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
            if(graph[i][j] == 1) {
		        len = len + 1;
            }
            else if(graph[i][j] == 2) {
                  len =  len + 2;
            }
            else if (graph[i][j] == 3){
                  len =  len + 3;
            }

          } 
    }

    //  Define the Container as Basis of our work  --------------------------
     struct EdgeBag edgeBag[len];
     
    //  Fill the Container values with i, j, edgeWeigth, vsnare, tsnare Values.
    edgePos = 0;
    for(i=0; i<N; i++) {
		for(j=0; j<N; j++) {
            if ((graph[i][j] == 1) || (graph[i][j] == 2) || (graph[i][j] == 3)) {
                  edgeBag[edgePos].ith = i;
                  edgeBag[edgePos].jth = j;
                  edgeBag[edgePos].edgeWeight  = setWeight(nodes[i]);
                  edgeBag[edgePos].vSnare  = ((edgeBag[edgePos].edgeWeight) >> snareLength) & ((1 << snareLength) - 1)  ;
                  edgeBag[edgePos].tSnare  = ((edgeBag[edgePos].edgeWeight) & (( 1 << snareLength) -1)) ;
                  edgePos = edgePos + 1;
            }

            if ((graph[i][j] == 2) ||  (graph[i][j] == 3)) {
                  edgeBag[edgePos].ith = i;
                  edgeBag[edgePos].jth = j;
                  edgeBag[edgePos].edgeWeight = setWeight(nodes[i]);
                  edgeBag[edgePos].vSnare  = ((edgeBag[edgePos].edgeWeight) >> snareLength) & ((1 << snareLength) - 1)  ;
                  edgeBag[edgePos].tSnare  = ((edgeBag[edgePos].edgeWeight) & (( 1 << snareLength) -1)) ;
                  edgePos = edgePos + 1;
            }
            if ((graph[i][j] == 3)) {
                  edgeBag[edgePos].ith = i;
                  edgeBag[edgePos].jth = j;
                  edgeBag[edgePos].edgeWeight = setWeight(nodes[i]);
                  edgeBag[edgePos].vSnare  = ((edgeBag[edgePos].edgeWeight) >> snareLength) & ((1 << snareLength) - 1)  ;
                  edgeBag[edgePos].tSnare  = ((edgeBag[edgePos].edgeWeight) & (( 1 << snareLength) -1)) ;
                  edgePos = edgePos + 1;
            }
         }
    }

    //  Edgeweight is not allowed to be zero : build C0 to represent that :
    C0 = 1; 
    for (j = 0; j < len; j++) {
         C0 = C0 && (edgeBag[j].edgeWeight != 0);
     }
    
     // Assume No two edgeweight are same in the array edgeBag[len] :
     for  (i = 0; i < len; i++) {
        for  (j = 0; (j != i) && (j < len) ; j++) {
           __CPROVER_assume(edgeBag[i].edgeWeight != edgeBag[j].edgeWeight);
        }
    
     }
     
//  STEADY STATE CONDITION BEGINS --------------------------------------- 
    //  The inflow of type of molecule is same as outflow of type of the molecule.
    //  Different type of molecules coming in is same as differnt type of molecules going out.
    C1 = 1;
     for(i=0; i<N; i++) {
         iVal = i;
         outTotal = 0b0;
         inTotal  = 0b0;

         for(j = 0; j < len; j++) {
                 if (edgeBag[j].ith == iVal) {
                             outTotal = (outTotal | edgeBag[j].edgeWeight);
                 }

                 if (edgeBag[j].jth  == iVal) {
                             inTotal = (inTotal | edgeBag[j].edgeWeight);
                 }
         }

         C1 = C1 && (inTotal == outTotal);
        
     }

//  STEADY STATE CONDITION ENDS -----------------------------------------


     //  Define FRIEND Matrix : 
     for  (i = 0; i < snareLength; i++) {
         friendMatrix[i] = zeroTon(MAX); 
     }
  
/* =================== ISSUE  + COMMENT ========================================
    Looks Like we do-not require C4 and C5 as  they should come 
    in assigments as non-zero Recheck without contraining with these

 ** Both FRIEND AND ONOFF MATRIX ARE REPRESNTING REVERSE T SNARES PRESENTATION
    Index of t sanres in table is starting from t[snarelength] and goes to t[0] 
================================================================================*/

    //  C4 : Boolean Condition : Each Row of FriendMatrix is Non-zero : 
     for  (j = 0; j < snareLength; j++) {
         if (friendMatrix[j] & (( 1 << snareLength) -1)) {
             C4 = C4 && 1;
         }
         else {
             C4 = C4 && 0;
         }
     }


   //  C5 : Bool , Each Row of OnOffMatrix is Non-zero :
    for  (j = 0; j < N; j++) {
         if (onOffMatrix[j] & (( 1 << snareLength) -1))  {
             C5 = C5 && 1;
         }
         else {
             C5 = C5 && 0;
         }
   
     }

    //  Make sure two row entries are not same in Friend matrix and OnOffMatrix :
    for  (i = 0; i < snareLength; i++) {
        for  (j = 0; (j < snareLength) && (j != i); j++) {
          
            __CPROVER_assume( friendMatrix[i] != friendMatrix[j]);
      
        }
     }
 
    for  (i = 0; i < N; i++) {
        for  (j = 0; (j < N) && (j != i); j++) {
          
            __CPROVER_assume( onOffMatrix[i] != onOffMatrix[j]);
        }
     }

    
// THE BASIC CONSTRAINTS BEGINS --------------------------------------------------------------------- 
 /*=================================================================
  * Steps :
  
  * 1. Check if the ith Vsnare is present on current Edge ?
  *
  * 2. Check if its corresponding frd t-snares (t required for fusion), 
  *    based on FriendMatrix are all absent on the current edge.
  * 
  * 3. Then check if the t-snare required for fusion are all present on 
  *    target edge and all are in On Conditions based on OnOffMatrix.
  *
  * 4. Check if t snares required for fusion are not all present on the 
  *    source node of the current edge or they are off.
  *    
  *    **** I'm implimenting it as just checking OnOffMatrix and make 
  *    ***  sure all are not onn to avoid the case that it might be 
  *    **   on even if its not present.

  =====================================================================*/
    
    for  (i = 0; i < len; i++) {
        centTotal = 0b0;
        total = 0b0;
        ticks = 0;
        
        //  Check if jth vSnare is present then check if all its t-snare frds are present on the edge. 
        //  If yes don't consider him as a cnadidate to check the fusion that happens btw current nodes.

        for  (j = 0; j < snareLength; j++) {
           v = edgeBag[i].vSnare;
           t = edgeBag[i].tSnare;
           f = friendMatrix[j];
           valj = edgeBag[i].jth;
           vali = edgeBag[i].ith;
          
           if( (v & (1 << j)) && ((t & f) != f) ){
              edgeBag[i].zebraMask[ticks] = f;  
              centTotal = centTotal | f;
              ticks = ticks + 1;     
              if ( ((nodes[valj]  & f)  == f)  && ((onOffMatrix[valj] & f) == f ) && 
                      ((onOffMatrix[vali] & f) != f)) {
                 Ck = Ck || 1 ;                                  
              }
           }
         }
           
         edgeBag[i].combinedMask = centTotal;
         edgeBag[i].count = ticks;

         if(Ck == 1) {
             C2 = C2 && 1;
         }
         else {
             C2 = C2 && 0;
         }

        //  Make Sure that each contributing vsnares frds are either absent or Are off on all other nodes except current traget node.
        for  (j = 0; j < ticks; j++){
                cond2Total = edgeBag[i].zebraMask[j];
    
             // The combined mask pattern is absent in the all other nodes or 
             // the onOffMatrix cause all the tsnares that are pattern to be absent.
              for (k=0; (k<N) && (k!= edgeBag[i].jth); k++){
                 if(( (cond2Total & nodes[k]) == 0) || ((onOffMatrix[k] & cond2Total) == 0 )){
                       Cf = Cf && 1;
                  }
                 else {
                       Cf = Cf && 0;
                  }
              }
         }

        if(Cf == 1){
              C3 = C3 && 1;
        }
        else if (Cf == 0){
            C3 = C3 && 0;
        }

    }

    
//  BASIC BLOCK ENDS -----------------------------------------------------------------------------------------

   for  (i = 0; i < len; i++) {

        printf("The edge No.%d has this config : \n There is an edge between graph[%d][%d]" , i , edgeBag[i].ith, edgeBag[i].jth);

        printf (" edgeweight is = %d \n vSnare =  %d \n tSnare = %d\n combinedMask = %d \n counts = %d " ,edgeBag[i].edgeWeight , edgeBag[i].vSnare , edgeBag[i].tSnare, edgeBag[i].combinedMask, edgeBag[i].count);
   
   }

    for  (i = 0; i < N; i++){
        printf(" Nodes[%d] = %d" , i , nodes[i]);
    }

    for  (i = 0; i < snareLength; i++) {
        printf( "\n The frindmatrix[%d] = %d ", i , friendMatrix[i]);
    }

    for  (i = 0; i < N; i++){
        printf(" \n The onOffMatrix[%d] = %d ", i, onOffMatrix[i]);
    }

    printf("\nThe value of : \n C0 = %d \n C1 : %d \n C2 : %d , C3 : %d \n",C0,C1,C2,C3);
    printf(" the value of mr.Ticks is %d and len was %d ", ticks , len);
    
   //assert(0);
  __CPROVER_assert(!( C0 && C1 && C2 && C3 && C4  && C5 ) , "Graph that satisfy friendZoned model exists");  
 
}

