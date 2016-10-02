#include <stdio.h>
#include <stdlib.h>

#define M 4       
#define N 2
#define snareLength 4
#define bigLen  16   // 2 ^ M
#define len 3

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

//bigVector biig = 0b1;

bigVector nondetBV() {
     bigVector bee;
  //   __CPROVER_assume(bee >= 0b0 && bee <= 0b1111);  
     return bee;
}

//  Define the Structure of the Container `
struct EdgeBag
 {
   int ith;
   int jth;
   unsigned int count;
   snareVector  vSnare;
   snareVector tSnare;
   unsigned int zebra[snareLength];
   snareVector combinedMask; 
};



int main (int argc, char** argv)

{    

    unsigned  int j; 
    unsigned int pos, i, k, l, w, x, y , iVal, jVal , g, g0,gl, lastg, ng,nl,nl2 ;
    unsigned int edgePos, bagNo = 0, colorNode = 0 , minColor, cPos = 0 , tComp;
    unsigned int  ticks, valj, vali , calc;
    unsigned int  edgeCount;
    bigVector vSnareChoicet[snareLength] , vSnareChoicef[snareLength], result, vt, vf, vl, vl2;
    bigVector b0 = 0b0, b1 = 0b1 ;
    _Bool Ck=0, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5; 

    bitvector Vnodes[N];
    bitvector Tnodes[N] ;

    bitvector  fareTotal, inTotal, outTotal , outVSnareTotal , inVSnareTotal , outTSnareTotal , inTSnareTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, t, f, lastv, lastv2 ,nv, nv2, v0,v2 ;
    snareVector Tedge[N][N], Vedge[N][N] , Vedge2[N][N] , Tedge2[N][N] , fComp , bComp;
      
    //  OnOffMatrix is the N * t-snare matrix where N:nodes are rows and T snares are column  
    snareVector onOffMatrix[N], stCorres , ew;
  
    // Input the graph , Future plans are to make it arbitary 
    unsigned int graph[N][N];
    
    //  Pre-calculate the total required length(#edges) for the containerBag
	edgeCount = 0;
    for (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
			if(i != j) {
				__CPROVER_assume(graph[i][j] >= 0 && graph[i][j] <=2);
			    if (graph[i][j] == 1)
                    edgeCount += 1;	
                else if (graph[i][j] == 2) 
					edgeCount += 2;
            }
             else
				__CPROVER_assume(graph[i][j] == 0); 

			} 
    }

     __CPROVER_assume(edgeCount == len);

    // C5 makes sure that its Graph is Strongly connected
    C5 = 1;

    for ( i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
            if ( graph[i][j] >= 1 && (i != j)) {  // if there is Direct edge we are done
                C5 = C5 && 1;
             }
            else if (i != j) {  // Else case
                unsigned int nub;  // Define max hop
                __CPROVER_assume( nub >= 1 && (nub <= N-2));
                unsigned int gPath[nub];

                for (k = 0; k < nub; k++) {   // zdynamic N - 2 iteration
                     gPath[k] = zeroTon(N-1);
                 }
                 
                //  Make sure first edge is connected to i  and last edge is connected to j
                if( (graph[i][gPath[0]] >= 1) && (graph[gPath[nub - 1]][j] >= 1))   
                     C5 = C5 && 1;
                else 
                     C5 = 0;
            
             if (nub > 1) {
               // rest Of the case is just checking edge btw consecutive array elements
                 for (l = 0; l < nub - 1; l++) {         //Dynamic N - 3  iteration
                       if ( graph[gPath[l]][gPath[l+1]] >= 1 ) 
                             C5 = C5 && 1;
                        else 
                             C5 = 0;
                     }
                }
            }
        }
    }

    struct EdgeBag edgeBag[len]; 
    
    //  Fill the Container values with i, j, edgeWeigth, vsnare, tsnare Values.
    edgePos = 0;
    for  (i = 0; i < N; i++) {
	    for  (j = 0; j < N; j++) {
              if ((graph[i][j] == 1) || (graph[i][j] == 2)) { 
                  edgeBag[edgePos].ith = i;     // Record the source node
                  edgeBag[edgePos].jth = j;     // Record the target Node
                 
                  // Only molecule present at the nodes are allowed to fly out.
                  __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                  __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0); ;
                  
                  // Additional Vedge[i][j] and Tedge[i][j] is used to be lookup value in global steady state check condition.
                  Vedge[i][j] = edgeBag[edgePos].vSnare;
                  Tedge[i][j] = edgeBag[edgePos].tSnare;
                  edgePos = edgePos + 1;
            }

            if ((graph[i][j] == 2)) {      
                 edgeBag[edgePos].ith = i;      // Record the Source Node  
                 edgeBag[edgePos].jth = j;      // Record the Target Node
                  
                // Only molecule present at the nodes are allowed to fly out.
                  __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                  __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0);
                  
                  // Additional Vedge2[i][j] and Tedge2[i][j] is used to be lookup value in global steady state check condition.
                  Vedge2[i][j] = edgeBag[edgePos].vSnare;
                  Tedge2[i][j] = edgeBag[edgePos].tSnare;
                  edgePos = edgePos + 1;
            }
 
         }
    }
 
/* Graph has to be Strongly Connected +  3-Connected but not 2-Strongly connected
 Not adding this constrint as Input graph will be satisfying this Constraint*/
// FIRST CONSTARAINT ON THE GRAPH 
// The code for make sure that it'll be 3 connected and not four connected
 
        C4 = 0;
        for ( i = 0; i < N ; i++) {
            calc = 0;
            for ( j = 0 ; j < len; j++) {              // 20 UNWINDINGS
                if ( (edgeBag[j].ith == i) || (edgeBag[j].jth == i) ){
                    calc = calc +  1;
                }
               }
            __CPROVER_assume(calc >= 3);
            if(calc < 4) {
                C4 = 1;
            }
        } 

    //  Edgeweight is not allowed to be zero : build C0 to represent that :
    C0 = 1; 
    for (j = 0; j < len; j++) {   
         C0 = (C0 && (edgeBag[j].vSnare != 0));
     }
     
      for  (i = 0; i < N; i++) {
		   __CPROVER_assume(Vnodes[i] != 0);
	   }

 C1 = 1;
   for (i = 0; i < len; i++ ) {      // For each Edge  
       for (j = 0; j < snareLength; j++) {       // for each molecule               
           if(edgeBag[i].vSnare & (1 << j)) {     // Present molecules   
                vali = edgeBag[i].ith;   // store the source node
                valj = edgeBag[i].jth;   // Store the target node
                // If there is a back edge from taget to source we are done.
                if (((graph[valj][vali] == 1) && (Vedge[valj][vali] & (1 << j) ))  || ((graph[valj][vali] == 2) && ((Vedge2[valj][vali] & (1 << j)) || (Vedge[valj][vali] & (1 << j) )) ) ) {
                      C1 = C1 && 1;
                }
                // Else continue checking for the cycle
                else { 
         		// g0 is unsigned int checks if there is an edge btw two nodes
                //  It should be on some cycle, So assume that it'll be between 0 and N-2
                //  As we are Only considering elementary cycles.
                unsigned int big;
                __CPROVER_assume( big >= 1 && big <= (N - 2));
                 unsigned int path[big];   // An array to store the path taken by molecule.
             
               //  Make sure every int is between 0 and N-1 that represent the node
                for (l = 0; l < big; l++) {           // Dynamic
                      path[l] = zeroTon(N - 1);
                } 
               
	           g0  = graph[valj][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	           v0  = Vedge[valj][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
               v2  = Vedge2[valj][path[0]];
               
                   gl  = graph[path[big - 1]][vali];
	           vl  = Vedge[path[big - 1]][vali];    // snareVector gets the edgeweight of the corresponding edge.
                   vl2 = Vedge2[path[big - 1]][vali];

               if ( ((( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v2 & (1 << j)) ) )) &&  ((( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) )))  {                  
                   C1 = C1 && 1;
               }

               else {
                   C1 = 0;
               }
           
           
           if ( big > 1 ) {
               for (k = 0; k < big - 1 ; k++)  {                  // Dynamic 				    	 
		           ng  = graph[path[k]][path[k+1]];
		           nv  = Vedge[path[k]][path[k+1]];
		           nv2 = Vedge2[path[k]][path[k+1]];	
                   if (((ng == 1) && (nv & (1 << j))) ||  ( (ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j)))) ) {
                           C1 = C1 && 1;
                   }
                   else {
                           C1 = 0;
                   }
               }
           }


           }  // else Outside closed
        } 
      }  // jth for closed    
    }   //  ith for closed 
  
  
  
 for (i = 0; i < len; i++ ) {      // For each Edge  
       for (j = 0; j < snareLength; j++) {       // for each molecule               
           if(edgeBag[i].tSnare & (1 << j)) {     // Present molecules   
                vali = edgeBag[i].ith;   // store the source node
                valj = edgeBag[i].jth;   // Store the target node
                
                if (((graph[valj][vali] == 1) && (Tedge[valj][vali] & (1 << j) ))  || ((graph[valj][vali] == 2) && (Tedge2[valj][vali] & (1 << j)) || (Tedge[valj][vali] & (1 << j)) ) ) {
                      C1 = C1 && 1;
                 }

                else { 
                unsigned int big;
                __CPROVER_assume( big >= 1 && big <= (N - 2));
     
                 unsigned int path[big];   // An array to store the path taken by molecule.
             
               //  Make sure every int is between 0 and N-1 that represent the node1
                for (l = 0; l < big; l++) {           // Dynamic
                      path[l] = zeroTon(N - 1);
                } 
               
	           g0  = graph[valj][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	           v0  = Tedge[valj][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
               v2  = Tedge2[valj][path[0]];
               
               gl  = graph[path[big - 1]][vali];
	           vl  = Tedge[path[big - 1]][vali];    // snareVector gets the edgeweight of the corresponding edge.
               vl2 = Tedge2[path[big - 1]][vali];

               if ( ((( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v2 & (1 << j)) ) )) &&  ((( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) )))  {                  
                   C1 = C1 && 1;
               }

               else {
                   C1 = 0;
               }
          if ( big > 1) {
               for (k = 0; k < big - 1 ; k++)  {                  // Dynamic 				    	 
		           ng  = graph[path[k]][path[k+1]];
		           nv  = Tedge[path[k]][path[k+1]];
		           nv2 = Tedge2[path[k]][path[k+1]];	
                   if (((ng == 1) && (nv & (1 << j))) ||  ( (ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j))) )) {
                           C1 = C1 && 1;
                   }
                   else {
                           C1 = 0;
                   }
               }
          }
           }  // else Outside closed
        } 
      }  // jth for closed    
    }   //  ith for closed 
  

    for  (i = 0; i < snareLength ; i++ ) {
         vSnareChoicet[i] = nondetBV();
    }

    for (j = 0; j < snareLength; j++) {
        vSnareChoicef[j] = nondetBV();
    }
    
    
   
    C2 = 1;
    C3 = 1;
    for (i = 0; i < len; i++) {  
		ticks = 0;
		Ck = 0;
        for  (j = 0; j < snareLength; j++) {    
               v = edgeBag[i].vSnare;
               t = edgeBag[i].tSnare;
               valj = edgeBag[i].jth;
               vali = edgeBag[i].ith;
          
           if  (v & (1 << j))  {                    
              vt = vSnareChoicet[j];    
              result = (vt & (1 << t));   
              if (result == 0) {   
                  edgeBag[i].zebra[ticks] = j;  
                  ticks  =  ticks + 1;
	          fComp  =  (Tnodes[valj] & onOffMatrix[valj]);   
                  bComp  =  (Tnodes[vali] & onOffMatrix[vali]);    		  
                  vf  =  vSnareChoicef[j];    
                  if (  (vf  & (1 << fComp ))  && ( (vf & (1 << bComp)) == 0 ))  {
                         Ck = 1 ;                                  
                  }
              }
           }
	     }
	     
         edgeBag[i].count = ticks;
         
         if(Ck == 1) {
             C2 = C2 && 1;
         }
         else {
             C2 = C2 && 0;
         }
           
         for (k = 0;k < N; k++){
              if (k != edgeBag[i].jth){	                    
 			      bComp =  Tnodes[k] & onOffMatrix[k] ;   	  			       
			      for (l = 0; l < edgeBag[i].count; l++) {           // THIS IS DYNAMIC CODE    
			           vf = vSnareChoicef[edgeBag[i].zebra[l]];  
			           if ( (vf & (1 << bComp)) == 0) {
                             C3 = C3 && 1;
                       }
                       else {
                             C3 = C3 && 0;
                       }
                  }
            }
         }
    }
    
    for  (i = 0; i < N; i++){
        printf("\n VNodes[%d] = %d" , i , Vnodes[i]);
        printf(" TNodes[%d] = %d" , i , Tnodes[i]);
        
    }
  
  for  (i = 0; i < len; i++) {

        printf("The edge No.%d has this config : \n There is an edge between graph[%d][%d]", i, edgeBag[i].ith, edgeBag[i].jth);
        printf(" SourceNodes[%d] (v : t) = (%d , %d)" , edgeBag[i].ith , Vnodes[edgeBag[i].ith] , Tnodes[edgeBag[i].ith]);
        printf(" TargetNodes[%d] (v : t) = (%d , %d) " , edgeBag[i].jth ,Vnodes[edgeBag[i].jth] , Tnodes[edgeBag[i].jth]);
        printf (" vSnare =  %d \n tSnare = %d ", edgeBag[i].vSnare, edgeBag[i].tSnare);
        printf (" combinedMask = %d \n counts = %d \n" ,edgeBag[i].combinedMask, edgeBag[i].count);
   
   }
   
    for  (i = 0; i < snareLength ; i++ ) {
        printf(" vSnareChoicet[%d] = %d" , i, vSnareChoicet[i]);
    }

    for (j = 0; j < snareLength; j++) {
               printf(" vSnareChoicef[%d] = %d" , j, vSnareChoicef[j]);
    }
    for (i = 0; i < N; i++){
        printf(" The onOffMatrix[%d] = %d ", i, onOffMatrix[i]);
    }

    for(i = 0;i < N; i++) {
        for(j = 0;j < N; j++) {
           printf("Graph[%d][%d] = %d",i,j,graph[i][j]);
        }
     }
    
    printf("\nThe value of : \n C0 = %d \n C1 : %d \n C2 : %d , C3 : %d C4 : %d , C5 = %d \n",C0,C1,C2,C3, C4,C5);
    printf(" the value of mr.Ticks is %d and len was %d ", ticks , len);    
 
 // assert(0);
  __CPROVER_assert(!(C0 && C1 && C5 && C2 && C3 && C4) , "Graph that satisfy friendZoned model exists");   
  return 0; 
}



