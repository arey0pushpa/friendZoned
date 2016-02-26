#include <stdio.h>
#include <stdlib.h>

#define M 10	       
#define N 5
#define snareLength 10
#define len 10
//#define bigLen  1024

_Bool nondet_bool();
unsigned int nondet_uint();

typedef unsigned __CPROVER_bitvector[M] bitvector; 
typedef unsigned __CPROVER_bitvector[snareLength] snareVector; 
//typedef unsigned __CPROVER_bitvector[bigLen] bigVector;
 
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


//  Define the Structure of the Container `
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


int main ()

{    

    unsigned int pos, i,j, k, l, w, x, y , iVal, jVal , g, g0,gl, lastg, ng ;
    unsigned int edgePos,edgeCount = 0, bagNo = 0, colorNode = 0 , minColor, cPos = 0 , tComp, result;
    unsigned int ticks, valj, vali , calc;
    _Bool Ck=0, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5; 

    bitvector Vnodes[N];
    bitvector Tnodes[N] ;

    bitvector  fareTotal, inTotal, outTotal , outVSnareTotal , inVSnareTotal , outTSnareTotal , inTSnareTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, t, f, v2, lastv, lastv2 ,nv, nv2, v0, v02,vl,vl2 ;
    snareVector Tedge[N][N], Vedge[N][N] , Vedge2[N][N] , Tedge2[N][N] , fComp , bComp;
    
    //  FriendMatrix is v * t-snare matrix where v snares are rows and T snares are columns
    snareVector friendMatrix[snareLength];     
    //  OnOffMatrix is the N * t-snare matrix where N:nodes are rows and T snares are column  
    snareVector onOffMatrix[N], stCorres , ew;
  
       // Input the graph *******************************************
    unsigned int graph[N][N];
                                
     for ( i = 0;i < N; i++) {
          for (j = 0; j < N; j++) {
            if (graph[i][j] == 1) {
                edgeCount += 1;
            }
            else if(graph[i][j] == 2) {
                edgeCount += 2;
            }
          }
      }
      __CPROVER_assume(edgeCount == len);

    // __CPROVER_assume(len >= (2 * N));


/*
// C5 makes sure that its Graph is Strongly connected
    C5 = 1;

    for ( i = 0; i < N; i++) {
        for (j = 0; (j < N) ; j++) {
            if ( graph[i][j] >= 1 && (i != j)) {  // if there is Direct edge we are done
                C5 = C5 && 1;
             }
            else if (i != j) {  // Else case
                unsigned int nub;  // Define max hop // Total nodes comes btw
                unsigned int gPath[nub];
                __CPROVER_assume( nub >= 1 && (nub <= N-2));
                
                for (k = 0; k < nub; k++) {            // Dynamic
                     gPath[k] = zeroTon(N-1);
                 }
                 
                //  Make sure first edge is connected to i  and last edge is connected to j
                if(graph[i][gPath[0]] >= 1 && (graph[gPath[nub - 1]][j] >= 1))   
                     C5 = C5 && 1;
                else 
                     C5 = 0;

               // rest Of the case is just checking edge btw consecutive array elements
               // You never checked btw 0 -1 and hence its 0 to n-3 . n-3 and n-2 will be checked in last loop. 
             if ( nub > 1) {
                for (l = 0; l < nub - 1; l++) {   // Dynamic
                    // Why nub - 2?? cause two nodes already gone and as we checking btw l and l+1 one less will require
                       if ( graph[gPath[l]][gPath[l+1]] >= 1 ) 
                               C5 = C5 && 1;
                        else 
                            C5 = 0;
                     }

            }
          }
        }
    }

*/
    //  Define the Container Which will record info about each edge
    //  Declare a Structure array of length =  len (#edges)
    struct EdgeBag edgeBag[len];
     
    /*============================================================
     * Statement :
     * For all edges Record the source and target nodes and 
     *  Assign EdgeWeights to edges in form of VSnares , tSnares
     *  Array.
     *
     * Qbf ::
     * For_All i , j ==> Rcord (i,j,Vnodes[i],Tnodes[i]))
     ===============================================================*/
     
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
    //  Edgeweight is not allowed to be zero : build C0 to represent that :
/*

 // The code for make sure that it'll be 3 connected and not four connected
        C4 = 0;
        for ( i = 0; i < N ; i++) {
            calc = 0;
            for ( j = 0 ; j < len; j++) {              // 20 UNWINDINGS DYNAMIC
                if ( (edgeBag[j].ith == i) || (edgeBag[j].jth == i) ){
                    calc += 1;
                }
               }
            __CPROVER_assume(calc >= 3);
            if(calc < 4) {
                C4 = 1;
            }
        }
   */ 
    C0 = 1; 
    for (j = 0; j < len; j++) {   
         C0 = (C0 && (edgeBag[j].vSnare != 0));
     }
   //  Make assumption that each TNodes will be differnt.    
    for  (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
            if ( i != j) {
              __CPROVER_assume(Tnodes[i] != Tnodes[j]);
              __CPROVER_assume(Vnodes[i] != Vnodes[j]);
           }
        } 
    }
     
  
 C1 = 1;

// No.1 : Steady State C ndition For VSnares	
     	
   for (i = 0; i < len; i++ ) {      // For each Edge  
       for (j = 0; j < snareLength; j++) {       // for each molecule               
           unsigned int big;
           if(edgeBag[i].vSnare & (1 << j)) {     // Present molecules   
                vali = edgeBag[i].ith;   // store the source node
                valj = edgeBag[i].jth;   // Store the target node
                // If there is a back edge from taget to source we are done.
                if ((graph[valj][vali] >= 1) && (Vedge[valj][vali] & ( 1 << j) )) {
                      C1 = C1 && 1;
                }
                // Else continue checking for the cycle
                else { 
         		// g0 is unsigned int checks if there is an edge btw two nodes
                //  It should be on some cycle, So assume that it'll be between 0 and N-2
                //  As we are Only considering elementary cycles.
                __CPROVER_assume( big >= 1 && big <= (N - 2));
     
                 unsigned int path[big];   // An array to store the path taken by molecule.
             
               //  Make sure every int is between 0 and N-1 that represent the node
                for (l = 0; l < big; l++) {           // Dynamic
                      path[l] = zeroTon(N - 1);
                } 
               
	           g0  = graph[valj][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	           v0  = Vedge[valj][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
                   v2  = Vedge[valj][path[0]];
               
                   gl  = graph[path[big - 1]][vali];
	           vl  = Vedge[path[big - 1]][vali];    // snareVector gets the edgeweight of the corresponding edge.
                   vl2 = Vedge[path[big - 1]][vali];

               if ( ( (( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v2 & (1 << j)))))  &&  ((( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) )))  {                  
                   C1 = C1 && 1;
               }

               else {
                   C1 = 0;
               }

             if( big > 1){  
               for (k = 0; k < big - 1 ; k++)  {                  // Dynamic 				    	 
		           ng  = graph[path[k]][path[k+1]];
		           nv  = Vedge[path[k]][path[k+1]];
		           nv2 = Vedge2[path[k]][path[k+1]];	
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
  
  
  
// No.2 : Steady State Condition For VSnares	
   for (i = 0; i < len; i++ ) {      // For each Edge  
       for (j = 0; j < snareLength; j++) {       // for each molecule               
           unsigned int big;
           if(edgeBag[i].tSnare & (1 << j)) {     // Present molecules   
                vali = edgeBag[i].ith;   // store the source node
                valj = edgeBag[i].jth;   // Store the target node
                
                if ((graph[valj][vali] >= 1) && (Tedge[valj][vali] & ( 1 << j) )) {
                      C1 = C1 && 1;
                 }

                else { 
         		// g0 is unsigned int checks if there is an edge btw two nodes
                //  It should be on some cycle, So assume that it'll be between 0 and N-2
                //  As we are Only considering elementary cycles.
                __CPROVER_assume( big >= 1 && big <= (N - 2));
     
                 unsigned int path[big];   // An array to store the path taken by molecule.
             
               //  Make sure every int is between 0 and N-1 that represent the node
                for (l = 0; l < big; l++) {           // Dynamic
                      path[l] = zeroTon(N - 1);
                } 
               
	           g0  = graph[valj][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	           v0  = Tedge[valj][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
                   v2  = Tedge[valj][path[0]];
               
                   gl  = graph[path[big -1]][vali];
	           vl  = Tedge[path[big -1]][vali];    // snareVector gets the edgeweight of the corresponding edge.
                   vl2 = Tedge[path[big -1]][vali];

               if (( (( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v2 & (1 << j)) ) )) && ( (( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) )) )  {                  
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
  
     
        C2 = 1;
        C3 = 1;
        
    for  (i = 0; i < len; i++) {
        centTotal = 0b0;
        total = 0b0;
        ticks = 0;
        Ck = 0;
        //  Check if jth vSnare is present then check if all its t-snare frds are present on the edge. 
        //  If yes don't consider him as a cnadidate to check the fusion that happens btw current nodes.
        //  POINT I MISSED : Make sure that t snares are onn, on target node. 
        for  (j = 0; j < snareLength; j++) {
           v = edgeBag[i].vSnare;
           t = edgeBag[i].tSnare;
           f = friendMatrix[j];
           valj = edgeBag[i].jth;
           vali = edgeBag[i].ith;
          
           if  ((v & (1 << j)) && ((t & f) == 0) ) {
              centTotal = centTotal | f;
              ticks = ticks + 1;
              //  Target Edge Should have all required t snares present and Onn in Order to Make fusion Possible.       
              if ( (((Tnodes[valj]  & onOffMatrix[valj] ) & f)  != 0 ) && ((onOffMatrix[vali] & f) == 0)) {
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

         // The combined mask pattern is absent in the all other nodes or 
         // the onOffMatrix cause all the tsnares that are pattern to be absent.
          for (k = 0; (k < N); k++){
              if ((k != edgeBag[i].jth)){
                 //  You can clean It too
                 if(((onOffMatrix[k] & Tnodes[k]) & (edgeBag[i].combinedMask)) == 0) {
                        C3 = C3 && 1;
                  }
                 else {
                      C3 = C3 && 0;
                  }
                }
              }
         }
    
   assert(0);
  __CPROVER_assert((!(C0 && C1 && C2 && C3)), "Graph that satisfy friendZoned model exists");  
  return 0; 
}



