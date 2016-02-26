#include <stdio.h>
#include <stdlib.h>

#define M 10	       
#define N 5
#define snareLength 10 
#define bigLen  32
#define len 10

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



int main (int argc, char** argv)

{    

    int j; 
    unsigned int pos, i, k, l, w, x, y , iVal, jVal , g, g0, gl,lastg, ng ;
    unsigned int edgePos, bagNo = 0, colorNode = 0 , minColor, cPos = 0 , tComp, result;
    unsigned int  ticks, valj, vali , calc;
    unsigned int connectedArray[N] = {}, edgeCount = 0;
    bigVector vSnareChoicet[snareLength] , vSnareChoicef[snareLength] , vt , vf,vl , vl2;
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
  
    // Input the graph , Future plans are to make it arbitary 
    unsigned int graph[N][N];
    
    //  Pre-calculate the total required length(#edges) for the containerBag
    for (i = 0; i < N; i++) {
        for (j = 0; j < N; j++) {
            __CPROVER_assume(graph[i][j] >= 0 && graph[i][j] <=2);
             } 
    }
    
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

    // C5 makes sure that its Graph is Strongly connected
    C5 = 1;

    for ( i = 0; i < N; i++) {
        for (j = 0; (j < N) ; j++) {
            if ( graph[i][j] >= 1 && (i != j)) {  // if there is Direct edge we are done
                C5 = C5 && 1;
             }
            else if (i != j) {  // Else case
                unsigned int nub;  // Define max hop
                unsigned int gPath[nub];
                __CPROVER_assume( nub >= 1 && (nub <= N-2));
                
                for (k = 0; k < nub; k++) {
                     gPath[k] = zeroTon(N-1);
                 }
                 
                //  Make sure first edge is connected to i  and last edge is connected to j
                if(graph[i][gPath[0]] >= 1 && (graph[gPath[nub - 1]][j] >= 1))   
                     C5 = C5 && 1;
                else 
                     C5 = 0;

               // rest Of the case is just checking edge btw consecutive array elements
                 for (l = 1; l < nub - 1; l++) {
                       if ( graph[gPath[l]][gPath[l+1]] >= 1 ) 
                               C5 = C5 && 1;
                        else 
                            C5 = 0;
                     }

            }
        }
    }
    
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
// FIRST CONSTARAINT ON THE GRAPH 
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

    //  Edgeweight is not allowed to be zero : build C0 to represent that :
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
       
     
//  STEADY STATE CONDITION BEGINS --------------------------------------- 
/*===========================================================================
 *
 * Formal StateMent :
 *
 *  "All those molecules that are present, MAKE SURE that they come back
 *  to original(Source) Node in a cycle "
 *
 * Qbf :
 *
 * For_All i(#edges),j(#molecules) 
 *      There_Exists path[l] : 
 *                graph (path [1..l])
 *
 * l is max N-2 as we are considering only elementary cycles.
 *
 *============================================================================*/
  
 C1 = 1;


// No.1 : Steady State Condition For VSnares	
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
               
	           g0  = graph[j][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	           v0  = Vedge[j][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
               v2  = Vedge[j][path[0]];
               
               gl  = graph[big][i];
	           vl  = Vedge[big][i];    // snareVector gets the edgeweight of the corresponding edge.
               vl2 = Vedge[big][i];

               if ( (( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v02 & (1 << j)) ) ) &&  (( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) ))  {                  
                   C1 = C1 && 1;
               }

               else {
                   C1 = 0;
               }

               for (k = 1; k < big - 1 ; k++)  {                  // Dynamic 				    	 
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
               
	           g0  = graph[j][path[0]];    // g0 is unsigned int checks if there is an edge btw two nodes
	           v0  = Tedge[j][path[0]];    // snareVector gets the edgeweight of the corresponding edge.
               v2  = Tedge[j][path[0]];
               
               gl  = graph[big][i];
	           vl  = Tedge[big][i];    // snareVector gets the edgeweight of the corresponding edge.
               vl2 = Tedge[big][i];

               if ( (( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v02 & (1 << j)) ) ) &&  (( gl == 1) && (vl & (1 << j))) ||  ( (gl == 2) &&  ( (vl & ( 1 << j)) || ( vl2 & (1 << j)) ) ))  {                  
                   C1 = C1 && 1;
               }

               else {
                   C1 = 0;
               }

               for (k = 1; k < big - 1 ; k++)  {                  // Dynamic 				    	 
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
           }  // else Outside closed
        } 
      }  // jth for closed    
    }   //  ith for closed 
  
     

   /*=================================================================
    * Step1 : Choose arbitary function for each V-snare and T-snare :
    * We are representing each possible function as bitvector.
    * Representing bitvector of length  2 ^ N  gave us power to 
    * represent all 2 ^ (2 ^ N) functions.
    *-================================================================*/

    for  (i = 0; i < snareLength ; i ++ ) {
         vSnareChoicet[i] = nondetBV();
    }

    for (j = 0; j< snareLength; j++) {
        vSnareChoicef[j] = nondetBV();
    }
   
/*========================================================================
Step 2 :
Statement :
 At Least one V-Snare has to be active on the Edge and is causing budding
 according to budding rules.
 
 Check active Vsnares on the edges and then check if they are 
 causing buddying.
 
 Qbf ::
 For_All i(#edges) , j(#V-Snares) ==>
     There_Exists j :
               result := 0 && Ck = 1 
               (Active)       (Satisfy Budding Rule)

Step 3 :
Statement :
  Make Sure that all Edges that are budding to a particular Nodes 
  is not budding with any other Node.

For_All k :
       k != Current Edge target Node ==>
            Budding Not Possible i.e C3 == 1

=======================================================================*/

/* For each edge present  Check if jth V-Snare is present 
 * then check if all its t-snare frds are present on the edge. 
 * If yes don't consider him as a cnadidate to check the fusion 
 * that happens btw current source and target  nodes.
 * POINT I MISSED : Make sure that t snares are onn, on target node. 
 */
     
    for (i = 0; i < len; i++) {  
		ticks = 0;
        for  (j = 0; j < snareLength; j++) {    // For each elemet you have to follow some rules 
               v = edgeBag[i].vSnare;
               t = edgeBag[i].tSnare;
               // f = friendMatrix[j];
               valj = edgeBag[i].jth;
               vali = edgeBag[i].ith;
          
          if  (v & (1 << j))  {  // jth vsnare is present on the edge  
          // Logic whether vsnare is active  or not
              tComp = t;    // Converting bitvector to the integer number                 
              vt = vSnareChoicet[j];   // bitvector representation of function 
              result = vt & (b1 << tComp);    // Find whether its active based upon the function choosen
              if (result == 0) {   // Means jth vsnare is active 
                 edgeBag[i].zebra[ticks] = j;  // add to the array the active v snares index
                  ticks  +=  1;
              }
// ** Target Edge Should have all required t snares present and Onn in Order to Make fusion Possible.                   
              // Fcompp represent the Active T-Snares on the nOde 
		      fComp  =  (Tnodes[valj] & onOffMatrix[valj]);    // On Target Node
              bComp  =  (Tnodes[vali] & onOffMatrix[vali]);    // On the Source Node 			  
              // Take Bitvector representation of the function
              vf  =  vSnareChoicef[j];
                  
			  // First part makes sure that fusion is allowed and second part states that back fusion is not allowed
              // vf & active t snares should == 1 for f comp and vf & active vsnares == 0 for b comp
              if (  (vf  & (b1 << fComp)) && ( (vf & (b1 << bComp)) == 0 ))  {
                         Ck = 1 ;                                  
              }
            }
           
         edgeBag[i].count = ticks;
         if(Ck == 1) {
             C2 = C2 && 1;
         }
         else {
             C2 = C2 && 0;
         }
    }
        // cond2Total = edgeBag[i].combinedMask; 
         // The combined mask pattern is absent in the all other nodes or 
         // the onOffMatrix cause all the tsnares that are pattern to be absent.
         for (k = 0; (k < N); k++){
              if ((k != edgeBag[i].jth)){	  
                  // Will represent the bitvector of the node
 			      bComp =  Tnodes[k] & onOffMatrix[k] ;   // Convert the bitvector into interger number		  
			       // For each active v snares that might be reasponsible for fusion make sure its not making glue to others
			      for (l = 0 ; l < edgeBag[i].count; l++) {           // THIS IS DYNAMIC CODE    
			           vf = vSnareChoicef[edgeBag[i].zebra[l]];  // Convert the chosen number into the bitvector
			           if ( (vf & (b1 << bComp)) == 0) {
                          C3 = C3 && 1;
                        }
                       else {
                          C3 = C3 && 0;
                       }
                  }
              }
         }
    }

//  assert(0);
  __CPROVER_assert(!(C0 && C1 && !(C2) && C3 && C4), "Graph that satisfy friendZoned model exists");   
  return 0; 
}



