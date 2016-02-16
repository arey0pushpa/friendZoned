#include <stdio.h>
#include <stdlib.h>

//  THIS CODE IS FOR THE Arbitary grah with 3 conncted and 4 conncted added constrint --------------------------------
// Starting with N  = 5

#define M 18	       
#define N 9
#define snareLength 9
#define bigLen  512

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
    unsigned int graph[N][N] = {{1,0,1,1,1,1,0,1,0},
                                {1,1,1,1,1,1,1,2,0},
                                {1,1,1,1,1,1,1,2,1},
                                {1,1,1,1,1,1,1,1,0},
                                {1,1,1,0,1,1,1,1,0},
                                {1,1,1,1,1,1,0,0,1},
                                {1,1,1,1,1,1,1,0,1},
                                {1,1,1,1,1,1,1,0,1},
                                {1,2,1,1,1,0,1,1,1}};
    
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

    // __CPROVER_assume(len >= (2 * N));


    //  Define the Container as Basis of our work  --------------------------
    //  Declare a Structure array of length =  len ; Will give structure to things coming
    struct EdgeBag edgeBag[len];
     
    //  Fill the Container values with i, j, edgeWeigth, vsnare, tsnare Values.
    edgePos = 0;
    for  (i = 0; i < N; i++) {
	for  (j = 0; j < N; j++) {
              if ((graph[i][j] == 1) || (graph[i][j] == 2)) {
                  
                  edgeBag[edgePos].ith = i;     // Record the source node
                  edgeBag[edgePos].jth = j;     // Record the target Node
                 
                  // Avoid use of subset function
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
                  
                 // Avoid use of subset function
                  __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                  __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0);
                  
                  // Additional Vedge2[i][j] and Tedge2[i][j] is used to be lookup value in global steady state check condition.
                  Vedge2[i][j] = edgeBag[edgePos].vSnare;
                  Tedge2[i][j] = edgeBag[edgePos].tSnare;
                  edgePos = edgePos + 1;
            }
 
         }
    }

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

        
        // ------------------- Next two constrints are temporary and only required in case of reporting 
        // The counterexample as this type of constraints helps make biological sense of program..


    //  Edgeweight is not allowed to be zero : build C0 to represent that :
    C0 = 1; 
    for (j = 0; j < len; j++) {   //  DYNAMIC
         C0 = (C0 && (edgeBag[j].vSnare != 0));
     }
   //  Make assumption that each TNodes will be differnt.    
    for  (i = 0; i < N; i++) {
        for ( j = 0; j < N; j++) {
            if ( i != j) {
              __CPROVER_assume(Tnodes[i] != Tnodes[j]);
              __CPROVER_assume(Vnodes[i] != Vnodes[j]);
           }
        } 
    }
    
    
     
//  STEADY STATE CONDITION BEGINS --------------------------------------- 
    
    C1 = 1;


//  JUST FOR VSNARES STEADY SATATE CONDITION, TO AVOID ANY CONFISION THIS IS BAD CODE
	
   for ( i = 0; i < len; i++ ) {      // For each Edge  
     for (j = 0; j < M ; j++) {       // for each molecule          

//  All those molecules that are present, MAKE SURE that they come back to original node in a cycle
//  ONLY FOR Vsnares 
            
            unsigned int big;

            if(edgeBag[i].vSnare & (1 << j)) {     // Present molecules   
          
                vali = edgeBag[i].ith;   // store the source node
                valj = edgeBag[i].jth;   // Store the target node
            
                //  It should be on some cycle, So assume that it'll be between 1 and 9.
                //  As we are Only considering elementary cycles.

                __CPROVER_assume( big >= 1 && big <= (N - 1));

                unsigned int path[big];   // An array to store the path taken by molecule.
              
               //  Make sure every int is between 0 and 9 that represent the node
               //  Allowing Only eight steps max will force to write one more block.
 
                for (l = 0; l < big; l++) {           // this is DYNAMIC TOO
                      path[l] = zeroTon(N - 1);
                } 

// ======== JUST TO CHECK MOLECULES COMES BACK IN A CYCLE ======================= 

                for (k = 0; k < big; k++)           // THIS IS DYNAMIC 
                {
				 
				 if ((k == 0) && (k == (big - 1)))  {     // If its first Node and only node
                                       // Big == 1
	        		       if (path[k] == vali) {	       // path[k] == vali represents same node	 
					 g0  = graph[valj][path[k]];    // g0 is unsigned int checks if there is an edge btw two nodes
					 v0  = Vedge[valj][path[k]];    // snareVector gets the edgeweight of the corresponding edge.
					 // V02 has been used to get the edgeweight in case graph[i][j] = 2.
                                         v02 = Vedge2[valj][path[k]];   // snareVecor gets the edgeweight of second edge if graph[i][j] == 2 !

                    // Check that there is an edge btw valj ---- pathk  and under investigation vsnare is present on edge.
                    if ( (( g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v02 & (1 << j)) ) ))  {
                             C1 = C1 && 1;
                    }
                    else {
                           C1 = C1 && 0;
                    }
				   }
				   else {
					   C1 = 0;
				   }
                    
                  }
                  
                 else if (k == 0) {                    // If its first Node edge
					 g  = graph[valj][path[k]];
					 v  = Vedge[valj][path[k]];
					 v2 = Vedge2[valj][path[k]]; 
                    
                    if ( (( g == 1) && (v & (1 << j))) ||  ( (g == 2) &&  ( (v & ( 1 << j)) || ( v2 & (1 << j)) ) ))  {
                             C1 = C1 && 1;
                    }
                    else {
                           C1 =  0;
                    }
                    
                  }
                  
                  else if (k == (big - 1)) {     // Last node

                            // In case of last node.
						
					 lastg  = graph[path[k]][vali];
					 lastv  = Vedge[path[k]][vali];
					 lastv2 = Vedge2[path[k]][vali];
                     
                     if  ( (( lastg == 1) && (lastv & (1 << j)) ) || ((lastg == 2) && ((lastv & (1 << j)) || (lastv2 & (1 << j))) ) )
                      {
						 C1 = C1 && 1;
				      }
				      
				      else {
					 	 C1 = 0;
					  }
				    }
				    
				    
				 
                 else {         // Any other node besides first and last   					
					
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
// -------------------------- MOLECULE CAME BACK IN A CYCLE -------------------------
	        }
	        
		  }
             
      }     
   
  
  
    // FOR TSNARES IN ORDER TO AVOID CONFUSION . Else in a single for loop we could have written for both v and t snares;
    
      for ( i = 0; i < len; i++) {  // For each Edge == Len  
          for (j = 0; j < M ; j++) {       // for each molecule Plz check the code
          
			  
//********************** All those molecules that are present *****************************
// LOGIC TO MAKE SURE that they come back to original node in a cycle        
            
            if(edgeBag[i].tSnare & (1 << j)) {   // All those molecules that are present
                
                unsigned int big2;

                vali = edgeBag[i].ith;
                valj = edgeBag[i].jth;
            
                //It should be on some cycle 
                __CPROVER_assume( 1 <= big2 && big2 <= (N - 1));

                unsigned int path1[big2];
       
      // each elemet int should be between 0 and 9 i.represnt the nodes        
                for (l = 0; l < big2; l++) {                    // THIS IS DYNAMIC
                      path1[l] = zeroTon(N - 1);
                }
                
// ======== Just make sure molecules come back in the cycle form =======================
                for (k = 0; k < big2; k++)           // THIS IS DYNAMIC 
                {
				 
				 if ((k == 0) && (k == (big2 - 1)))  {     // If its first Node and only node
			       if (path1[k] == vali) {		 
					 g0  = graph[valj][path1[k]];
					 v0  = Tedge[valj][path1[k]];
					 v02 = Tedge2[valj][path1[k]]; 
                    
                    if ( ((g0 == 1) && (v0 & (1 << j))) ||  ( (g0 == 2) &&  ( (v0 & ( 1 << j)) || ( v02 & (1 << j)) ) ))  {
                             C1 = C1 && 1;
                    }
                    else {
                           C1 = C1 && 0;
                    }
				   }
				   else {
					   C1 = 0;
				   }
                    
                  }
                  
                 else if (k == 0) {                    // If its first Node edge
					 g  = graph[valj][path1[k]];
					 v  = Tedge[valj][path1[k]];
					 v2 = Tedge2[valj][path1[k]]; 
                    
                    if ( (( g == 1) && (v & (1 << j))) ||  ( (g == 2) &&  ( (v & ( 1 << j)) || ( v2 & (1 << j)) ) ))  {
                             C1 = C1 && 1;
                    }
                    else {
                           C1 = C1 && 0;
                    }
                    
                  }
                  
                  else if (k == (big2 - 1)) {     // Last node
						
					 lastg  = graph[path1[k]][vali];
					 lastv  = Tedge[path1[k]][vali];
					 lastv2 = Tedge2[path1[k]][vali];
                     
                     if  ( (( lastg == 1) && (lastv & (1 << j)) ) || ((lastg == 2) && ((lastv & (1 << j)) || (lastv2 & (1 << j))) ) )
                      {
						 C1 = C1 && 1;
				      }
				      
				      else {
					 	 C1 = 0;
					  }
				    }
				 
                 else {         // Any other node besides first and last   					
					
					ng  = graph[path1[k]][path1[k+1]];
					nv  = Tedge[path1[k]][path1[k+1]];
					nv2 = Tedge2[path1[k]][path1[k+1]];
					
                    if (((ng == 1) && (nv & (1 << j))) ||  ( (ng == 2) && ((nv & (1 << j)) || (nv2 & (1 << j))) )) {
                             C1 = C1 && 1;
                    }
                    else {
                        C1 = 0;
                    }
                 }
                 
             }
 // Made sure that the molecule got back in the form of the cycle =======================            
             
           }
             
          }
          
    }
     

   // Step1 : Choose arbitary function for each vsnare to t snare :
      //  We are representing each possible function as bitvector representing bitvector of length 
      // 1024 gave us power to represent all 2 ^ 1024 functions.

    for  (i = 0; i < snareLength ; i ++ ) {
         vSnareChoicet[i] = nondetBV();
    }

    for (j = 0; j< snareLength; j++) {
        vSnareChoicef[i] = nondetBV();
    }
    
    // Main restrictions on the program :
    
    
    // For each edge present
        //  Check if jth vSnare is present then check if all its t-snare frds are present on the edge. 
        //  If yes don't consider him as a cnadidate to check the fusion that happens btw current nodes.
        //  POINT I MISSED : Make sure that t snares are onn, on target node. 
     
    for (i = 0; i < len; i++) {   // DYNAMIC 
        for  (j = 0; j < M; j++) {    // For each elemet you have to follow some rules 
		  
               v = edgeBag[i].vSnare;
               t = edgeBag[i].tSnare;
                  // f = friendMatrix[j];
               valj = edgeBag[i].jth;
               vali = edgeBag[i].ith;
          
          if  (v & (1 << j))  {  // jth vsnare is present on the edge  
       
              // Logic for active vsnare or not
              
              tComp = t;    // Converting bitvector to the integer number                 

              vt = vSnareChoicet[j];   // bitvector representation of function 
             
              result = vt & (b1 << tComp);    // Find whether its active based upon the function choosen
			  

              if (result == 0) {   // Means jth vsnare is active 
                 edgeBag[i].zebra[ticks] = j;  // add to the array the active v snares index
                  ticks  +=  1;
                  }
	
              //  Target Edge Should have all required t snares present and Onn in Order to Make fusion Possible.       
                  
		      // Fcompp represent the Active T-Snares on the nOde 
		          fComp  =  (Tnodes[valj]  & onOffMatrix[valj] ); // On Target Node
                  bComp  =  Tnodes[vali] & onOffMatrix[vali] ;    // On the Source Node 			  

			  //  Take Bitvector representation of the function
                  vf  =  vSnareChoicef[j];
                  
				  // First part makes sure that fusion is allowed and second part states that back fusion is not allowed
                  // vf & active t snares should == 1 for f comp and vf & active vsnares == 0 for b comp
                  if (  (vf  & ( b1 << fComp)) && ( (vf & ( b1 << bComp)) == 0 ))  {
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

         cond2Total = edgeBag[i].combinedMask; 

         // The combined mask pattern is absent in the all other nodes or 
         // the onOffMatrix cause all the tsnares that are pattern to be absent.
          for (k = 0; (k < N); k++){
              if ((k != edgeBag[i].jth)){
				  
            // Will represent the bitvector of the node
 			  bComp =  Tnodes[k] & onOffMatrix[k] ;   // Convert the bitvector into interger number
			 			  
			  // For each active v snares that might be reasponsible for fusion make sure its not making glue to others
			  for (l = 0 ; l < ticks ; l++) {           // THIS IS DYNAMIC CODE   
                
			    vf = vSnareChoicef[edgeBag[i].zebra[l]];  // Convert the chosen number into the bitvector
	
			    if ( (vf & (b1 << bComp)) == 0)
                  {
					  
                        C3 = C3 && 1;
                  }
                 else {
                      C3 = C3 && 0;
                  }
				  }
        
        }
		
         }



    
//  BASIC BLOCK ENDS -----------------------------------------------------------------------------------------

    for  (i = 0; i < N; i++){
        printf("\n VNodes[%d] = %d" , i , Vnodes[i]);
        printf(" TNodes[%d] = %d" , i , Tnodes[i]);
        
    }
    /*
    for  (i = 0; i < len; i++) {  //

        printf("The edge No.%d has this config : \n There is an edge between graph[%d][%d]", i, edgeBag[i].ith, edgeBag[i].jth);
        printf(" SourceNodes[%d] (v : t) = (%d , %d)" , edgeBag[i].ith , Vnodes[edgeBag[i].ith] , Tnodes[edgeBag[i].ith]);
        printf(" TargetNodes[%d] (v : t) = (%d , %d) " , edgeBag[i].jth ,Vnodes[edgeBag[i].jth] , Tnodes[edgeBag[i].jth]);
        printf (" vSnare =  %d \n tSnare = %d ", edgeBag[i].vSnare, edgeBag[i].tSnare);
        printf (" combinedMask = %d \n counts = %d \n" ,edgeBag[i].combinedMask, edgeBag[i].count);
   
   }
   */

    for  (i = 0; i < snareLength; i++) {
        printf( " The InteractionMatrix[%d] = %d ", i , friendMatrix[i]);
    }
    printf( " \n");
    for  (i = 0; i < N; i++){
        printf(" The onOffMatrix[%d] = %d ", i, onOffMatrix[i]);
    }

    printf("\nThe value of : \n C0 = %d \n C1 : %d \n C2 : %d , C3 : %d \n",C0,C1,C2,C3);
    printf(" the value of mr.Ticks is %d and len was %d ", ticks , len);
    
  // assert(0);
  __CPROVER_assert(!(C1 && C2 && C3 && C4), "Graph that satisfy friendZoned model exists");  
  return 0; 
}



