#include <stdio.h>
#include <stdlib.h>

//  THIS CODE IS FOR THE N = 5 --------------------------------

#define M 20      
#define N 10
#define snareLength 20

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
   snareVector zebraMask[snareLength];
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

//  Setweight function allow only subset to out!
    bitvector setWeight( bitvector node) {
         bitvector edge;
         edge = 0b0;
         unsigned int k;
         for(k=0; k<M; k++){
             if ((node & (0b1 << k)) == (0b1 << k)) {
                    edge =  (edge |  (nondet() << k));
               } 
         }
         return edge;
    }
	
//  ChooseSomef Function  : chose function between 0 and 1


int main (int argc, char** argv)
 {    
	int j; 
    unsigned int pos, i, k, l, w, x, y , iVal, jVal , g, g0, lastg, ng ;
    unsigned int edgePos, bagNo = 0, colorNode = 0 , minColor, cPos = 0;
    unsigned int len = 0, ticks, valj, vali , vSnareChoicet[snareLength] , vSnareChoicef[snareLength];
    _Bool Ck=0, Cf = 1, C0, C1, C2 = 1, C3 = 1, C4, C5; 

    bitvector Vnodes[N];
    bitvector Tnodes[N] ;

    bitvector  fareTotal, inTotal, outTotal , outVSnareTotal , inVSnareTotal , outTSnareTotal , inTSnareTotal ;
    snareVector total, cond2Total, cond2fareTotal, centTotal, placeHolder, v, t, f, v2, lastv, lastv2 ,nv, nv2, v0, v02 ;
    snareVector Tedge[N][N], Vedge[N][N] , Vedge2[N][N] , Tedge2[N][N] ;
    
    //  FriendMatrix is v * t-snare matrix where v snares are rows and T snares are columns
    snareVector friendMatrix[snareLength];     
    //  OnOffMatrix is the N * t-snare matrix where N:nodes are rows and T snares are column  
    snareVector onOffMatrix[N], stCorres , ew;
  
    // Input the graph *******************************************
     unsigned int graph[N][N] =  { {0, 2, 0, 0, 1, 1, 0, 0, 0, 0},
                                {1, 0, 1, 1, 0, 0, 0, 0, 0, 0}, 
							    {1, 0, 0, 0, 0, 0, 1, 0, 0, 0}, 
								{1, 0, 1, 0, 0, 1, 0, 0, 0, 0}, 
								{0, 0, 0, 1, 0, 0, 0, 1, 0, 0}, 
								{0, 0, 0, 0, 1, 0, 0, 0, 0, 2}, 
								{0, 0, 0, 0, 0, 0, 0, 1, 0, 1}, 
							    {1, 0, 0, 0, 0, 0, 0, 0, 2, 0}, 
								{0, 0, 0, 0, 1, 1, 0, 0, 0, 0}, 
								{0, 0, 0, 0, 0, 0, 2, 0, 0, 0}
                          };
  
  

    //  Calculate the total required length that is required for our container
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

    //  Define the Container as Basis of our work  --------------------------
     struct EdgeBag edgeBag[len];
     
    //  Fill the Container values with i, j, edgeWeigth, vsnare, tsnare Values.
    edgePos = 0;
    for(i=0; i<N; i++) {
		for(j=0; j<N; j++) {
            if ((graph[i][j] == 1) || (graph[i][j] == 2)) {
                  edgeBag[edgePos].ith = i;
                  edgeBag[edgePos].jth = j;
                  __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                  __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0); ;
                  Vedge[i][j] = edgeBag[edgePos].vSnare;
                  Tedge[i][j] = edgeBag[edgePos].tSnare;
                  edgePos = edgePos + 1;
            }

            if ((graph[i][j] == 2)) {
                 edgeBag[edgePos].ith = i;
                 edgeBag[edgePos].jth = j;
                  __CPROVER_assume((edgeBag[edgePos].vSnare  & (~ Vnodes[i])) == 0);
                  __CPROVER_assume((edgeBag[edgePos].tSnare  & (~ Tnodes[i])) == 0);
                  Vedge2[i][j] = edgeBag[edgePos].vSnare;
                  Tedge2[i][j] = edgeBag[edgePos].tSnare;
                  edgePos = edgePos + 1;
            }
 
         }
    }

    //  Edgeweight is not allowed to be zero : build C0 to represent that :
    C0 = 1; 
    for (j = 0; j < len; j++) {
         C0 = (C0 && (edgeBag[j].vSnare != 0));
     }
    
    for  (i = 0; i < N; i++) {
        for ( j = 0; j < N; j++) {
            if ( i != j) {
              __CPROVER_assume(Tnodes[i] != Tnodes[j]);
              __CPROVER_assume(Vnodes[i] != Vnodes[j]);
           }
        } 
    }
    
    
     
//  STEADY STATE CONDITION BEGINS --------------------------------------- 
    
//  STEADY STATE CONDITION BEGINS --------------------------------------- 
    
    C1 = 1;

//  VSNARES STEADY SATATE CONDITION TO AVOID ANY CONFISION THIS BAD CODE
	
    i = 0;    // For each Edge == Len 
    for (j = 0; i < len ; j++) {       // for each molecule Plz check the code         
          if (j < M) {

//********************** All those molecules that are present *****************************
// LOGIC TO MAKE SURE that they come back to original node in a cycle
            
            unsigned int big;

            if(edgeBag[i].vSnare & (1 << j)) {     // Present molecules   
          
                vali = edgeBag[i].ith;
                valj = edgeBag[i].jth;
            
                //It should be on some cycle 
                __CPROVER_assume( big >= 1 && big <= (N - 1));

                unsigned int path[big];
              
              //  Make sure every int is between 0 and 9 that represent the node
                for (l = 0; l < big; l++) {           // this is DYNAMIC TOO
                      path[l] = zeroTon(N - 1);
                } 
// ======== JUST TO CHECK MOLECULES COMES BACK IN A CYCLE ======================= 
                for (k = 0; k < big; k++)           // THIS IS DYNAMIC 
                {
				 
				 if ((k == 0) && (k == (big - 1)))  {     // If its first Node and only node
			       if (path[k] == vali) {		 
					 g0  = graph[valj][path[k]];
					 v0  = Vedge[valj][path[k]];
					 v02 = Vedge2[valj][path[k]]; 
                    
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
                           C1 = C1 && 0;
                    }
                    
                  }
                  
                  else if (k == (big - 1)) {     // Last node
					if (path[k] == vali) {
						
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
          else {
               j = -1;             // reset j to 0 incase  where j = 20
               i = i + 1;   
                       // Increment the i    }  
    }
             
      }     
   
  
  
    // FOR TSNARES IN ORDER TO AVOID CONFUSION WE ARE WRITING AWEFUL CODE ;
    
     i = 0;    // For each Edge == Len 
        for (j = 0; i < len ; j++) {       // for each molecule Plz check the code
          
          if (j < M) {
			  
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
					if (path1[k] == vali) {
						
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
          
          else {
             j = -1;
                           // Reste j in case j = 20
             i = i + 1;           // Increment the i   
          }
    }
    
    
    /*
    //  Lets say we have f[#func =  2 ^ 2 ^ N]  = { f0 , f1 , f2 , ... }
    //  Each function will be a table of 2 ^ n length. 
    //  f[i] each is a bitvector array of 2 ^ n length each of snareLength bits long.
    //  Results have been stored on result[#f] as bivector of length snarelength
    //  Write a function that chooses arbir f[] from this function for each vSnare.
    
    */

   // Step1 : Choose arbitary function for each vsnare to t snare :
    for  (i = 0; i < snareLength ; i ++ ) {
         vSnareChoicet[i] = zeroTon(1023);
    }

    for (j = 0; j< snareLength; j++) {
        vSnareChoicef[i] = zeroTon(1023);
    }
    
    // Main restrictions on the program :
  // Main restrictions on the program :
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
          
           if  ((v & (1 << j)) && ((t & f) == 0) ) {  // Jth vsnare is present 
              centTotal = centTotal | f;
              ticks = ticks + 1;
              //  Target Edge Should have all required t snares present and Onn in Order to Make fusion Possible.       
              if ( (((Tnodes[valj]  & onOffMatrix[valj] ) & f)  != 0 ) && ((onOffMatrix[vali] & f) == 0)) {
                 Ck = 1 ;                                  
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

         cond2Total = edgeBag[i].combinedMask;  
         // The combined mask pattern is absent in the all other nodes or 
         // the onOffMatrix cause all the tsnares that are pattern to be absent.
          for (k = 0; (k < N); k++){
              if ((k != edgeBag[i].jth)){
                 //  You can clean It too
                 if(( (onOffMatrix[k]) & cond2Total) == 0) {
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
    for  (i = 0; i < len; i++) {

        printf("The edge No.%d has this config : \n There is an edge between graph[%d][%d]", i, edgeBag[i].ith, edgeBag[i].jth);
        printf(" SourceNodes[%d] (v : t) = (%d , %d)" , edgeBag[i].ith , Vnodes[edgeBag[i].ith] , Tnodes[edgeBag[i].ith]);
        printf(" TargetNodes[%d] (v : t) = (%d , %d) " , edgeBag[i].jth ,Vnodes[edgeBag[i].jth] , Tnodes[edgeBag[i].jth]);
        printf (" vSnare =  %d \n tSnare = %d ", edgeBag[i].vSnare, edgeBag[i].tSnare);
        printf (" combinedMask = %d \n counts = %d \n" ,edgeBag[i].combinedMask, edgeBag[i].count);
   
   }
   

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
  __CPROVER_assert(!(C1 && C2 && C3), "Graph that satisfy friendZoned model exists");  
  return 0; 
}



