#include<stdio.h>

#define N 4
#define C 3
#define len 4


unsigned int nondet_uint();
_Bool nondet_bool();


unsigned int oneTon (unsigned int n){  
    unsigned int result = nondet_uint();
       __CPROVER_assume(result>=1 && result<=n);
          return result;
};



int  main() 
{
    unsigned int i, j, colorSet[len];
    _Bool Cl;
    unsigned int graph[N][N] = { {0,1,0,0},
                                 {0,0,1,0},
                                 {0,0,0,1},
                                 {1,0,0,0}};
                                 
 
    // Constraint 1 : all nodes are of some color 
      
    for (i = 0; i < N; i++){
            colorSet[i] = oneTon(C);
     }
 
  
    // Constraine 2 : If two edges are connected then both can't have same color.
      Cl = 1;
      for (i = 0; i < len; i++){
	      for ( j = 0; j < len; j++){
	          if(graph[i][j] == 1) 
                   Cl = Cl && (colorSet[i] != colorSet[j]); 
          }
      }

   __CPROVER_assert(!(Cl) , "Graph has three color Solution"); 


}

