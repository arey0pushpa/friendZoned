#include <stdio.h>
#include <stdlib.h>

#define M 6	       
#define N 3

_Bool nondet_bool();
unsigned int nondet_uint();

unsigned int zeroTon(unsigned int n) {
    unsigned int result = nondet_uint();
    __CPROVER_assume(result >=0 && result <=n);
    return result ;
};


int main (int argc, char** argv)
 {    
	int j; 
    unsigned int pos, i, k, l, w, x, y ;

    
    for (i = 0; i < 10 ; i++) {              
            
         unsigned int big;

            if(2 > 1) {        
                
                __CPROVER_assume( big >= 1 && big <= (N - 1));

                unsigned int path[big];
                
                for (l = 0; l < big; l++) {           // DYNAMIC  
                      path[l] = zeroTon(N-1);
                } 

                for (k = 0; k < big; k++)           // THIS IS DYNAMIC    
                {
				 printf("cbmc");
		        }
	        }
        }
      
   
        for (j = 0; j < 10 ; j++) {     
            
                unsigned int big2;
            
                if( 10 > 9) {   
                

                __CPROVER_assume(big2 >= 1 && big2 <= (N - 1));

                unsigned int path1[big2];
                
                for (l = 0; l < big2; l++) {                    // THIS IS DYNAMIC
                      path1[l] = zeroTon(N-1);
                }
                
                for (k = 0; k < big2; k++)           // THIS IS DYNAMIC 
                {
					printf("cbmc");
                }
             }
           }

  
        
        assert(0);  
  
        return 1; 
}



