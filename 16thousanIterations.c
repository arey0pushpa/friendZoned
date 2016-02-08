#include<stdio.h>
#include<stdlib.h>



int main() {
   unsigned int x,y,z;
   for ( x  = 0; x < 8000; x ++) {
       for ( z =0; z < 8000; z++) {
           x = x + 1;
          if ( 10 > 2) {
             y = 2 + 2;
          }
          else {
             printf("ghost");
          }
       }
         //  printf(
       printf("cbmc");
   }

   assert(0);
}

