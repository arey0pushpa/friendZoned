#include<stdio.h>

int main() {
    unsigned int x , y ,i;
   
    x  =10;
    y = 0;

    for (i=0;i<10;i++) {
        x --;
       y++;
    }

    assert(x >0 && y>=10);
  return 1;
}
