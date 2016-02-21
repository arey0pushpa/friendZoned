#include<stdio.h>

void main() {
    int x ;
    int y;

    x  = x + y;

    if(x !=3) {
        x = 2;
    }
    else {
        x ++;
    }


    assert(x <= 3);
    
    return 1;
}

