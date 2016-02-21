#include<stdio.h>

void main() {
    int x ;
    int y = 8 , z = 0, w =0;

    if(x) {
        z = y + 1;
    }

    else {
        z = y -1;
    }

    assert(z == 7 || z == 9);
    
    return 1;
}

