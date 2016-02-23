#include<stdio.h>

int main() {
    unsigned int i,j,x;
    j = 0;
    x = 10;

    for (i=0;i<10;i++) {
        j++;
        x--;
    }

    printf(" i = %d , j = %d , x = %d", i , j , x);

    assert(0);

    return 0;

}
