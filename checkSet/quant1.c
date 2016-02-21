#include<stdio.h>


int main() {

    unsigned int a[10];

    assert(__CPROVER_exists {unsigned int  i ; (i >= 0 && i < 10) ==> a[i] <= 0});

    printf(" a[1] = %d", a[1]);

    //assert (0);

    return 1;

}

