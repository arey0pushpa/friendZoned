#include<stdio.h>


int main() {

    unsigned int a[10];

    __CPROVER_assume(__CPROVER_forall {unsigned int  i ; (i >= 0 && i < 10) ==> (a[i] >= 0 && a[i] <= 9) });

    printf(" a[1] = %d", a[1]);

    assert (0);

    return 0;

}

