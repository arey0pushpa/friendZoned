#include<stdio.h>


int main() {

    unsigned int a[10];
    unsigned int b[10];

    __CPROVER_assert(__CPROVER_forall {unsigned int  i ; ((i >= 0 && i < 10)) ==> (__CPROVER_forall { unsigned int j; ( j >= 0 && j > 10) ==> a[i] >= a[j]) }},"Exists");


    printf(" a[1] = %d", a[1]);

   // assert (0);

    return 1;

}

