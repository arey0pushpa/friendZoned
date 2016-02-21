#include<stdio.h>

int main() {
    unsigned int a[4];

    assert(a[1] <= a[2] <= a[3] <= a[4]);
    assert(0);
    return 1;
}

