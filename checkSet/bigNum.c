#include <stdio.h>
#include <gmp.h>
#include<stdarg.h>
#include<obstack.h>

int main(void) {
 mpz_t x,y,result;

 mpz_init_set_str(x, "7612058254738945", 10);
 mpz_init_set_str(y, "9263591128439081", 10);
 mpz_init(result);

 mpz_mul(result, x, y);
 gmp_printf("    %Zd\n"
            "*\n"
            "    %Zd\n"
            "--------------------\n"
            "%Zd\n", x, y, result);

 /* free used memory */
 mpz_clear(x);
 mpz_clear(y);
 mpz_clear(result);
 assert(0);
 return 0;
}
