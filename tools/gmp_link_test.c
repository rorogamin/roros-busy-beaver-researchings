#include <stdio.h>

typedef struct { int alloc; int size; unsigned long *d; } mpz_s;
typedef mpz_s mpz_t[1];

void __gmpz_init(mpz_t);
void __gmpz_set_ui(mpz_t, unsigned long);
void __gmpz_add_ui(mpz_t, const mpz_t, unsigned long);
char *__gmpz_get_str(char *, int, const mpz_t);

int main(void) {
  mpz_t x;
  __gmpz_init(x);
  __gmpz_set_ui(x, 12345UL);
  __gmpz_add_ui(x, x, 7UL);
  char *s = __gmpz_get_str(NULL, 10, x);
  puts(s);
  return 0;
}
