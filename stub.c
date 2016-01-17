#include <stdio.h>
#include <stdlib.h>

extern void tiger_start(char *, char *);

FILE *tiger_stderr;

int main() {
  char *hp, *sp;

  tiger_stderr = stderr;
  sp = alloca(1000000); hp = malloc(4000000);
  if (hp == NULL || sp == NULL) {
    fprintf(stderr, "malloc or alloca failed\n");
    return 1;
  }
  fprintf(stderr, "sp = %p, hp = %p\n", sp, hp);
  tiger_start(sp, hp);

  return 0;
}
