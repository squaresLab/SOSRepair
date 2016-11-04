/**/
#include <stdio.h>

struct s{
        int a;
}

int main (int argc) {
        int a, b, c;    //**/
        FILE *f = fopen("alaki.txt", "w");
        struct s *e;
        e->a++;
        char *d;
        fprintf(f, "salam");
        ALAKI(f);
        printf("Please enter 3 numbers separated by spaces > ");
                scanf("%d%d%d", &a, &b, &c);
        a = b + 2;
        e->a = 5;
        c = c * 5;
        if ((a > b && b > c) || (c > b && b > a)) {
                printf ("%d is the median\n", b);
                printf ("%s\n", d);
                }
//        else if ((b > a && a > c) || (c > a && a > b)) {
//                printf ("%d is the median\n", a);
//                }
//        else if ((a > c && c > b) || (b > c && c > a)) {
//                printf ("%d is the median\n", c);
//                }
        fclose(f);
        return 0;
}