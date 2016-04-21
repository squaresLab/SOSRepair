/**/

#include <stdio.h>
#include <math.h>

int main() {
	int a, b, c, median;
	char *d = "salam";
	int e[10];
	*d = "hi";
	printf("Please enter 3 numbers separated by spaces > ");
//	scanf("%d%d%d", &a, &b, &c);
	if ((a<=b && a>=c) || (a>=b && a<=c))
		median = a;
	else if ((b<=a && b>=c) || (b>=a && b<=c))
		median = b;
	else if ((c<=b && a>=c) || (c>=b && a<=c))
		median = c;
	printf("%d is the median\n", median);
	return 0;
	
}
