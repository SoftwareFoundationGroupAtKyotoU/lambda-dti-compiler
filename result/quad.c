#include <stdio.h>

int dbl(int x) {
	int y = x + x;
	return y;
}

int quad(int x) {
	int y = dbl(x);
	int z = dbl(y);
	return z;
}

int main() {
	int x = quad(4);
	printf("%d\n", x);
	return 0;
}
