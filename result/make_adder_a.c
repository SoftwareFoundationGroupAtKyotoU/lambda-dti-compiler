#include <stdio.h>

typedef int r_adder_t;

typedef struct r_var35_t {
	int (*fun)(int, int*);
	int arg;
	int zs[1];
} r_var35_t;

typedef struct makeadder_t {
	r_var35_t (*fun)(int, int*);
	int arg;
	int zs[1];
} makeadder_t;

r_adder_t adder(int y, int zs[1]) {
	int x = zs[0];
	return x + y;
}

r_var35_t var35(int x) {
	r_var35_t f;
	f.fun = adder;
	f.zs[0] = x;
	return f; 
}

r_var35_t makeadder(int x, int zs[1]) {
	int a = zs[0];
	int var37 = a + x;
	return var35(var37);
}

int main() {
	int a = 1;
	makeadder_t f;
	f.fun = makeadder;
	f.zs[0] = a;
	int v3 = 3;
	r_var35_t f_ = f.fun(v3, f.zs);
	int v4 = 4;
	int v = f_.fun(v4, f_.zs);
	printf("%d\n", v);
	return 0;
}

/*
let a = 1;;
let makeadder x = 
  let x = x + a in 
  let adder y = x + y in 
  adder 
in makeadder 3 4;;
*/