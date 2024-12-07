#include <stdio.h>

typedef int r_adder_t;

typedef struct cls_adder_t {
	r_adder_t (*fun)(int, int*)
	int arg;
	int zs[1];
} cls_adder_t;

r_adder_t adder(int y, int zs[1]) {
	int x = zs[0];
	return x + y;
}

cls_adder_t makeadder(int x) {
	cls_adder_t f;
	f.fun = adder;
	f.zs[0] = x;
	return f;
}

int main() {
	int v3 = 3;
	cls_adder_t f = makeadder(v3);
	int v4 = 4;
	int v = f.fun(v4, f.zs);
	printf("%d\n", v);
	return 0;
}

/*
let makeadder x = 
  let adder y = x + y in 
  adder 
in makeadder 3 4

===============

let rec (adder.31:int -> int) (y.32:int) = 
  x.30 + y.32 (fv:x.30:int);;

let rec (makeadder.29:int -> int -> int) (x.30:int) = 
  cls (adder.31:int -> int) = adder.31[x.30] in 
  adder.31;;

let (_var.33:int) = 3 in 
let (_var.34:int -> int) = label(makeadder.29) _var.33 in 
let (_var.35:int) = 4 in 
cls(_var.34) _var.35;;

===============

typedef int r_adder_t;

typedef struct cls_adder_t {
	r_adder_t (*fun)(int, int*)
	int arg;
	int zs[1];
} cls_adder_t;

int var33 = 3;

int var35 = 4;

*/