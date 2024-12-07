#include <stdio.h>
#include <stdlib.h> //for abort

typedef struct obj obj;

typedef enum {
	TDyn,
	TInt,
	TBool,
	TUnit
} ty;

typedef enum {
	P,
	N
} dir;

typedef struct cast {
	obj *v;
	ty former;
	ty latter;
	int blame;
	dir d;
} cast;

typedef union content {
	int i;
	cast c;
} content;

typedef enum t {
	NO_CAST,
	CAST,
	BLAME
} t;

typedef struct obj {
	content con;
	t tag;
} obj;

obj resolve(obj *o) {
	switch(o->tag) {
	case NO_CAST:
		return *o;
	case CAST:
		ty tyf = o->con.c.former;
		obj *o_ = o->con.c.v;
		switch(o_->tag) {
			case NO_CAST:
				return *o;
			case CAST:
				ty tyl = o_->con.c.latter;
				if (tyf == tyl) {
					return *o_->con.c.v;
				}
			case BLAME:
				abort();
		}
	case BLAME:
		abort();
	}
}

int main() {
	int iv = 1;
	content icon;
	icon.i = iv;
	obj v = {icon, NO_CAST};
	cast ca = {&v, TInt, TDyn, 26, P};
	content acon;
	acon.c = ca;
	obj a = {acon, CAST};
	a = resolve(&a);
	cast cb = {&a, TDyn, TInt, 34, P};
	content bcon;
	bcon.c = cb;
	obj b = {bcon, CAST};
	b = resolve(&b);
	int bn = b.con.i;
	printf("%d\n", bn);
	return 0;
}