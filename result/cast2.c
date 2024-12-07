#include <stdio.h>
#include <stdlib.h> //for abort

typedef struct obj obj;

typedef enum ty {
	TDyn,
	TInt,
	TBool,
	TUnit
} ty;

typedef enum dir { //for direction of cast
	P,
	N
} dir;

typedef struct cast { //(v: former =>^(d*blame) latter)
	obj *v; 	
	ty former;	
	ty latter;
	int blame;
	dir d;
} cast;

typedef union content {
	int i;
	cast c;
	//function later
} content;

typedef enum tag_name { //represents what type the content has
	NO_CAST,
	CAST,
	BLAME
} tag_name;

typedef struct obj {
	content con;
	tag_name tag;
} obj;

obj resolve(obj *o) {
	switch(o->tag) {
	case NO_CAST:	//when o has no cast, return o itself
		return *o;
	case CAST:		//when o has a cast, check inner object
		ty tyf = o->con.c.former;
		obj *o_ = o->con.c.v;	//place o_ as inner object
		switch(o_->tag) {
			case NO_CAST:		//for examle, o = (o_:int => ★)
				return *o;
			case CAST:
				ty tyl = o_->con.c.latter;
				if (tyf == tyl) {		//when o is ((v:int => ★):★:int)
					return *o_->con.c.v;
				}
			case BLAME:	//yet
				abort();
		}
	case BLAME:		//yet
		abort();
	}
}

obj f(obj x){
	cast cast_x_cast = {&x, TDyn, TInt, 37, P};
	content cast_x_content;
	cast_x_content.c = cast_x_cast;
	obj cast_x = {cast_x_content, CAST};
	cast_x = resolve(&cast_x);
	int int_1_int = 1;
	content int_1_content;
	int_1_content.i = int_1_int;
	obj int_1 = {int_1_content, NO_CAST};
	int int_plus_int = cast_x.con.i + int_1.con.i;
	content int_plus_content;
	int_plus_content.i = int_plus_int;
	obj int_plus = {int_plus_content, NO_CAST};
	return int_plus;
}

int main() {
	int int_4_int = 4;
	content int_4_content;
	int_4_content.i = int_4_int;
	obj int_4 = {int_4_content, NO_CAST};
	cast cast_4_cast = {&int_4, TInt, TDyn, 26, P};
	content cast_4_content;
	cast_4_content.c = cast_4_cast;
	obj cast_4 = {cast_4_content, CAST};
	cast_4 = resolve(&cast_4);
	obj b = f(cast_4);
	int bn = b.con.i;
	printf("%d\n", bn);
	return 0;
}