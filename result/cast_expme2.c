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
		ty tyl = o->con.c.latter;
		obj *o_ = o->con.c.v;	//place o_ as inner object
		switch(o_->tag) {
		case NO_CAST:			//for examle, o = (o_:int => ★)
			return *o;
		case CAST:
			ty tyf = o_->con.c.former;
			if (tyf == tyl) {		//when o is ((v:tyf => ★):★ => tyl)
				printf("%s\n", "cast success");
				return *o_->con.c.v;
			} else {
				printf("%s\n", "not equal");
				abort(); //yet
			}
		case BLAME:	//yet
			abort();
		}
	case BLAME:		//yet
		abort();
	}
}

obj f(obj x){										//let f x =
	cast cast_x_cast = {&x, TDyn, TInt, 37, P}; 	//let cast_x = (x:★ => int) in
	content cast_x_content;
	cast_x_content.c = cast_x_cast;
	obj cast_x = {cast_x_content, CAST};
	cast_x = resolve(&cast_x);						//(resolve cast)
	int int_1_int = 1;								//let int_1 = 1 in
	content int_1_content;
	int_1_content.i = int_1_int;
	obj int_1 = {int_1_content, NO_CAST};
	int int_plus_int = cast_x.con.i + int_1.con.i;	//cast_x + int_1
	content int_plus_content;
	int_plus_content.i = int_plus_int;
	obj int_plus = {int_plus_content, NO_CAST};
	return int_plus;
}

int main() {
	int int_4_int = 4;								//let int_4 = 4 in
	content int_4_content;
	int_4_content.i = int_4_int;
	obj int_4 = {int_4_content, NO_CAST};
	cast cast_4_cast = {&int_4, TInt, TDyn, 26, P};	//let cast_4 = (4:int => ★) in
	content cast_4_content;
	cast_4_content.c = cast_4_cast;
	obj cast_4 = {cast_4_content, CAST};
	cast_4 = resolve(&cast_4);						//(resolve cast)
	obj int_print = f(cast_4);						//let int_print = f (cast_4) in
	int int_print_int = int_print.con.i;			//print_int (int_print)
	printf("%d\n", int_print_int);								
	return 0;
}