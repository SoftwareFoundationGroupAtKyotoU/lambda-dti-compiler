#include <stdio.h>
#include <stdlib.h> //for abort
#include "cast.h"

ty tydyn = { .tykind = DYN };
ty tyint = { .tykind = BASE_INT };
ty tybool = { .tykind = BASE_BOOL };
ty tyunit = { .tykind = BASE_UNIT };
ty tyar = { .tykind = TYFUN, .tyfun = { .left = &tydyn, .right = &tydyn } };

int is_ground(ty t){
	switch(t.tykind) {
		case(BASE_INT):
		case(BASE_BOOL):
		case(BASE_UNIT):
		return 1;
		break;

		case(TYFUN):
		ty l = *t.tyfun.left;
		ty r = *t.tyfun.right;
		if (l.tykind == DYN && r.tykind == DYN) {
			return 1;
		} else {
			return 0;
		}
		break;

		case(TYVAR):
		return 0;
		break;
	}
}

ground_ty to_ground(ty t){
	switch(t.tykind) {
		case(BASE_INT):
		return G_INT;
		break;

		case(BASE_BOOL):
		return G_BOOL;
		break;

		case(BASE_UNIT):
		return G_UNIT;
		break;

		case(TYFUN):
		ty l = *t.tyfun.left;
		ty r = *t.tyfun.left;
		if (l.tykind == DYN && r.tykind == DYN) {
			return G_AR;
		} else {
			printf("not ground type was applied\n");
			abort();
		}
		break;
	}
}

value cast(value x, ty *t1, ty *t2) {							// input = x:t1=>t2
	value retx;
	if (t1->tykind == TYFUN && t2->tykind == TYFUN) { 				// when t1 and t2 are function type
		printf("defined as a wrapped function\n");						// define x:U1->U2=>U3->U4 as wrapped function
		retx.f.fundat.wrap.w = (fun*)malloc(sizeof(fun));
		*retx.f.fundat.wrap.w = x.f;
		retx.f.fundat.wrap.u1 = t1->tyfun.left;
		retx.f.fundat.wrap.u2 = t1->tyfun.right;
		retx.f.fundat.wrap.u3 = t2->tyfun.left;
		retx.f.fundat.wrap.u4 = t2->tyfun.right;
		retx.f.funkind = WRAPPED;
	} else if (is_ground(*t1) == 1 && t2->tykind == DYN) {			// when t1 is ground and t2 is ?
		printf("defined as a dyn value\n");								// define x:G=>? as dynamic type value
		retx.d.v = (value*)malloc(sizeof(value));
		*retx.d.v = x;
		retx.d.g = to_ground(*t1);
	} else if (t1->tykind == DYN && t2->tykind == DYN) {			// when t1 and t2 are ?
		printf ("ID STAR\n");											// R_IDSTAR (x:?=>? -> x)
		retx.d = x.d;
	} else if (t1->tykind == BASE_INT && t2->tykind == BASE_INT) {	// when t1 and t2 are int
		printf ("ID BASE by int\n");									// R_IDBASE (x:int=>int -> x)
		retx.i_b_u = x.i_b_u;
	} else if (t1->tykind == BASE_BOOL && t2->tykind == BASE_BOOL) {// when t1 and t2 are bool
		printf ("ID BASE by bool\n");									// R_IDBASE (x:bool=>bool -> x)
		retx.i_b_u = x.i_b_u;
	} else if (t1->tykind == BASE_UNIT && t2->tykind == BASE_UNIT) {// when t1 and t2 are unit
		printf ("ID BASE by unit\n");									// R_IDBASE (x:unit=>unit -> x)
		retx.i_b_u = x.i_b_u;
	} else if (t1->tykind == DYN && is_ground(*t2) == 1) {			// when t1 is ? and t2 is ground type
		ground_ty t = x.d.g;
		ground_ty t_ = to_ground(*t2);
		if (t == t_) {													// when t1's injection ground type equals t2
			printf("cast success\n");										// R_SUCCEED (x':G=>?=>G -> x')
			retx = *x.d.v;
		} else if (t != t_) {											// when t1's injection ground type dosen't equal t2
			printf("cast fail\n");											// E_FAIL (x':G1=>?=>G2 if G1<>G2 -> blame)
			abort();
		} else {
			printf("cannot reachable\n");
			abort();
		}
	} else if (t1->tykind == TYFUN && t2->tykind == DYN) {			// when t1 is function type and t2 is ?
		printf("cast ground\n");
		value x_ = cast(x, t1, &tyar);									// R_GROUND (x:U=>? -> x:U=>G=>U)
		retx = cast(x_, &tyar, t2);
	} else if (t1->tykind == DYN && t2->tykind == TYFUN) {			// when t1 is ? and t2 is function type
		printf("cast expand\n");
		value x_ = cast(x, t1, &tyar);									// R_EXPAND (x:?=>U -> x:?=>G=>U)
		retx = cast(x_, &tyar, t2); 
	} else if (t1->tykind == DYN && t2->tykind == TYVAR){			// when t1 is ? and t2 is type variable
		switch(x.d.g){
			case(G_INT):												// when t1's injection ground type is int
			printf("DTI : int was inferenced\n");							// R_INSTBASE (x':int=>?=>X -[X:=int]> x')
			*t2 = tyint;
			retx = *x.d.v;
			break;

			case(G_BOOL):												// when t1's injection ground type is bool	
			printf("DTI : bool was inferenced\n");							// R_INSTBASE (x':bool=>?=>X -[X:=bool]> x')
			*t2 = tybool;
			retx = *x.d.v;
			break;

			case(G_UNIT):												// when t1's injection ground type is unit
			printf("DTI : unit was inferenced\n");							// R_INSTBASE (x':unit=>?=>X -[X:=unit]> x')
			*t2 = tyunit;
			retx = *x.d.v;
			break;

			case(G_AR):													// when t1's injection ground type is ?->?
			printf("DTI : array was inferenced\n");							// R_INSTARROW (x':?->?=>?=>X -[X:=X_1->X_2]> x':?->?=>X_1->X_2)
			t2->tykind = TYFUN;
			t2->tyfun.left = (ty*)malloc(sizeof(ty));
			t2->tyfun.right = (ty*)malloc(sizeof(ty));
			t2->tyfun.left->tykind = TYVAR;
			t2->tyfun.right->tykind = TYVAR;
			retx = cast(*x.d.v, &tyar, t2);
			break;
		}
	} else {
		printf("cast cannot be resolved\n");
		abort();
	}
	return retx;
}

value app(value f, value v) {									// reduction of f(v)
	value retx;
	switch(f.f.funkind) {
		case(LABEL):												// if f is "label" function
		value (*l)(value) = f.f.fundat.label;							// R_BETA : return f(v)
		retx = l(v);
		break;

		case(CLOSURE):												// if f is closure
		value (*c)(value, value*) = f.f.fundat.closure.cls;				// R_BETA : return f(v, fvs)
		retx = c(v, f.f.fundat.closure.fvs);
		break;

		case(WRAPPED):												// if f is wrapped function (f = w:U1->U2=>U3->U4)
		value f1;														// R_APPCAST : return (w(v:U3=>U1)):U2=>U4
		f1.f = *f.f.fundat.wrap.w;
		value v_ = cast(v, f.f.fundat.wrap.u3, f.f.fundat.wrap.u1);
		value v__ = app(f1, v_);
		retx = cast(v__, f.f.fundat.wrap.u2, f.f.fundat.wrap.u4);
		break;
	}
	return retx;
}

value fun_print_int(value v) {
	printf("%d", v.i_b_u);
	value retunit = { .i_b_u = 0 };
	return retunit;
}

value print_int = { .f = { .fundat = { .label = fun_print_int }, .funkind = LABEL } };

value fun_print_bool(value v) {
	int i = v.i_b_u;
	if (i == 1) {
		printf("true");
	} else if (i == 0) {
		printf("false");
	} else {
		printf("error:not boolean value is applied to print_bool");
		abort();
	}
	value retunit = { .i_b_u = 0 };
	return retunit;
}

value print_bool = { .f = { .fundat = { .label = fun_print_bool }, .funkind = LABEL } };

value fun_print_newline(value v) {
	int i = v.i_b_u;
	if (i == 0) {
		printf("\n");
	} else {
		printf("error:not unit value is applied to print_newline");
		abort();
	}
	value retunit = { .i_b_u = 0 };
	return retunit;
}

value print_newline_ = { .f = { .fundat = { .label = fun_print_newline }, .funkind = LABEL } };