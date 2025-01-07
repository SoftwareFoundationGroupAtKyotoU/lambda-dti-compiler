#ifndef CAST_H
#define CAST_H

typedef struct ran_pol {
	char *filename;
	int startline;
	int startchr;
	int endline;
	int endchr;
	int polarity;
} ran_pol;

typedef union value value;

typedef enum ground_ty {
	G_INT,
	G_BOOL,
	G_UNIT,
	G_AR,
} ground_ty;

typedef struct dyn {
	value *v;
	ground_ty g;
	ran_pol r_p;
} dyn;

typedef struct ty ty;

typedef struct ty {
	enum tykind {
		DYN,
		BASE_INT,
		BASE_BOOL,
		BASE_UNIT,
		TYFUN,
		TYVAR,
	} tykind;
	struct tyfun {
		ty *left;
		ty *right;
	} tyfun;
} ty;

typedef struct fun fun;

typedef struct fun {
	enum funkind {
		LABEL,
		CLOSURE,
		WRAPPED,
	} funkind;
	union fundat {
		value (*label)(value);
		struct closure {
			value (*cls)(value, value*);
			value *fvs;
		} closure;
		struct wrap {
			fun *w;
			ty *u1;
			ty *u2;
			ty *u3;
			ty *u4;
			ran_pol r_p;
		} wrap;
	} fundat;
} fun;

typedef union value {
	int i_b_u;
	dyn d;
	fun f;
} value;

value cast(value, ty*, ty*, ran_pol);

value app(value, value);

extern ty tydyn;
extern ty tyint;
extern ty tybool;
extern ty tyunit;
extern ty tyar;

extern value (fun_print_int)(value);
extern value (fun_print_bool)(value);
extern value (fun_print_newline)(value);

extern value print_int;
extern value print_bool;
extern value print_newline;

#endif