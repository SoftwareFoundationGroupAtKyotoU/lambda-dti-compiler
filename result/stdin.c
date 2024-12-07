#include <stdio.h>

typedef struct cls_f_32_t {
        int (*fun)(int, int*);
        int arg;
        int zs[2];
} cls_f_32_t;

int f_32(int x_33, int zs[2]) {
        int a_29 = zs[0];
        int c_31 = zs[1];
        int _var_34 = c_31 / a_29;
        return x_33 + _var_34;
}

int main() {
        int a_29 = 2;
        int b_30 = 3;
        int c_31 = 4;
        cls_f_32_t f_32_;
        f_32_.fun = f_32;
        f_32_.zs[0] = a_29;
        f_32_.zs[1] = c_31;
        int _var_35 = 5;
        int _var_36 = f_32_.fun(_var_35, f_32_.zs);
        printf("%d\n", _var_36);
        return 0;
}