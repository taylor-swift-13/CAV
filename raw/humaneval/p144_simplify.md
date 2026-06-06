# P144 Simplify

## Problem (HumanEval 144)

Your task is to implement a function that will p144_simplify the expression
x * n. The function returns true if x * n evaluates to a whole number && false
otherwise. Both x && n, are string representation of a fraction, && have the following format,
<numerator>/<denominator> where both numerator && denominator are positive whole numbers.

You can assume that x, && n are valid fractions, && do ! have zero as denominator.

p144_simplify("1/5", "5/1") = true
p144_simplify("1/6", "2/1") = false
p144_simplify("7/10", "10/2") = false

## Reference Implementation

```c
/*
Your task is to implement a function that will p144_simplify the expression
x * n. The function returns true if x * n evaluates to a whole number && false
otherwise. Both x && n, are string representation of a fraction, && have the following format,
<numerator>/<denominator> where both numerator && denominator are positive whole numbers.

You can assume that x, && n are valid fractions, && do ! have zero as denominator.

p144_simplify("1/5", "5/1") = true
p144_simplify("1/6", "2/1") = false
p144_simplify("7/10", "10/2") = false
*/

int strlen(char *s)

;

int p144_simplify(char *x, char *n)

{
    int a = 0;
    int b = 0;
    int c = 0;
    int d = 0;
    int i;

    int x_len = strlen(x);

    for (i = 0; x[i] != 47; i++) {
        a = a * 10 + (x[i] - 48);
    }

    i = i + 1;

    for (; i < x_len; i++) {
        b = b * 10 + (x[i] - 48);
    }

    int n_len = strlen(n);


    for (i = 0; n[i] != 47; i++) {
        c = c * 10 + (n[i] - 48);
    }

    i = i + 1;

    for (; i < n_len; i++) {
        d = d * 10 + (n[i] - 48);
    }

    int product_num = a * c;
    int product_den = b * d;
    if (product_num % product_den == 0) return 1;
    return 0;
}
```
