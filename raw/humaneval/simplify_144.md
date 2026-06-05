# Simplify 144

## Problem (HumanEval 144)

Your task is to implement a function that will simplify_144 the expression
x * n. The function returns true if x * n evaluates to a whole number && false
otherwise. Both x && n, are string representation of a fraction, && have the following format,
<numerator>/<denominator> where both numerator && denominator are positive whole numbers.

You can assume that x, && n are valid fractions, && do ! have zero as denominator.

simplify_144("1/5", "5/1") = true
simplify_144("1/6", "2/1") = false
simplify_144("7/10", "10/2") = false

## Reference Implementation

```c
bool simplify_144(const char* x, const char* n){
    int a,b,c,d;
    if (sscanf(x, "%d/%d", &a, &b) != 2) return false;
    if (sscanf(n, "%d/%d", &c, &d) != 2) return false;
    if ((a*c)%(b*d)==0) return true;
    return false;
}
```
