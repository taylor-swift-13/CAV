# Digits 131

## Problem (HumanEval 131)

Given a positive integer n, return the product of the odd digits_131.
Return 0 if all digits_131 are even.
For example:
digits_131(1)  == 1
digits_131(4)  == 0
digits_131(235) == 15

## Reference Implementation

```c
int digits_131(int n){
    int prod=1,has=0;
    if (n == 0) return 0;
    while (n > 0) {
        int d = n % 10;
        if (d % 2 == 1) {
            has = 1;
            prod *= d;
        }
        n /= 10;
    }
    if (has==0) return 0;
    return prod;
}
```
