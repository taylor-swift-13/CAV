# P131 Digits

## Problem (HumanEval 131)

Given a positive integer n, return the product of the odd p131_digits.
Return 0 if all p131_digits are even.
For example:
p131_digits(1)  == 1
p131_digits(4)  == 0
p131_digits(235) == 15

## Reference Implementation

```c
/*
Given a positive integer n, return the product of the odd p131_digits.
Return 0 if all p131_digits are even.
For example:
p131_digits(1)  == 1
p131_digits(4)  == 0
p131_digits(235) == 15
*/

int p131_digits(int n)

{
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
