# Any Int 92

## Problem (HumanEval 92)

Create a function that takes 3 numbers.
Returns true if one of the numbers is equal to the sum of the other two, && all numbers are integers.
Returns false in any other cases.

Examples
any_int_92(5, 2, 7) ➞ true

any_int_92(3, 2, 2) ➞ false

any_int_92(3, -2, 1) ➞ true

any_int_92(3.6, -2.2, 2) ➞ false

## Reference Implementation

```c
bool any_int_92(float a, float b, float c){
    if (round(a)!=a) return false;
    if (round(b)!=b) return false;
    if (round(c)!=c) return false;
    if (a+b==c || a+c==b || b+c==a) return true;
    return false;
}
```
