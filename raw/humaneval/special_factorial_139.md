# Special Factorial 139

## Problem (HumanEval 139)

The Brazilian factorial is defined as:
brazilian_factorial(n) = n! * (n-1)! * (n-2)! * ... * 1!
where n > 0

For example:
>>> special_factorial_139(4)
288

The function will receive an integer as input && should return the special
factorial of this integer.

## Reference Implementation

```c
long long special_factorial_139(int n){
    long long fact=1,bfact=1;
    for (int i=1;i<=n;i++)
    {
        fact=fact*i;
        bfact=bfact*fact;
    }
    return bfact;
}
```
