# P024 Largest divisor

## Problem (HumanEval 24)

For a given number n, find the largest number that divides n evenly, smaller than n
>>> p024_largest_divisor(15)
5

## Reference Implementation

```c
int p024_largest_divisor(int n){
    for (int i=2;i*i<=n;i++)
        if (n%i==0) return  n/i;
    return 1;

}
```
