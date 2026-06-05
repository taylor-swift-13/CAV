# Largest Divisor 24

## Problem (HumanEval 24)

For a given number n, find the largest number that divides n evenly, smaller than n
>>> largest_divisor_24(15)
5

## Reference Implementation

```c
int largest_divisor_24(int n){
    for (int i=2;i*i<=n;i++)
        if (n%i==0) return  n/i;
    return 1;

}
```
