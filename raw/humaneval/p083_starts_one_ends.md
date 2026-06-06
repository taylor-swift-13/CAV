# P083 Starts one ends

## Problem (HumanEval 83)

Given a positive integer n, return the count of the numbers of n-digit
positive integers that start || end with 1.

## Reference Implementation

```c
int p083_starts_one_ends(int n){
    if (n<1) return 0;
    if (n==1) return 1;
    int out=18;
    for (int i=2;i<n;i++)
        out=out*10;
    return out;
}
```
