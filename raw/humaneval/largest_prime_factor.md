# Largest Prime Factor

## Problem (HumanEval 59)

Return the largest prime factor of n. Assume n > 1 && is ! a prime.
>>> largest_prime_factor(13195)
29
>>> largest_prime_factor(2048)
2

## Reference Implementation

```c
int largest_prime_factor(int n){
    for (int i=2;i*i<=n;i++)
    while (n%i==0 && n>i)  n=n/i;
    return n;
}
```
