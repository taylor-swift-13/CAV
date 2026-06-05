# Is Prime 31

## Problem (HumanEval 31)

Return true if a given number is prime, && false otherwise.
>>> is_prime_31(6)
false
>>> is_prime_31(101)
true
>>> is_prime_31(11)
true
>>> is_prime_31(13441)
true
>>> is_prime_31(61)
true
>>> is_prime_31(4)
false
>>> is_prime_31(1)
false

## Reference Implementation

```c
bool is_prime_31(long long n){
    if (n<2) return false;
    for (long long i=2;i*i<=n;i++)
        if (n%i==0) return false;
    return true;
}
```
