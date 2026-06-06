# P031 Is prime

## Problem (HumanEval 31)

Return true if a given number is prime, && false otherwise.
>>> p031_is_prime(6)
false
>>> p031_is_prime(101)
true
>>> p031_is_prime(11)
true
>>> p031_is_prime(13441)
true
>>> p031_is_prime(61)
true
>>> p031_is_prime(4)
false
>>> p031_is_prime(1)
false

## Reference Implementation

```c
bool p031_is_prime(long long n){
    if (n<2) return false;
    for (long long i=2;i*i<=n;i++)
        if (n%i==0) return false;
    return true;
}
```
