# P082 Prime length

## Problem (HumanEval 82)

Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
p082_prime_length("Hello") == true
p082_prime_length("abcdcba") == true
p082_prime_length("kittens") == true
p082_prime_length("orange") == false

## Reference Implementation

```c
/*
Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
p082_prime_length("Hello") == true
p082_prime_length("abcdcba") == true
p082_prime_length("kittens") == true
p082_prime_length("orange") == false
*/

int strlen(char *s)

;

int p082_prime_length(char *str)

{
    int i;
    int n = strlen(str);
    if (n < 2) return 0;

    for (i = 2; i * i <= n; i++) {
        if (n % i == 0) return 0;
    }
    return 1;
}
```
