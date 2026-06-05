# Prime Length 82

## Problem (HumanEval 82)

Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
prime_length_82("Hello") == true
prime_length_82("abcdcba") == true
prime_length_82("kittens") == true
prime_length_82("orange") == false

## Reference Implementation

```c
bool prime_length_82(const char* str){
    int l,i;
    l=(int)strlen(str);
    if (l<2) return false;
    for (i=2;i*i<=l;i++)
    if (l%i==0) return false;
    return true;
}
```
