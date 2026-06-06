# P075 Is multiply prime

## Problem (HumanEval 75)

Write a function that returns true if the given number is the multiplication of 3 prime numbers
&& false otherwise.
Knowing that (a) is less then 100.
Example:
p075_is_multiply_prime(30) == true
30 = 2 * 3 * 5

## Reference Implementation

```c
bool p075_is_multiply_prime(int a){
    int num=0;
    for (int i=2;i*i<=a;i++)
    while (a%i==0 && a>i)
    {
        a=a/i;
        num+=1;
    }
    if (num==2) return true;
    return false;
}
```
