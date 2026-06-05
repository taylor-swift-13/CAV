# Is Multiply Prime 75

## Problem (HumanEval 75)

Write a function that returns true if the given number is the multiplication of 3 prime numbers
&& false otherwise.
Knowing that (a) is less then 100. 
Example:
is_multiply_prime_75(30) == true
30 = 2 * 3 * 5

## Reference Implementation

```c
bool is_multiply_prime_75(int a){
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
