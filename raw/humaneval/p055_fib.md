# P055 Fib

## Problem (HumanEval 55)

Return n-th Fibonacci number.
>>> p055_fib(10)
55
>>> p055_fib(1)
1
>>> p055_fib(8)
21

## Reference Implementation

```c
/*
Return n-th Fibonacci number (1-indexed: p055_fib(1)=1, p055_fib(2)=1, p055_fib(3)=2, ...).
Rewritten to avoid local arrays: uses two rolling variables.
>>> p055_fib(10) = 55
>>> p055_fib(1)  = 1
>>> p055_fib(8)  = 21
*/

int p055_fib(int n)

{
    int a;
    int b;
    int c;
    int i;
    a = 0;
    b = 1;

    for (i = 2; i <= n; i++) {
        c = a + b;
        a = b;
        b = c;
    }
    return b;
}
```
