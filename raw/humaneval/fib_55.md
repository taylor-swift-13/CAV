# Fib 55

## Problem (HumanEval 55)

Return n-th Fibonacci number.
>>> fib_55(10)
55
>>> fib_55(1)
1
>>> fib_55(8)
21

## Reference Implementation

```c
int fib_55(int n){
    int f[1000];
    f[0]=0;f[1]=1;
    for (int i=2;i<=n; i++)
    f[i]=f[i-1]+f[i-2];
    return f[n];
}
```
