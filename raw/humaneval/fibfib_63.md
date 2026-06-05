# Fibfib 63

## Problem (HumanEval 63)

The FibFib number sequence is a sequence similar to the Fibbonacci sequnece that's defined as follows:
fibfib_63(0) == 0
fibfib_63(1) == 0
fibfib_63(2) == 1
fibfib_63(n) == fibfib_63(n-1) + fibfib_63(n-2) + fibfib_63(n-3).
Please write a function to efficiently compute the n-th element of the fibfib_63 number sequence.
>>> fibfib_63(1)
0
>>> fibfib_63(5)
4
>>> fibfib_63(8)
24

## Reference Implementation

```c
int fibfib_63(int n){
    int ff[100];
    ff[0]=0;
    ff[1]=0;
    ff[2]=1;
    for (int i=3;i<=n;i++)
        ff[i]=ff[i-1]+ff[i-2]+ff[i-3];
    return ff[n];

}
```
