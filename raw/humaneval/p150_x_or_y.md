# P150 X or y

## Problem (HumanEval 150)

A simple program which should return the value of x if n is
a prime number && should return the value of y otherwise.

Examples:
for p150_x_or_y(7, 34, 12) == 34
for p150_x_or_y(15, 8, 5) == 5

## Reference Implementation

```c
/*
A simple program which should return the value of x if n is
a prime number && should return the value of y otherwise.

Examples:
for p150_x_or_y(7, 34, 12) == 34
for p150_x_or_y(15, 8, 5) == 5

*/

int p150_x_or_y(int n, int x, int y)

{
    int isp=1;
    if (n<2) isp=0;
    int i;

    for (i=2;i<=n/i;i++)
    if (n%i==0) isp=0;
    if (isp) return x;
    return y;
}
```
