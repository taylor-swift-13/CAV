# P108 Count nums

## Problem (HumanEval 108)

Write a function p108_count_nums which takes a vector of integers && returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, && 3.
>>> p108_count_nums({}) == 0
>>> p108_count_nums({-1, 11, -11}) == 1
>>> p108_count_nums({1, 1, 2}) == 3

## Reference Implementation

```c
/*
Write a function p108_count_nums which takes a vector of integers && returns
the number of elements which has a sum of digits > 0.
If a number is negative, then its first signed digit will be negative:
e.g. -123 has signed digits -1, 2, && 3.
>>> p108_count_nums({}) == 0
>>> p108_count_nums({-1, 11, -11}) == 1
>>> p108_count_nums({1, 1, 2}) == 3
*/

int abs(int x)

{
    if (x < 0) return -x;
    else return x;
}

int p108_count_nums(int* n, int n_size)

{
    int num=0;
    int i;

    for (i=0;i<n_size;i++)
        if (n[i]>0) num+=1;
        else
        {
            int sum=0;
            int w;
            w=abs(n[i]);

            while (w>=10)
            {
                sum+=w%10;
                w=w/10;
            }
            sum-=w;
            if (sum>0) num+=1;
        }
    return num;
}
```
