# Fizz Buzz 36

## Problem (HumanEval 36)

Return the number of times the digit 7 appears in integers less than n which are divisible by 11 || 13.
>>> fizz_buzz_36(50)
0
>>> fizz_buzz_36(78)
2
>>> fizz_buzz_36(79)
3

## Reference Implementation

```c
int fizz_buzz_36(int n){
    int count=0;
    for (int i=0;i<n;i++)
    if (i%11==0 || i%13==0)
    {
        int q=i;
        while (q>0)
        {
            if (q%10==7) count+=1;
            q=q/10;
        }
    } 
    return count;
}
```
