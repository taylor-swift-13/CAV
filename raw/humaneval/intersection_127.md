# Intersection 127

## Problem (HumanEval 127)

You are given two intervals,
where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
The given intervals are closed which means that the interval (start, end)
includes both start && end.
For each given interval, it is assumed that its start is less || equal its end.
Your task is to determine whether the length of intersection_127 of these two 
intervals is a prime number.
Example, the intersection_127 of the intervals (1, 3), (2, 4) is (2, 3)
which its length is 1, which ! a prime number.
If the length of the intersection_127 is a prime number, return "YES",
otherwise, return "NO".
If the two intervals don't intersect, return "NO".


{input/output} samples:
intersection_127({1, 2}, {2, 3}) ==> "NO"
intersection_127({-1, 1}, {0, 4}) ==> "NO"
intersection_127({-3, -1}, {-5, 5}) ==> "YES"

## Reference Implementation

```c
static int max_int(int a, int b){ return a > b ? a : b; }
static int min_int(int a, int b){ return a < b ? a : b; }

const char* intersection_127(int* interval1, int interval1_size, int* interval2, int interval2_size){
    int inter1,inter2,l,i;
    inter1=max_int(interval1[0],interval2[0]);
    inter2=min_int(interval1[1],interval2[1]);
    l=inter2-inter1;
    if (l<2) return "NO";
    for (i=2;i*i<=l;i++)
        if (l%i==0) return "NO";
    return "YES";
}
```
