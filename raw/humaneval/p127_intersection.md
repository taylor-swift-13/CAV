# P127 Intersection

## Problem (HumanEval 127)

You are given two intervals,
where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
The given intervals are closed which means that the interval (start, end)
includes both start && end.
For each given interval, it is assumed that its start is less || equal its end.
Your task is to determine whether the length of p127_intersection of these two
intervals is a prime number.
Example, the p127_intersection of the intervals (1, 3), (2, 4) is (2, 3)
which its length is 1, which ! a prime number.
If the length of the p127_intersection is a prime number, return "YES",
otherwise, return "NO".
If the two intervals don't intersect, return "NO".


{input/output} samples:
p127_intersection({1, 2}, {2, 3}) ==> "NO"
p127_intersection({-1, 1}, {0, 4}) ==> "NO"
p127_intersection({-3, -1}, {-5, 5}) ==> "YES"

## Reference Implementation

```c
/*
You are given two intervals,
where each interval is a pair of integers. For example, interval = (start, end) = (1, 2).
The given intervals are closed which means that the interval (start, end)
includes both start && end.
For each given interval, it is assumed that its start is less || equal its end.
Your task is to determine whether the length of p127_intersection of these two
intervals is a prime number.
Example, the p127_intersection of the intervals (1, 3), (2, 4) is (2, 3)
which its length is 1, which ! a prime number.
If the length of the p127_intersection is a prime number, return "YES",
otherwise, return "NO".
If the two intervals don't intersect, return "NO".

{input/output} samples:
p127_intersection({1, 2}, {2, 3}) ==> "NO"
p127_intersection({-1, 1}, {0, 4}) ==> "NO"
p127_intersection({-3, -1}, {-5, 5}) ==> "YES"
*/

int p127_intersection(int* interval1, int interval1_size, int* interval2, int interval2_size)

{
    int s1 = interval1[0];
    int e1 = interval1[1];
    int s2 = interval2[0];
    int e2 = interval2[1];
    int inter1;
    int inter2;

    if (s1 > s2) {
        inter1 = s1;
    } else {
        inter1 = s2;
    }
    if (e1 < e2) {
        inter2 = e1;
    } else {
        inter2 = e2;
    }
    int l = inter2 - inter1;

    if (l < 2) return 0;

    int i;

    for (i = 2; i * i <= l; i++) {
        if (l % i == 0) return 0;
    }
    return 1;
}
```
