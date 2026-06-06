/*
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
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (problem_127_pre: list Z -> list Z -> Prop)
               (problem_127_spec: list Z -> list Z -> Z -> Prop)
               (interval_int_range: list Z -> Prop)
               (inter_start: list Z -> list Z -> Z)
               (inter_end: list Z -> list Z -> Z)
               (inter_len: list Z -> list Z -> Z)
               (prime_prefix: Z -> Z -> Prop) */
/*@ Import Coq Require Import intersection_127 */

int intersection_127(int* interval1, int interval1_size, int* interval2, int interval2_size)
/*@ With i1 i2
    Require
        interval1_size == 2 &&
        interval2_size == 2 &&
        problem_127_pre(i1, i2) &&
        interval_int_range(i1) &&
        interval_int_range(i2) &&
        IntArray::full(interval1, interval1_size, i1) *
        IntArray::full(interval2, interval2_size, i2)
    Ensure
        problem_127_spec(i1, i2, __return) &&
        IntArray::full(interval1, interval1_size, i1) *
        IntArray::full(interval2, interval2_size, i2)
*/
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
