# P107 Even odd palindrome

## Problem (HumanEval 107)

Given a positive integer n, return a vector that has the number of even && odd
integer palindromes that fall within the range(1, n), inclusive.

Example 1:

    Input: 3
    Output: (1, 2)
    Explanation:
    Integer palindrome are 1, 2, 3. one of them is even, && two of them are odd.

Example 2:

    Input: 12
    Output: (4, 6)
    Explanation:
    Integer palindrome are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11. four of them are even, && 6 of them are odd.

Note:
    1. 1 <= n <= 10^3
    2. returned vector has the number of even && odd integer palindromes respectively.

## Reference Implementation

```c
/*
Given a positive integer n, return a vector that has the number of even && odd
integer palindromes that fall within the range(1, n), inclusive.

Example 1:

    Input: 3
    Output: (1, 2)
    Explanation:
    Integer palindrome are 1, 2, 3. one of them is even, && two of them are odd.

Example 2:

    Input: 12
    Output: (4, 6)
    Explanation:
    Integer palindrome are 1, 2, 3, 4, 5, 6, 7, 8, 9, 11. four of them are even, && 6 of them are odd.

Note:
    1. 1 <= n <= 10^3
    2. returned vector has the number of even && odd integer palindromes respectively.
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

static int is_pal(int x)

{
    int r = 0;
    int t = x;

    while (t > 0) {
        r = r * 10 + (t % 10);
        t /= 10;
    }
    return r == x;
}

IntArray *p107_even_odd_palindrome(int n)

{
    int num1=0,num2=0;
    IntArray *out = malloc_int_array_struct();
    int i;

    for (i=1;i<=n;i++)
    {
        if (is_pal(i) && i%2==1) num1+=1;
        if (is_pal(i) && i%2==0) num2+=1;
    }
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    data[0] = num2;
    data[1] = num1;
    return out;
}
```
