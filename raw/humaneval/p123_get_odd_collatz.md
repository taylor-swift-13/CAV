# P123 Get odd collatz

## Problem (HumanEval 123)

Given a positive integer n, return a sorted vector that has the odd numbers in collatz sequence.

The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
as follows: start with any positive integer n. Then each term is obtained from the
previous term as follows: if the previous term is even, the next term is one half of
the previous term. If the previous term is odd, the next term is 3 times the previous
term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

Note:
    1. Collatz(1) is {1}.
    2. returned vector sorted in increasing order.

For example:
p123_get_odd_collatz(5) returns {1, 5} // The collatz sequence for 5 is {5, 16, 8, 4, 2, 1}, so the odd numbers are only 1, && 5.

## Reference Implementation

```c
/*
Given a positive integer n, return a sorted vector that has the odd numbers in collatz sequence.

The Collatz conjecture is a conjecture in mathematics that concerns a sequence defined
as follows: start with any positive integer n. Then each term is obtained from the
previous term as follows: if the previous term is even, the next term is one half of
the previous term. If the previous term is odd, the next term is 3 times the previous
term plus 1. The conjecture is that no matter what value of n, the sequence will always reach 1.

Note:
    1. Collatz(1) is {1}.
    2. returned vector sorted in increasing order.

For example:
p123_get_odd_collatz(5) returns {1, 5} // The collatz sequence for 5 is {5, 16, 8, 4, 2, 1}, so the odd numbers are only 1, && 5.
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

void sort_int_array(int *array, int init_size, int size, int ascending)
;

IntArray *p123_get_odd_collatz(int n)

{
    IntArray *out = malloc_int_array_struct();
    out->size = 0;
    out->data = malloc_int_array(1024);
    int *data = out->data;
    int output_size = 0;

    data[output_size] = 1;
    output_size = output_size + 1;

    while (n != 1) {

        if (n % 2 == 1) {

            data[output_size] = n;
            output_size++;

            n = n * 3 + 1;
        } else {
            n = n / 2;
        }
    }

    sort_int_array(data, output_size, 1024, 1);

    out->size = output_size;
    return out;
}
```
