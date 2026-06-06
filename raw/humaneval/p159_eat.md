# P159 Eat

## Problem (HumanEval 159)

You"re a hungry rabbit, && you already have eaten a certain number of carrots,
but now you need to p159_eat more carrots to complete the day's meals.
you should return a vector of { total number of eaten carrots after your meals,
                                the number of carrots left after your meals }
if there are ! enough remaining carrots, you will p159_eat all remaining carrots, but will still be hungry.

Example:
* p159_eat(5, 6, 10) -> {11, 4}
* p159_eat(4, 8, 9) -> {12, 1}
* p159_eat(1, 10, 10) -> {11, 0}
* p159_eat(2, 11, 5) -> {7, 0}

Variables:
@number : integer
    the number of carrots that you have eaten.
@need : integer
    the number of carrots that you need to p159_eat.
@remaining : integer
    the number of remaining carrots thet exist in stock

Constrain:
* 0 <= number <= 1000
* 0 <= need <= 1000
* 0 <= remaining <= 1000

Have fun :)

## Reference Implementation

```c
/*
You"re a hungry rabbit, && you already have eaten a certain number of carrots,
but now you need to p159_eat more carrots to complete the day's meals.
you should return a vector of { total number of eaten carrots after your meals,
                                the number of carrots left after your meals }
if there are ! enough remaining carrots, you will p159_eat all remaining carrots, but will still be hungry.

Example:
* p159_eat(5, 6, 10) -> {11, 4}
* p159_eat(4, 8, 9) -> {12, 1}
* p159_eat(1, 10, 10) -> {11, 0}
* p159_eat(2, 11, 5) -> {7, 0}

Variables:
@number : integer
    the number of carrots that you have eaten.
@need : integer
    the number of carrots that you need to p159_eat.
@remaining : integer
    the number of remaining carrots thet exist in stock

Constrain:
* 0 <= number <= 1000
* 0 <= need <= 1000
* 0 <= remaining <= 1000

Have fun :)
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

IntArray *p159_eat(int number,int need,int remaining)

{
    IntArray *out = malloc_int_array_struct();
    out->data = malloc_int_array(2);
    out->size = 2;
    int *data = out->data;
    if (data == 0) {
        out->size = 0;
        return out;
    }
    if (need>remaining) {
        data[0] = number + remaining;
        data[1] = 0;
        return out;
    }
    data[0] = number + need;
    data[1] = remaining - need;
    return out;
}
```
