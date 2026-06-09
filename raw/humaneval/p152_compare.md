# P152 Compare

## Problem (HumanEval 152)

I think we all remember that feeling when the result of some long-awaited
event is finally known. The feelings && thoughts you have at that moment are
definitely worth noting down && comparing.
Your task is to determine if a person correctly guessed the results of a number of matches.
You are given two vectors of scores && guesses of equal length, where each index shows a match.
Return a vector of the same length denoting how far off each guess was. If they have guessed correctly,
the value is 0, && if !, the value is the absolute difference between the guess && the score.


example:

p152_compare({1,2,3,4,5,1},{1,2,3,4,2,-2}) -> {0,0,0,0,3,3}
p152_compare({0,5,0,0,0,4},{4,1,1,0,0,-2}) -> {4,4,1,0,0,6}

## Stub Function Specifications

Contract stage must preserve these helper/external functions as explicit stubs, give each one a function contract, and implement any logical meaning with definition-only Coq in the companion `.v`. Do not use `Axiom`, `Parameter`, `Hypothesis`, `Admitted`, or proof-only assumptions for stub semantics.

### `malloc_int_array_struct`

Allocates a fresh `IntArray` header object.

Contract shape:

```c
IntArray *malloc_int_array_struct()
/*@ Require emp
    Ensure __return != 0 &&
           undef_data_at(&(__return -> data)) *
           undef_data_at(&(__return -> size))
*/;
```

### `malloc_int_array`

Allocates a fresh writable integer array with unspecified contents.

Contract shape:

```c
int *malloc_int_array(int size)
/*@ Require size >= 0 && size < INT_MAX
    Ensure __return != 0 && IntArray::undef_full(__return, size)
*/;
```

### `abs`

Coq model:

```coq
Definition he_abs_spec (x r : Z) : Prop :=
  r = Z.abs x.
```

Contract shape:

```c
int abs(int x)
/*@ Require INT_MIN < x && x <= INT_MAX
    Ensure he_abs_spec(x, __return)
*/;
```

## Reference Implementation

```c
/*
Your task is to determine if a person correctly guessed the results of a number of matches.
You are given two arrays of scores and guesses of equal length, where each index shows a match.
Return an array of the same length denoting how far off each guess was. If they have guessed correctly,
the value is 0, and if not, the value is the absolute difference between the guess and the score.
*/

typedef struct {
    int* data;
    int size;
} IntArray;

IntArray *malloc_int_array_struct()
;

int *malloc_int_array(int size)
;

int abs(int x)

{
    if (x < 0) return -x;
    else return x;
}

IntArray *p152_compare(int* game, int game_size, int* guess, int guess_size)

{
    IntArray *out = malloc_int_array_struct();
    int n = game_size < guess_size ? game_size : guess_size;
    out->size = n;
    out->data = malloc_int_array(n);
    int *data = out->data;
    if (data == 0) {
        out->size = 0;
        return out;
    }
    int i;

    for (i=0;i<n;i++) {
        int diff;
        int value;
        diff = game[i] - guess[i];
        value = abs(diff);
        data[i] = value;

    }
    return out;
}
```
