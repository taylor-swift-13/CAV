/*
Write a function that takes a string && returns true if the string
length is a prime number || false otherwise
Examples
p082_prime_length("Hello") == true
p082_prime_length("abcdcba") == true
p082_prime_length("kittens") == true
p082_prime_length("orange") == false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_82_pre: list Z -> Prop)
               (problem_82_spec: list Z -> Z -> Prop)
               (prime_prefix: Z -> Z -> Prop) */
/*@ Import Coq Require Import p082_prime_length */

int strlen(char *s)
/*@ With l n
    Require 0 <= n && n < INT_MAX &&
            Zlength(l) == n &&
            (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
            CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int p082_prime_length(char *str)
/*@ With l len
    Require
        0 <= len && len <= 2147302921 &&
        Zlength(l) == len &&
        problem_82_pre(l) &&
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < len) => Znth(k, l, 0) != 0) &&
        problem_82_spec(l, __return) &&
        CharArray::full(str, len + 1, app(l, cons(0, nil)))
*/
{
    int i;
    int n = strlen(str);
    if (n < 2) return 0;

    for (i = 2; i * i <= n; i++) {
        if (n % i == 0) return 0;
    }
    return 1;
}
