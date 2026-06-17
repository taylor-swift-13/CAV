/*
Checks if given string is a palindrome
>>> p048_is_palindrome("")
true
>>> p048_is_palindrome("aba")
true
>>> p048_is_palindrome("aaaaa")
true
>>> p048_is_palindrome("zbcd")
false
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_48_pre: list Z -> Prop)
               (problem_48_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop) */
/*@ Import Coq Require Import string_bridge */
/*@ Import Coq Require Import p048_is_palindrome */

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

int p048_is_palindrome(char *text)
/*@ With l n
    Require
        0 <= n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_48_pre(l) &&
        ascii_range(l) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
        CharArray::full(text, n + 1, app(l, cons(0, nil)))
    Ensure
        (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
        problem_48_spec(l, __return) &&
        CharArray::full(text, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;
    int j = strlen(text) /*@ where l = l, n = n */;

    if (j == 0) {
        return 1;
    }

    j = j - 1;
    /*@ Inv Assert
        text == text@pre &&
        0 < n && n < INT_MAX &&
        Zlength(l) == n &&
        problem_48_pre(l) &&
        ascii_range(l) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
        0 <= i && i <= n &&
        0 <= j && j < n &&
        i + j == n - 1 &&
        CharArray::full(text, n + 1, app(l, cons(0, nil))) &&
        (forall (k: Z), (0 <= k && k < i) =>
            Znth(k, l, 0) == Znth(n - 1 - k, l, 0))
    */
    while (i < j) {
        if (text[i] != text[j]) {
            return 0;
        }
        i = i + 1;
        j = j - 1;
    }
    return 1;
}
