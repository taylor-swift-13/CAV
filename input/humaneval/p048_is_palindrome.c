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
/*@ Import Coq Require Import p048_is_palindrome */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
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
        CharArray::full(text, n + 1, app(l, cons(0, nil)))
    Ensure
        problem_48_spec(l, __return) &&
        CharArray::full(text, n + 1, app(l, cons(0, nil)))
*/
{
    int i = 0;
    int j = strlen(text);

    if (j == 0) {
        return 1;
    }

    j = j - 1;

    while (i < j) {
        if (text[i] != text[j]) {
            return 0;
        }
        i = i + 1;
        j = j - 1;
    }
    return 1;
}
