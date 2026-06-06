/*
Write a function vowels_count_64 which takes a string representing a word as input && returns the number of vowels in the string. Vowels in this case are 'a', 'e', 'i', 'o', 'u'. 
Here, 'y' is also a vowel, but only when it is at the end of the given word.
Example: 
>>> vowels_count_64("abcde") 
2 
>>> vowels_count_64("ACEDY") 
3
*/
#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

/*@ Extern Coq (problem_64_pre: list Z -> Prop)
               (problem_64_spec: list Z -> Z -> Prop)
               (ascii_range: list Z -> Prop)
               (count_regular_vowels_upto: Z -> list Z -> Z)
               (last_y_add: list Z -> Z) */
/*@ Import Coq Require Import vowels_count_64 */

int strlen(char *s)
/*@ With l n
    Require CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure __return == n &&
           CharArray::full(s, n + 1, app(l, cons(0, nil)))
*/
;

int vowels_count_64(char *s)
/*@ With l len
    Require
        0 <= len && len < INT_MAX &&
        Zlength(l) == len &&
        problem_64_pre(l) &&
        ascii_range(l) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
    Ensure
        problem_64_spec(l, __return) &&
        CharArray::full(s, len + 1, app(l, cons(0, nil)))
*/
{
    int n = strlen(s);
    int count = 0;
    int i;
    
    for (i = 0; i < n; i++) {
        if (s[i] == 97 || s[i] == 101 || s[i] == 105 ||
            s[i] == 111 || s[i] == 117 ||
            s[i] == 65 || s[i] == 69 || s[i] == 73 ||
            s[i] == 79 || s[i] == 85) {
            count = count + 1;
        }
    }
    if (n > 0 && (s[n - 1] == 121 || s[n - 1] == 89)) {
        count = count + 1;
    }
    return count;
}
