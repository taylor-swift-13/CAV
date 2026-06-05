#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (ex_anagram_count_pre : list Z -> list Z -> Prop) */
/*@ Extern Coq (ex_anagram_count_spec : list Z -> list Z -> Z) */
/*@ Import Coq Require Import ex_anagram_count */

int ex_anagram_count(const char *subject, const char *candidates)
/*@ With ls lc ns nc
    Require
      subject != 0 && candidates != 0 &&
      0 <= ns && ns < 2147483647 &&
      0 <= nc && nc < 2147483647 &&
      Zlength(ls) == ns &&
      Zlength(lc) == nc &&
      (forall (k: Z), (0 <= k && k < ns) => ls[k] != 0) &&
      (forall (k: Z), (0 <= k && k < nc) => lc[k] != 0) &&
      ex_anagram_count_pre(ls, lc) &&
      CharArray::full((char *)subject, ns + 1, app(ls, cons(0, nil))) *
      CharArray::full((char *)candidates, nc + 1, app(lc, cons(0, nil)))
    Ensure
      __return == ex_anagram_count_spec(ls, lc) &&
      CharArray::full((char *)subject, ns + 1, app(ls, cons(0, nil))) *
      CharArray::full((char *)candidates, nc + 1, app(lc, cons(0, nil)))
*/
{
    int sl = 0;
    int base[26];
    int ans = 0;
    int i = 0;
    int k;

    while (1) {
        if (subject[sl] == 0) {
            break;
        }
        sl++;
    }

    k = 0;
    while (k < 26) {
        base[k] = 0;
        k++;
    }

    k = 0;
    while (k < sl) {
        int ch = subject[k];

        if (65 <= ch && ch <= 90) {
            ch = ch - 65 + 97;
        }
        base[ch - 97]++;
        k++;
    }

    while (1) {
        int start;
        int end;
        int same;
        int cur[26];

        if (candidates[i] == 0) {
            break;
        }

        start = i;
        while (1) {
            if (candidates[i] == 0) {
                break;
            }
            if (candidates[i] == 59) {
                break;
            }
            i++;
        }
        end = i;

        same = sl == end - start;
        k = 0;
        while (k < sl) {
            int a;
            int b;

            if (!same) {
                break;
            }

            a = subject[k];
            b = candidates[start + k];
            if (65 <= a && a <= 90) {
                a = a - 65 + 97;
            }
            if (65 <= b && b <= 90) {
                b = b - 65 + 97;
            }
            if (a != b) {
                same = 0;
            }
            k++;
        }

        k = 0;
        while (k < 26) {
            cur[k] = 0;
            k++;
        }

        k = start;
        while (k < end) {
            int ch = candidates[k];

            if (65 <= ch && ch <= 90) {
                ch = ch - 65 + 97;
            }
            cur[ch - 97]++;
            k++;
        }

        {
            int ok = !same;

            k = 0;
            while (k < 26) {
                if (base[k] != cur[k]) {
                    ok = 0;
                }
                k++;
            }
            if (ok) {
                ans++;
            }
        }

        if (candidates[i] == 59) {
            i++;
        }
    }

    return ans;
}
