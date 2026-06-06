#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

void string_to_upper_ascii(char *s)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          (((97 <= Znth(i, l, 0) && Znth(i, l, 0) <= 122) => Znth(i, lr, 0) == Znth(i, l, 0) - 32) &&
           ((Znth(i, l, 0) < 97 || 122 < Znth(i, l, 0)) => Znth(i, lr, 0) == Znth(i, l, 0)))) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, lr, 0) != 0) &&
        CharArray::full(s, n + 1, app(lr, cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] >= 97 && s[i] <= 122) {
            s[i] = s[i] - 32;
        }
        i++;
    }
}
