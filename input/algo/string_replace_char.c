#include "verification_stdlib.h"
#include "verification_list.h"
#include "char_array_def.h"

void string_replace_char(char *s, char old_c, char new_c)
/*@ With l n
    Require
      0 <= n && n < INT_MAX &&
      Zlength(l) == n &&
      new_c != 0 &&
      (forall (k: Z), (0 <= k && k < n) => Znth(k, l, 0) != 0) &&
      CharArray::full(s, n + 1, app(l, cons(0, nil)))
    Ensure
      exists lr,
        Zlength(lr) == n &&
        (forall (i: Z),
          (0 <= i && i < n) =>
          ((Znth(i, l, 0) == old_c@pre => Znth(i, lr, 0) == new_c@pre) &&
           (Znth(i, l, 0) != old_c@pre => Znth(i, lr, 0) == Znth(i, l, 0)))) &&
        (forall (k: Z), (0 <= k && k < n) => Znth(k, lr, 0) != 0) &&
        CharArray::full(s, n + 1, app(lr, cons(0, nil)))
*/
{
    int i = 0;

    while (1) {
        if (s[i] == 0) {
            break;
        }
        if (s[i] == old_c) {
            s[i] = new_c;
        }
        i++;
    }
}
