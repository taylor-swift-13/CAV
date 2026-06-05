#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (decode_xored_array_csv_pre : list Z -> Z -> Z -> Prop) */
/*@ Extern Coq (decode_xored_array_csv_spec : list Z -> Z -> list Z) */
/*@ Import Coq Require Import decode_xored_array_csv */

int decode_xored_array_csv(const char *encoded, int first, char *out, int out_cap)
/*@ With l d n
    Require
      encoded != 0 && out != 0 &&
      0 <= first && first <= 2147483647 &&
      0 <= n && n < 2147483647 &&
      0 <= out_cap &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      decode_xored_array_csv_pre(l, first, out_cap) &&
      CharArray::full((char *)encoded, n + 1, app(l, cons(0, nil))) *
      CharArray::full(out, out_cap, d)
    Ensure
      exists t,
        __return == Zlength(decode_xored_array_csv_spec(l, first)) &&
        Zlength(t) == out_cap - 1 - Zlength(decode_xored_array_csv_spec(l, first)) &&
        CharArray::full((char *)encoded, n + 1, app(l, cons(0, nil))) *
        CharArray::full(out, out_cap,
          app(app(decode_xored_array_csv_spec(l, first), cons(0, nil)), t))
*/
{
    int pos = 0;
    int cur = first;
    int w;
    int digits[10];
    int m;
    int i = 0;

    w = cur;
    if (w == 0) {
        out[pos] = 48;
        pos++;
    } else {
        m = 0;
        while (w > 0) {
            digits[m] = w % 10;
            w = w / 10;
            m++;
        }
        while (m > 0) {
            m--;
            out[pos] = digits[m] + 48;
            pos++;
        }
    }

    while (1) {
        int v;

        if (encoded[i] == 0) {
            break;
        }

        v = 0;
        while (encoded[i] >= 48 && encoded[i] <= 57) {
            v = v * 10 + (encoded[i] - 48);
            i++;
        }

        cur = cur ^ v;
        out[pos] = 44;
        pos++;

        w = cur;
        if (w == 0) {
            out[pos] = 48;
            pos++;
        } else {
            m = 0;
            while (w > 0) {
                digits[m] = w % 10;
                w = w / 10;
                m++;
            }
            while (m > 0) {
                m--;
                out[pos] = digits[m] + 48;
                pos++;
            }
        }

        if (encoded[i] == 44) {
            i++;
        }
    }

    out[pos] = 0;
    return pos;
}
