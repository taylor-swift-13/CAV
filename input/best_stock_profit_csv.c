#include "../verification_stdlib.h"
#include "../verification_list.h"
#include "../char_array_def.h"

/*@ Extern Coq (best_stock_profit_csv_pre : list Z -> Prop) */
/*@ Extern Coq (best_stock_profit_csv_spec : list Z -> Z) */
/*@ Import Coq Require Import best_stock_profit_csv */

int best_stock_profit_csv(const char *prices)
/*@ With l n
    Require
      0 <= n && n < 2147483647 &&
      Zlength(l) == n &&
      (forall (k: Z), (0 <= k && k < n) => l[k] != 0) &&
      best_stock_profit_csv_pre(l) &&
      CharArray::full((char *)prices, n + 1, app(l, cons(0, nil)))
    Ensure
      __return == best_stock_profit_csv_spec(l) &&
      CharArray::full((char *)prices, n + 1, app(l, cons(0, nil)))
*/
{
    int minp = 0;
    int best = 0;
    int seen = 0;
    int i = 0;

    while (1) {
        if (prices[i] == 0) break;
        int v = 0;
        while (1) {
            if (prices[i] < 48 || prices[i] > 57) break;
            v = v * 10 + (prices[i] - 48);
            i++;
        }
        if (!seen || v < minp) minp = v;
        if (v - minp > best) best = v - minp;
        seen = 1;
        if (prices[i] == 44) i++;
    }

    return best;
}
