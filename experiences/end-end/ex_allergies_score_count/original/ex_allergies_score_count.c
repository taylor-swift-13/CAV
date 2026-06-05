#include "../verification_stdlib.h"

/*@ Extern Coq (ex_allergies_score_count_spec : Z -> Z) */
/*@ Import Coq Require Import ex_allergies_score_count */

int ex_allergies_score_count(int score)
/*@ Require
      0 <= score &&
      score <= 2147483647 &&
      emp
    Ensure
      0 <= __return &&
      __return <= 8 &&
      __return == ex_allergies_score_count_spec(score@pre) &&
      emp
*/
{
    int count = 0;
    int i;

    for (i = 0; i < 8; i++) {
        if ((score & (1 << i)) != 0) {
            count++;
        }
    }

    return count;
}
