#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

/*@ Extern Coq (intersperse_list: list Z -> Z -> list Z) */
/*@ Import Coq Require Import p005_intersperse */

void p005_intersperse(const int *numbers, int numbers_size, int delimeter,
         int *out)
/*@ With l
    Require 0 < numbers_size && 2 * numbers_size - 1 < INT_MAX &&
            Zlength(l) == numbers_size &&
            IntArray::full(numbers, numbers_size, l) *
            IntArray::undef_full(out, 2 * numbers_size - 1)
    Ensure exists outl,
            Zlength(outl) == 2 * numbers_size - 1 &&
            IntArray::full(numbers, numbers_size, l) *
            IntArray::full(out, 2 * numbers_size - 1, outl)
*/
{
    int k = 0;
    if (numbers_size == 0) {
        return;
    }

    out[k] = numbers[0];
    k = k + 1;

    int i;
    /*@ Inv Assert
        numbers == numbers@pre &&
        numbers_size == numbers_size@pre &&
        delimeter == delimeter@pre &&
        out == out@pre &&
        0 < numbers_size@pre &&
        2 * numbers_size@pre - 1 < INT_MAX &&
        Zlength(l) == numbers_size@pre &&
        1 <= i && i <= numbers_size@pre &&
        k == 2 * i - 1 &&
        IntArray::full(numbers@pre, numbers_size@pre, l) *
        IntArray::seg(out@pre, 0, k, intersperse_list(sublist(0, i, l), delimeter@pre)) *
        IntArray::undef_seg(out@pre, k, 2 * numbers_size@pre - 1)
    */
    for (i = 1; i < numbers_size; i++) {
        out[k] = delimeter;
        k = k + 1;
        out[k] = numbers[i];
        k = k + 1;
    }

}
