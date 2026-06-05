#include "verification_stdlib.h"
#include "verification_list.h"
#include "int_array_def.h"

void intersperse_5(const int *numbers, int numbers_size, int delimeter,
         int *out)
/*@ With l outl
    Require 0 <= numbers_size && numbers_size < INT_MAX &&
            IntArray::full(numbers, numbers_size, l) *
        IntArray::undef_full(out, 2 * numbers_size - 1)
    Ensure IntArray::full(numbers, numbers_size, l) * 
       IntArray::full(out, 2 * numbers_size - 1 ,outl)
*/
{
    int k = 0;
    if (numbers_size == 0) {
        return;
    }

    out[k] = numbers[0];
    k = k + 1;

    int i;
    
    for (i = 1; i < numbers_size; i++) {
        out[k] = delimeter;
        k = k + 1;
        out[k] = numbers[i];
        k = k + 1;
    }

}

