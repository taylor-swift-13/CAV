int ex_resistor_color_duo_value(int first, int second)
/*@ Require
      0 <= first && first <= 9 &&
      0 <= second && second <= 9 &&
      emp
    Ensure
      __return == 10 * first@pre + second@pre &&
      emp
*/
{
    return first * 10 + second;
}
