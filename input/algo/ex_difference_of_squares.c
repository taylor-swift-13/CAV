int ex_difference_of_squares(int n)
/*@ Require
      0 <= n &&
      n + 1 <= 2147483647 &&
      2 * n + 1 <= 2147483647 &&
      n * (n + 1) <= 2147483647 &&
      n * (n + 1) * (2 * n + 1) <= 2147483647 &&
      (n * (n + 1) / 2) * (n * (n + 1) / 2) <= 2147483647 &&
      -2147483648 <=
        (n * (n + 1) / 2) * (n * (n + 1) / 2) -
        (n * (n + 1) * (2 * n + 1) / 6) &&
      (n * (n + 1) / 2) * (n * (n + 1) / 2) -
        (n * (n + 1) * (2 * n + 1) / 6) <= 2147483647 &&
      emp
    Ensure
      __return ==
        (n@pre * (n@pre + 1) / 2) * (n@pre * (n@pre + 1) / 2) -
        (n@pre * (n@pre + 1) * (2 * n@pre + 1) / 6) &&
      emp
*/
{
    int sum = n * (n + 1) / 2;
    int square_sum = n * (n + 1) * (2 * n + 1) / 6;
    return sum * sum - square_sum;
}
