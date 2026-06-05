int ex_pythagorean_triplet_product(int sum)
/*@ Require
      1 <= sum && sum <= 32768 &&
      (forall (a: Z) (b: Z) (c: Z),
        (1 <= a && a < b && b < c &&
         a + b + c == sum &&
         a * a + b * b == c * c) =>
        a * b * c <= 2147483647) &&
      emp
    Ensure
      ((exists a, exists b, exists c,
          1 <= a && a < b && b < c &&
          a + b + c == sum@pre &&
          a * a + b * b == c * c) =>
       (exists a, exists b, exists c,
          1 <= a && a < b && b < c &&
          a + b + c == sum@pre &&
          a * a + b * b == c * c &&
          (forall (a0: Z) (b0: Z) (c0: Z),
            (1 <= a0 && a0 < b0 && b0 < c0 &&
             a0 + b0 + c0 == sum@pre &&
             a0 * a0 + b0 * b0 == c0 * c0) =>
            (a < a0 || (a == a0 && b <= b0))) &&
          __return == a * b * c)) &&
      ((forall (a: Z) (b: Z) (c: Z),
          (1 <= a && a < b && b < c &&
           a + b + c == sum@pre &&
           a * a + b * b == c * c) =>
          0 == 1) =>
       __return == 0) &&
      emp
*/
{
    int a;
    int b;

    for (a = 1; a < sum; ++a) {
        for (b = a + 1; b < sum; ++b) {
            int c = sum - a - b;
            if (b < c && a * a + b * b == c * c) {
                return a * b * c;
            }
        }
    }

    return 0;
}
