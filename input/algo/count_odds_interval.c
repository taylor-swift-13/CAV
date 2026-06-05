int count_odds_interval(int low, int high)
/*@ Require
      0 <= low &&
      low <= high &&
      emp
    Ensure
      (low@pre % 2 == 0 && high@pre % 2 == 0 =>
         __return == (high@pre - low@pre) / 2) &&
      (low@pre % 2 != 0 || high@pre % 2 != 0 =>
         __return == (high@pre - low@pre) / 2 + 1) &&
      emp
*/
{
    if (low % 2 == 0 && high % 2 == 0) {
        return (high - low) / 2;
    }

    return (high - low) / 2 + 1;
}
