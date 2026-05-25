class ArrayCountEven {
    //@ requires a != null;
    //@ requires n >= 0;
    //@ requires a.length == n;
    //@ assignable \nothing;
    //@ ensures 0 <= \result && \result <= n;
    //@ ensures \result == (\num_of int i; 0 <= i && i < n; a[i] % 2 == 0);
    public static int array_count_even(int n, int[] a) {
        int i;
        int cnt = 0;

        for (i = 0; i < n; ++i) {
            if (a[i] % 2 == 0) {
                cnt++;
            }
        }

        return cnt;
    }
}
