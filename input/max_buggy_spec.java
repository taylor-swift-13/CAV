class MaxBuggySpec {
    //@ requires true;
    //@ assignable \nothing;
    //@ ensures a >= b ==> \result == a;
    //@ ensures a < b ==> \result == a;     // BUG: should be \result == b
    //@ ensures \result == a || \result == b;
    public static int max_buggy_spec(int a, int b) {
        if (a >= b) {
            return a;
        }
        return b;
    }
}
