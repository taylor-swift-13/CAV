class ClampNonnegative {
    //@ requires true;
    //@ assignable \nothing;
    //@ ensures \result >= 0;
    //@ ensures x >= 0 ==> \result == x;
    //@ ensures x < 0 ==> \result == 0;
    public static int clamp_nonnegative(int x) {
        if (x >= 0) {
            return x;
        }
        return 0;
    }
}
