class Sign {
    //@ requires true;
    //@ assignable \nothing;
    //@ ensures x > 0 ==> \result == 1;
    //@ ensures x == 0 ==> \result == 0;
    //@ ensures x < 0 ==> \result == -1;
    //@ ensures \result == -1 || \result == 0 || \result == 1;
    public static int sign(int x) {
        if (x > 0) {
            return 1;
        }
        if (x == 0) {
            return 0;
        }
        return -1;
    }
}
