class MaxOfTwo {
    //@ requires true;
    //@ assignable \nothing;
    //@ ensures a >= b ==> \result == a;
    //@ ensures a < b ==> \result == b;
    //@ ensures \result >= a && \result >= b;
    //@ ensures \result == a || \result == b;
    public static int max_of_two(int a, int b) {
        if (a >= b) {
            return a;
        }
        return b;
    }
}
