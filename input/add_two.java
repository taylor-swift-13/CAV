class AddTwo {
    //@ requires Integer.MIN_VALUE <= (long)a + (long)b && (long)a + (long)b <= Integer.MAX_VALUE;
    //@ assignable \nothing;
    //@ ensures \result == a + b;
    public static int add_two(int a, int b) {
        return a + b;
    }
}
