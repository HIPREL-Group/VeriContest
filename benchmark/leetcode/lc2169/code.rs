impl Solution {
    pub fn count_operations(num1: i32, num2: i32) -> i32
    {
        let mut a = num1;
        let mut b = num2;
        let mut ops: i32 = 0;
        while a != 0 && b != 0
        {
            if a >= b {
                a -= b;
            } else {
                b -= a;
            }
            ops += 1;
        }
        ops
    }
}