impl Solution {
    pub fn sum_of_the_digits_of_harshad_number(x: i32) -> i32 {
        let mut s: u32 = 0;
        let mut t: u32 = x as u32;
        while t > 0 {
            let d = t % 10;
            s += d;
            t = t / 10;
        }
        if x as u32 % s == 0 {
            s as i32
        } else {
            -1
        }
    }
}
