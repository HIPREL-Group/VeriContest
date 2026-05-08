impl Solution {
    pub fn max_product(n: i32) -> i32 {
        let mut cur: u32 = n as u32;
        let mut max1: u32 = 0;
        let mut max2: u32 = 0;

        while cur != 0 {
            let d: u32 = cur % 10;
            if d > max1 {
                max2 = max1;
                max1 = d;
            } else if d > max2 {
                max2 = d;
            }
            cur = cur / 10;
        }

        (max1 * max2) as i32
    }
}
