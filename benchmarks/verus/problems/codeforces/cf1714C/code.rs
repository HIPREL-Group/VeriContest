impl Solution {
    pub fn min_varied(s: u32) -> u32 {
        let mut num: u64 = 0;
        let mut mul: u64 = 1;
        let mut rem: u32 = s;
        let mut d: u32 = 9;
        while d >= 1 {
            if d <= rem {
                let new_num: u64 = num + (d as u64) * mul;
                let new_mul: u64 = mul * 10;
                let new_rem: u32 = rem - d;
                num = new_num;
                mul = new_mul;
                rem = new_rem;
            }
            d = d - 1;
        }
        num as u32
    }
}
