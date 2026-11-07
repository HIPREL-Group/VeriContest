impl Solution {
    pub fn book_reading_digit_sum(n: u64, m: u64) -> u64 {
        let t = n / m;
        let m10 = m % 10;
        let mut cycle_sum: u64 = 0;
        let mut i: u64 = 1;
        while i <= 10 {
            let imod32 = (i % 10) as u32;
            let m1032 = m10 as u32;
            let d = ((imod32 * m1032) % 10) as u64;
            cycle_sum = cycle_sum + d;
            i = i + 1;
        }
        let full = t / 10;
        let rem = t % 10;
        let mut partial: u64 = 0;
        i = 1;
        while i <= rem {
            let imod32 = (i % 10) as u32;
            let m1032 = m10 as u32;
            let d = ((imod32 * m1032) % 10) as u64;
            partial = partial + d;
            i = i + 1;
        }
        let res = full * cycle_sum + partial;
        res
    }
}
