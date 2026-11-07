impl Solution {
    pub fn num_of_ways(n: i32) -> i32 {
        let modv: i64 = 1_000_000_007;
        let mut a121: i64 = 6;
        let mut a123: i64 = 6;
        let mut i: i32 = 1;
        while i < n {
            let new_a121 = (3 * a121 + 2 * a123) % modv;
            let new_a123 = (2 * a121 + 2 * a123) % modv;
            a121 = new_a121;
            a123 = new_a123;
            i = i + 1;
        }
        ((a121 + a123) % modv) as i32
    }
}
