impl Solution {
    fn can_allocate(candies: &Vec<i32>, x: i32, k: i64) -> bool {
        let mut cnt: i64 = 0;
        let mut i: usize = 0;
        while i < candies.len() {
            let add = (candies[i] as i64) / (x as i64);
            if cnt >= k - add {
                return true;
            }
            cnt = cnt + add;
            i = i + 1;
        }
        false
    }

    pub fn maximum_candies(candies: Vec<i32>, k: i64) -> i32 {
        let mut max_v: i32 = candies[0];
        let mut i: usize = 1;
        while i < candies.len() {
            if candies[i] > max_v {
                max_v = candies[i];
            }
            i = i + 1;
        }

        let mut lo: i32 = 0;
        let mut hi: i32 = max_v;
        while lo < hi {
            let mid: i32 = lo + (hi - lo + 1) / 2;
            if Self::can_allocate(&candies, mid, k) {
                lo = mid;
            } else {
                hi = mid - 1;
            }
        }
        lo
    }
}
