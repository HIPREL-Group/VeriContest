impl Solution {
    pub fn max_dist_to_closest(seats: Vec<i32>) -> i32 {
        let n = seats.len();
        let mut i: usize = 0;
        let mut ans: i32 = 0;
        let mut have_witness = false;
        while i < n {
            if seats[i] == 1 {
                i = i + 1;
            } else {
                let start = i;
                while i < n && seats[i] == 0 {
                    i = i + 1;
                }
                let end = i;
                let len = end - start;
                let cand = if start == 0 || end == n {
                    len as i32
                } else {
                    ((len + 1) / 2) as i32
                };
                if !have_witness || cand > ans {
                    ans = cand;
                    have_witness = true;
                } else {
                    have_witness = true;
                }
            }
        }
        ans
    }
}
