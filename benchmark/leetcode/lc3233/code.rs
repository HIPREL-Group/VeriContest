impl Solution {
    pub fn non_special_count(l: i32, r: i32) -> i32 {
        let limit = (r as f64).sqrt() as i32 + 1;
        let mut is_prime = vec![true; limit as usize + 1];
        is_prime[0] = false;
        if limit >= 1 {
            is_prime[1] = false;
        }
        let mut i = 2;
        while i * i <= limit {
            if is_prime[i as usize] {
                let mut j = i * i;
                while j <= limit {
                    is_prime[j as usize] = false;
                    j += i;
                }
            }
            i += 1;
        }
        let mut special_count = 0i32;
        let mut p = 2i32;
        while p <= limit {
            if is_prime[p as usize] {
                let sq = p * p;
                if sq >= l && sq <= r {
                    special_count += 1;
                }
            }
            p += 1;
        }
        r - l + 1 - special_count
    }
}
