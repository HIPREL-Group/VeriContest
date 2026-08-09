impl Solution {
    pub fn sum_of_floored_pairs(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        let modulo: i64 = 1_000_000_007;

        let mut count: Vec<i64> = Vec::new();
        let mut vi: usize = 0;
        while vi <= 100_000 {
            count.push(0);
            vi = vi + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = nums[i] as usize;
            count[val] = count[val] + 1;
            i = i + 1;
        }

        let mut prefix: Vec<i64> = Vec::new();
        prefix.push(count[0]);
        let mut v1: usize = 1;
        while v1 <= 100_000 {
            let next = prefix[v1 - 1] + count[v1];
            prefix.push(next);
            v1 = v1 + 1;
        }

        let mut gval: Vec<i64> = Vec::new();
        gval.push(0);
        let mut v2: usize = 1;
        while v2 <= 100_000 {
            let kmax_bound: usize = 100_000 / v2;
            let mut g: i64 = 0;
            let mut k: usize = 1;
            while k <= kmax_bound {
                let lo = k * v2;
                let k1 = k + 1;
                let hi_raw = k1 * v2 - 1;
                let hi: usize = if hi_raw > 100_000 { 100_000 } else { hi_raw };
                let range_count = prefix[hi] - prefix[lo - 1];
                g = g + (k as i64) * range_count;
                k = k + 1;
            }
            gval.push(g);
            v2 = v2 + 1;
        }

        let mut total: i64 = 0;
        let mut j: usize = 0;
        while j < n {
            let val = nums[j] as usize;
            total = (total + gval[val]) % modulo;
            j = j + 1;
        }
        (total % modulo) as i32
    }
}
