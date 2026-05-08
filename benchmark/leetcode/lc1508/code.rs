impl Solution {
    pub fn range_sum(nums: Vec<i32>, n: i32, left: i32, right: i32) -> i32 {
        let len: usize = n as usize;
        let mut sums: Vec<i32> = Vec::new();
        let mut i: usize = 0;

        while i < len {
            let mut sum: i32 = 0;
            let mut j: usize = i;

            while j < len {
                sum = sum + nums[j];
                sums.push(sum);
                j = j + 1;
            }

            i = i + 1;
        }

        let m: usize = sums.len();

        let max_val: usize = 100001;
        let mut counts: Vec<i32> = Vec::new();
        let mut ci: usize = 0;
        while ci < max_val {
            counts.push(0i32);
            ci = ci + 1;
        }

        let mut si: usize = 0;
        while si < m {
            let v: usize = sums[si] as usize;
            counts[v] = counts[v] + 1;
            si = si + 1;
        }

        let mut sorted: Vec<i32> = Vec::new();
        let mut vi: usize = 0;

        while vi < max_val {
            let mut c: i32 = 0;
            while c < counts[vi] {
                sorted.push(vi as i32);
                c = c + 1;
            }
            vi = vi + 1;
        }

        let modv: i64 = 1_000_000_007;
        let mut result: i64 = 0;
        let mut k: usize = (left - 1) as usize;

        while k < right as usize {
            result = (result + sorted[k] as i64) % modv;
            k = k + 1;
        }

        result as i32
    }
}
