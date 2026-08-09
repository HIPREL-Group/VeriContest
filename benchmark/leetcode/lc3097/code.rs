fn bit_set_exec(x: i32, b: u32) -> bool {
    (x >> b) & 1 == 1
}

impl Solution {
    pub fn minimum_subarray_length(nums: Vec<i32>, k: i32) -> i32 {
        let n = nums.len();

        let mut cnt: Vec<i32> = Vec::new();
        let mut bi: usize = 0;
        while bi < 30 {
            cnt.push(0);
            bi += 1;
        }

        let mut l: usize = 0;
        let mut r: usize = 0;
        let mut window_or: i32 = 0;
        let mut best: i32 = (n as i32) + 1;

        while l < n {
            while r < n && !(r > l && window_or >= k) {
                let old_r = r;
                let x = nums[r];
                let mut b: usize = 0;
                while b < 30 {
                    let bit_here = bit_set_exec(x, b as u32);
                    if bit_here {
                        cnt[b] = cnt[b] + 1;
                    }
                    b += 1;
                }
                window_or = window_or | x;
                r += 1;
            }

            let old_best = best;
            if window_or >= k {
                let candidate: i32 = (r - l) as i32;
                if candidate < best {
                    best = candidate;
                } else {
                    best = old_best;
                }
            } else {
                best = old_best;
            }

            let removed = nums[l];
            let old_l = l;
            let mut b2: usize = 0;
            while b2 < 30 {
                let bit_here = bit_set_exec(removed, b2 as u32);
                if bit_here {
                    cnt[b2] = cnt[b2] - 1;
                }
                b2 += 1;
            }

            let mut new_or: i32 = 0;
            let mut b3: usize = 0;
            while b3 < 30 {
                if cnt[b3] > 0 {
                    new_or = new_or | (1i32 << (b3 as u32));
                }
                b3 += 1;
            }
            window_or = new_or;
            l += 1;
        }

        if best <= n as i32 {
            best
        } else {
            -1
        }
    }
}
