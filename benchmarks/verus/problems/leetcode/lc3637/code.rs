impl Solution {
    fn check_prefix_inc(nums: &Vec<i32>, p: usize) -> bool {
        let mut i: usize = 0;
        while i < p {
            if nums[i] >= nums[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    fn check_mid_dec(nums: &Vec<i32>, p: usize, q: usize) -> bool {
        let mut i: usize = p;
        while i < q {
            if nums[i] <= nums[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    fn check_suffix_inc(nums: &Vec<i32>, q: usize) -> bool {
        let n = nums.len();
        let mut i: usize = q;
        while i + 1 < n {
            if nums[i] >= nums[i + 1] {
                return false;
            }
            i += 1;
        }
        true
    }

    fn check_pq(nums: &Vec<i32>, p: usize, q: usize) -> bool {
        let a = Self::check_prefix_inc(nums, p);
        if !a {
            return false;
        }

        let b = Self::check_mid_dec(nums, p, q);
        if !b {
            return false;
        }

        let c = Self::check_suffix_inc(nums, q);
        if !c {
            return false;
        }

        true
    }

    pub fn is_trionic(nums: Vec<i32>) -> bool {
        let n = nums.len();
        if n < 4 {
            return false;
        }

        let mut p: usize = 1;
        while p + 2 < n {
            let mut q: usize = p + 1;
            while q + 1 < n {
                if Self::check_pq(&nums, p, q) {
                    return true;
                }
                q += 1;
            }
            p += 1;
        }

        false
    }
}
