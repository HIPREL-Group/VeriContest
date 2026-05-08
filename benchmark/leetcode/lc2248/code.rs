impl Solution {
    pub fn intersection(nums: Vec<Vec<i32>>) -> Vec<i32> {
        let mut out: Vec<i32> = Vec::new();
        if nums.len() == 0 {
            return out;
        }

        let mut v: i32 = 1;
        while v <= 1000 {
            let mut all = true;
            let mut q: usize = 0;
            while q < nums.len() && all {
                let row_len = nums[q].len();
                let mut found = false;
                let mut r: usize = 0;
                while r < row_len {
                    if nums[q][r] == v {
                        found = true;
                    }
                    r = r + 1;
                }
                if !found {
                    all = false;
                } else {
                    q = q + 1;
                }
            }

            if all {
                out.push(v);
            }
            v = v + 1;
        }

        out
    }
}
