impl Solution {
    pub fn sort_digits(nums: Vec<u8>) -> Vec<u8> {
        let n = nums.len();
        let mut c1 = 0usize;
        let mut c2 = 0usize;
        let mut c3 = 0usize;
        let mut i = 0usize;
        while i < n {
            if nums[i] == 1 {
                c1 += 1;
            } else if nums[i] == 2 {
                c2 += 1;
            } else {
                c3 += 1;
            }
            i += 1;
        }
        let mut res = Vec::new();
        let mut j = 0usize;
        while j < c1 {
            res.push(1u8);
            j += 1;
        }
        j = 0;
        while j < c2 {
            res.push(2u8);
            j += 1;
        }
        j = 0;
        while j < c3 {
            res.push(3u8);
            j += 1;
        }
        res
    }
}
