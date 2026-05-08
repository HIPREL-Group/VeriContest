impl Solution {
    fn contains_num(nums: &Vec<i32>, target: i32) -> bool {
        let n = nums.len();
        let mut i: usize = 0;
        let mut found = false;
        while i < n {
            if nums[i] == target {
                found = true;
            }
            i += 1;
        }
        found
    }

    pub fn two_out_of_three(nums1: Vec<i32>, nums2: Vec<i32>, nums3: Vec<i32>) -> Vec<i32> {
        let mut result: Vec<i32> = Vec::new();
        let mut v: i32 = 1;
        while v <= 100 {
            let in1 = Self::contains_num(&nums1, v);
            let in2 = Self::contains_num(&nums2, v);
            let in3 = Self::contains_num(&nums3, v);
            let good = (in1 && in2) || (in1 && in3) || (in2 && in3);
            if good {
                result.push(v);
            }
            v += 1;
        }
        result
    }
}
