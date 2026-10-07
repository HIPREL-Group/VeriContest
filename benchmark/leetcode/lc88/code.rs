impl Solution {
    pub fn merge(nums1: &mut Vec<i32>, m: i32, nums2: &mut Vec<i32>, n: i32) {
        let mm = m as usize;
        let nn = n as usize;
        let total = mm + nn;
        let mut i: usize = mm;
        let mut j: usize = nn;
        while i > 0 || j > 0 {
            let w: usize = i + j - 1;
            if j == 0 || (i > 0 && nums1[i - 1] >= nums2[j - 1]) {
                i = i - 1;
                let v = nums1[i];
                nums1[w] = v;
            } else {
                j = j - 1;
                let v = nums2[j];
                nums1[w] = v;
            }
        }
    }
}
