impl Solution {
    pub fn added_integer(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let n = nums1.len();
        let mut min1 = nums1[0];
        let mut min2 = nums2[0];
        let mut i = 1;
        while i < n {
            if nums1[i] < min1 {
                min1 = nums1[i];
            }
            if nums2[i] < min2 {
                min2 = nums2[i];
            }
            i += 1;
        }
        min2 - min1
    }
}
