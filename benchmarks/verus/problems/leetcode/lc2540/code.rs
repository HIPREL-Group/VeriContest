impl Solution {
    pub fn get_common(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut i: usize = 0;
        let mut j: usize = 0;

        while i < n1 && j < n2 {
            if nums1[i] == nums2[j] {
                return nums1[i];
            } else if nums1[i] < nums2[j] {
                i = i + 1;
            } else {
                j = j + 1;
            }
        }

        -1
    }
}
