impl Solution {
    pub fn max_distance(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut i: usize = 0;
        let mut j: usize = 0;
        let mut ans: usize = 0;
        while i < n1 && j < n2 {
            if nums1[i] <= nums2[j] {
                if j - i > ans {
                    ans = j - i;
                }
                j = j + 1;
            } else {
                i = i + 1;
                if j < i {
                    j = i;
                }
            }
        }
        ans as i32
    }
}
