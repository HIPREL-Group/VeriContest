impl Solution {
    pub fn number_of_pairs(nums1: Vec<i32>, nums2: Vec<i32>, k: i32) -> i32 {
        let mut count: i32 = 0;
        let n = nums1.len();
        let m = nums2.len();
        for i in 0..n {
            let mut inner: i32 = 0;
            for j in 0..m {
                if nums1[i] % (nums2[j] * k) == 0 {
                    inner += 1;
                }
            }
            count += inner;
        }
        count
    }
}
