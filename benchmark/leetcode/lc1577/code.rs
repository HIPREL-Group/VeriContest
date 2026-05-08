impl Solution {
    pub fn num_triplets(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut count: i32 = 0;
        let mut i: usize = 0;
        while i < n1 {
            let mut j: usize = 0;
            while j < n2 {
                let mut k: usize = j + 1;
                while k < n2 {
                    if (nums1[i] as i64) * (nums1[i] as i64) == (nums2[j] as i64) * (nums2[k] as i64) {
                        count = count + 1;
                    }
                    k = k + 1;
                }
                j = j + 1;
            }
            i = i + 1;
        }
        let mut i2: usize = 0;
        while i2 < n2 {
            let mut j2: usize = 0;
            while j2 < n1 {
                let mut k2: usize = j2 + 1;
                while k2 < n1 {
                    if (nums2[i2] as i64) * (nums2[i2] as i64) == (nums1[j2] as i64) * (nums1[k2] as i64) {
                        count = count + 1;
                    }
                    k2 = k2 + 1;
                }
                j2 = j2 + 1;
            }
            i2 = i2 + 1;
        }
        count
    }
}
