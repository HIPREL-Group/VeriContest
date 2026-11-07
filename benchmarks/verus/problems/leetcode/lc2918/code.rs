impl Solution {
    pub fn min_sum(nums1: Vec<i32>, nums2: Vec<i32>) -> i64 {
        let mut s1: i128 = 0;
        let mut z1: i128 = 0;
        let mut i: usize = 0;
        while i < nums1.len() {
            if nums1[i] == 0 {
                s1 = s1 + 1;
                z1 = z1 + 1;
            } else {
                s1 = s1 + nums1[i] as i128;
            }
            i = i + 1;
        }

        let mut s2: i128 = 0;
        let mut z2: i128 = 0;
        let mut j: usize = 0;
        while j < nums2.len() {
            if nums2[j] == 0 {
                s2 = s2 + 1;
                z2 = z2 + 1;
            } else {
                s2 = s2 + nums2[j] as i128;
            }
            j = j + 1;
        }

        if s1 < s2 && z1 == 0 {
            -1
        } else if s2 < s1 && z2 == 0 {
            -1
        } else if s1 >= s2 {
            s1 as i64
        } else {
            s2 as i64
        }
    }
}
