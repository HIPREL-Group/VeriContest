impl Solution {
    pub fn min_number(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let mut min1: i32 = 10;
        let mut common_min: i32 = 10;
        let mut i: usize = 0;
        while i < nums1.len() {
            let d = nums1[i];
            if d < min1 {
                min1 = d;
            }
            let mut found = false;
            let mut j: usize = 0;
            while j < nums2.len() {
                if nums2[j] == d {
                    found = true;
                }
                j = j + 1;
            }
            if found && d < common_min {
                common_min = d;
            }
            i = i + 1;
        }

        if common_min < 10 {
            return common_min;
        }

        let mut min2: i32 = 10;
        let mut k: usize = 0;
        while k < nums2.len() {
            if nums2[k] < min2 {
                min2 = nums2[k];
            }
            k = k + 1;
        }

        if min1 < min2 {
            min1 * 10 + min2
        } else {
            min2 * 10 + min1
        }
    }
}
