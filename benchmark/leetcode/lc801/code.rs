impl Solution {
    pub fn min_swap(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let n = nums1.len();
        let mut keep: i32 = 0;
        let mut swap: i32 = 1;
        let mut i: usize = 1;
        while i < n {
            let a = nums1[i];
            let b = nums2[i];
            let pa = nums1[i - 1];
            let pb = nums2[i - 1];
            let mut new_keep: i32 = i as i32 + 1;
            let mut new_swap: i32 = i as i32 + 1;
            if a > pa && b > pb {
                if keep < new_keep { new_keep = keep; }
                if swap + 1 < new_swap { new_swap = swap + 1; }
            }
            if a > pb && b > pa {
                if swap < new_keep { new_keep = swap; }
                if keep + 1 < new_swap { new_swap = keep + 1; }
            }
            keep = new_keep;
            swap = new_swap;
            i = i + 1;
        }
        if keep < swap { keep } else { swap }
    }
}
