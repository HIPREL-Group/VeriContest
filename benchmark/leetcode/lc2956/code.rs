impl Solution {
    pub fn find_intersection_values(nums1: Vec<i32>, nums2: Vec<i32>) -> Vec<i32> {
        let mut c1: usize = 0;
        let mut i: usize = 0;
        while i < nums1.len() {
            let cur = nums1[i];
            let mut ok = false;
            let mut j: usize = 0;
            while j < nums2.len() {
                if cur == nums2[j] {
                    ok = true;
                    break;
                }
                j = j + 1;
            }
            if ok {
                c1 = c1 + 1;
            }
            i = i + 1;
        }

        let mut c2: usize = 0;
        i = 0;
        while i < nums2.len() {
            let cur = nums2[i];
            let mut ok = false;
            let mut j: usize = 0;
            while j < nums1.len() {
                if cur == nums1[j] {
                    ok = true;
                    break;
                }
                j = j + 1;
            }
            if ok {
                c2 = c2 + 1;
            }
            i = i + 1;
        }

        let mut out: Vec<i32> = Vec::new();
        out.push(c1 as i32);
        out.push(c2 as i32);
        out
    }
}
