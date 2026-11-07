impl Solution {
    pub fn minimum_added_integer(nums1: Vec<i32>, nums2: Vec<i32>) -> i32 {
        let n1 = nums1.len();
        let n2 = nums2.len();
        let mut x = -1000;
        while x <= 1000 {
            let mut ok = true;
            let mut v = 0;
            let mut fail_v = -1;
            while v <= 1000 && ok {
                let mut c1 = 0;
                let mut i: usize = 0;
                while i < n1 {
                    if nums1[i] as i64 + x as i64 == v as i64 {
                        c1 += 1;
                    }
                    i += 1;
                }
                let mut c2 = 0;
                let mut j: usize = 0;
                while j < n2 {
                    if nums2[j] as i64 == v as i64 {
                        c2 += 1;
                    }
                    j += 1;
                }
                if c1 < c2 {
                    ok = false;
                    fail_v = v;
                }
                v += 1;
            }
            if ok {
                return x;
            }
            let _ = fail_v;
            x += 1;
        }
        0
    }
}
