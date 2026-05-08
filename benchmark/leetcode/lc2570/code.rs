impl Solution {
    pub fn merge_arrays(nums1: Vec<Vec<i32>>, nums2: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        let mut out: Vec<Vec<i32>> = Vec::new();

        let mut id: i32 = 1;
        while id <= 1000 {
            let mut s: i32 = 0;
            let mut i: usize = 0;
            while i < nums1.len() {
                if nums1[i].len() == 2 && nums1[i][0] == id {
                    s = s + nums1[i][1];
                }
                i = i + 1;
            }

            let mut j: usize = 0;
            while j < nums2.len() {
                if nums2[j].len() == 2 && nums2[j][0] == id {
                    s = s + nums2[j][1];
                }
                j = j + 1;
            }

            if s > 0 {
                out.push(vec![id, s]);
            }
            id = id + 1;
        }

        out
    }
}
