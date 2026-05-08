impl Solution {
    pub fn intersect(nums1: Vec<i32>, nums2: Vec<i32>) -> Vec<i32> {
        let mut freq1: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t <= 1000 {
            freq1.push(0);
            t = t + 1;
        }
        let mut i: usize = 0;
        while i < nums1.len() {
            let idx: usize = nums1[i] as usize;
            freq1[idx] = freq1[idx] + 1;
            i = i + 1;
        }

        let mut freq2: Vec<i32> = Vec::new();
        let mut t2: usize = 0;
        while t2 <= 1000 {
            freq2.push(0);
            t2 = t2 + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nums2.len() {
            let idx: usize = nums2[j] as usize;
            freq2[idx] = freq2[idx] + 1;
            j = j + 1;
        }

        let mut v: usize = 0;
        while v <= 1000 {
            let mut c: i32 = if freq1[v] < freq2[v] { freq1[v] } else { freq2[v] };
            while c > 0 {
                result.push(v as i32);
                c = c - 1;
            }
            v = v + 1;
        }
        result
    }
}
