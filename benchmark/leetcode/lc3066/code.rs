impl Solution {
    pub fn min_operations(nums: Vec<i32>, k: i32) -> i32 {
        let mut h: Vec<i64> = Vec::new();
        let mut t: usize = 0;
        while t < nums.len() {
            let v = nums[t];
            let vi = v as i64;
            let mut p: usize = 0;
            while p < h.len() && h[p] > vi {
                p += 1;
            }
            h.insert(p, vi);
            t += 1;
        }
        let mut ops: i32 = 0;
        while h.len() >= 2 && h[h.len() - 1] < k as i64 {
            let nh = h.len();
            let x = h[nh - 1];
            let y = h[nh - 2];
            let merged = 2 * x + y;
            let _ = h.pop();
            let _ = h.pop();
            let mut p: usize = 0;
            while p < h.len() && h[p] > merged {
                p += 1;
            }
            h.insert(p, merged);
            ops = ops + 1;
        }
        ops
    }
}
