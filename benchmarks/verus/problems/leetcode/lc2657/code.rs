impl Solution {
    pub fn find_the_prefix_common_array(a: Vec<i32>, b: Vec<i32>) -> Vec<i32> {
        let n = a.len();
        let mut pos: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            pos.push(-1);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let val = b[i];
            pos[val as usize] = i as i32;
            i = i + 1;
        }

        let mut result: Vec<i32> = Vec::new();
        i = 0;
        while i < n {
            let mut common: i32 = 0;
            let mut p: usize = 0;
            while p <= i {
                let x = a[p];
                let idx = pos[x as usize];
                if idx >= 0 && idx <= i as i32 {
                    common = common + 1;
                }
                p = p + 1;
            }
            result.push(common);
            i = i + 1;
        }

        result
    }
}
