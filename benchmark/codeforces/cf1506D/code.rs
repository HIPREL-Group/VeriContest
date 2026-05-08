impl Solution {
    pub fn min_remaining_after_epic_transformation(a: Vec<i32>) -> i32 {
        let n: usize = a.len();
        let mut cnt: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k <= n {
            cnt.push(0);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let v: usize = a[i] as usize;
            cnt[v] = cnt[v] + 1;
            i = i + 1;
        }

        let mut mx: i32 = 0;
        let mut p: usize = 1;
        while p <= n {
            if cnt[p] > mx {
                mx = cnt[p];
            }
            p = p + 1;
        }

        let n_i32: i32 = n as i32;
        let two_mx: i32 = mx + mx;
        if two_mx > n_i32 {
            two_mx - n_i32
        } else {
            n_i32 % 2
        }
    }
}
