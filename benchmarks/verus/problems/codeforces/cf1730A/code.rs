impl Solution {
    pub fn min_destroy_cost(orbits: Vec<i32>, c: i32) -> i32 {
        let n = orbits.len();
        let mut cnt: Vec<i32> = Vec::new();
        let mut t = 0usize;
        while t < 101 {
            cnt.push(0);
            t = t + 1;
        }
        let mut i = 0usize;
        while i < n {
            let x = orbits[i] as usize;
            let prev = cnt[x];
            cnt[x] = prev + 1;
            i = i + 1;
        }
        let mut ans = 0i32;
        let mut v = 1usize;
        while v <= 100 {
            let k = cnt[v];
            let add = if k < c {
                k
            } else {
                c
            };
            ans = ans + add;
            v = v + 1;
        }
        ans
    }
}
