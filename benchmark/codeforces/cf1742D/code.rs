impl Solution {
    pub fn is_coprime_values(x: i32, y: i32) -> bool {
        let mut a = x;
        let mut b = y;
        while b != 0 {
            let r = a % b;
            a = b;
            b = r;
        }
        a == 1
    }

    pub fn max_coprime_index_sum(a: Vec<i32>) -> i32 {
        let n = a.len();
        let mut last: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < 1001 {
            last.push(-1);
            k = k + 1;
        }

        let mut i: usize = 0;
        while i < n {
            let v = a[i] as usize;
            last[v] = i as i32 + 1;
            i = i + 1;
        }

        let mut ans: i32 = -1;
        let mut x: i32 = 1;
        while x <= 1000 {
            let mut y: i32 = 1;
            while y <= 1000 {
                let cop = Self::is_coprime_values(x, y);
                let lx = last[x as usize];
                let ly = last[y as usize];
                if lx != -1 && ly != -1 && cop {
                    let cand = lx + ly;
                    if cand > ans {
                        ans = cand;
                    }
                }
                y = y + 1;
            }
            x = x + 1;
        }

        ans
    }
}
