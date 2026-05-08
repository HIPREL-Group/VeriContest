impl Solution {
    pub fn min_ops(n: usize, k: i32, a: Vec<i32>) -> i32 {
        if k == 2 {
            let mut any_even = false;
            let mut i: usize = 0;
            while i < n {
                if a[i] % 2 == 0 {
                    any_even = true;
                }
                i += 1;
            }
            if any_even {
                0
            } else {
                1
            }
        } else if k == 3 {
            let mut best: i32 = 3;
            let mut i: usize = 0;
            while i < n {
                let x = a[i];
                let r = x % 3;
                let cost = if r == 0 { 0 } else { 3 - r };
                if cost < best {
                    best = cost;
                }
                i += 1;
            }
            best
        } else if k == 5 {
            let mut best: i32 = 5;
            let mut i: usize = 0;
            while i < n {
                let x = a[i];
                let r = x % 5;
                let cost = if r == 0 { 0 } else { 5 - r };
                if cost < best {
                    best = cost;
                }
                i += 1;
            }
            best
        } else {
            let mut cnt_even: i32 = 0;
            let mut has4 = false;
            let mut has3mod4 = false;
            let mut i: usize = 0;
            while i < n {
                let old_c = cnt_even;
                let x = a[i];
                if x % 4 == 0 {
                    has4 = true;
                }
                if x % 4 == 3 {
                    has3mod4 = true;
                }
                if x % 2 == 0 {
                    cnt_even = old_c + 1;
                }
                i += 1;
            }
            if has4 {
                0
            } else if cnt_even >= 2 {
                0
            } else if cnt_even == 1 {
                1
            } else if has3mod4 {
                1
            } else {
                2
            }
        }
    }
}
