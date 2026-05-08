impl Solution {
    fn min_for_mask(m: &Vec<i32>, s: &Vec<i32>, target: i32) -> (i32, bool) {
        let inf: i32 = 1_000_000_000;
        let n = m.len();
        let mut best = inf;
        let mut seen = false;

        let mut i: usize = 0;
        while i < n {
            if s[i] == target {
                if !seen {
                    seen = true;
                    best = m[i];
                } else if m[i] < best {
                    best = m[i];
                }
            }
            i = i + 1;
        }

        (best, seen)
    }

    pub fn min_minutes(m: Vec<i32>, s: Vec<i32>) -> i32 {
        let inf: i32 = 1_000_000_000;
        let n = m.len();

        let r11 = Solution::min_for_mask(&m, &s, 3);
        let r10 = Solution::min_for_mask(&m, &s, 2);
        let r01 = Solution::min_for_mask(&m, &s, 1);

        let best11 = r11.0;
        let seen11 = r11.1;
        let best10 = r10.0;
        let seen10 = r10.1;
        let best01 = r01.0;
        let seen01 = r01.1;

        let cand11 = if seen11 { best11 } else { inf };
        let candpair = if best10 < inf && best01 < inf {
            best10 + best01
        } else {
            inf
        };
        let ans = if cand11 < candpair { cand11 } else { candpair };

        if ans >= inf {
            -1
        } else {
            ans
        }
    }
}
