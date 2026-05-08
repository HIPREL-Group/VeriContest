impl Solution {
    fn dp(l: i32, r: i32, m: i32) -> (i32, i32) {
        if l == r {
            return (1, 1);
        }
        let nxt = (m + 1) / 2;
        let mut best_min = 30i32;
        let mut best_max = 0i32;
        let mut i = 1i32;
        while i <= l {
            let j_lo_a = l - i + 1;
            let j_lo_b = l + r - m / 2 - i;
            let mut j_lo = if j_lo_a >= j_lo_b { j_lo_a } else { j_lo_b };
            if j_lo < 1 {
                j_lo = 1;
            }
            let j_hi_a = r - i;
            let j_hi_b = nxt - i;
            let j_hi = if j_hi_a <= j_hi_b { j_hi_a } else { j_hi_b };
            let mut local_min = 30i32;
            let mut local_max = 0i32;
            let mut j = j_lo;
            while j <= j_hi {
                let ii = if i <= j { i } else { j };
                let jj = if i <= j { j } else { i };
                let (sub_min, sub_max) = Self::dp(ii, jj, nxt);
                if sub_min + 1 < local_min {
                    local_min = sub_min + 1;
                }
                if sub_max + 1 > local_max {
                    local_max = sub_max + 1;
                }
                j += 1;
            }
            if local_min < best_min {
                best_min = local_min;
            }
            if local_max > best_max {
                best_max = local_max;
            }
            i += 1;
        }
        (best_min, best_max)
    }

    pub fn earliest_and_latest(n: i32, first_player: i32, second_player: i32) -> Vec<i32> {
        let l0 = first_player;
        let r0 = n - second_player + 1;
        let ll = if l0 <= r0 { l0 } else { r0 };
        let rr = if l0 <= r0 { r0 } else { l0 };
        let (e, la) = Self::dp(ll, rr, n);
        vec![e, la]
    }
}
