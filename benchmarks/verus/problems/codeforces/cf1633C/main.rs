use std::io::{self, Read};

struct Solution;

impl Solution {
    fn player_wins_battle(hc: i64, dc: i64, hm: i64, dm: i64) -> bool {
        let hc128 = hc as i128;
        let dc128 = dc as i128;
        let hm128 = hm as i128;
        let dm128 = dm as i128;
        let strikes = 1 + (hm128 - 1) / dc128;
        let k = strikes - 1;
        let b = k <= (hc128 - 1) / dm128;
        b
    }

    pub fn can_slay_monster(
        h_c: i64,
        d_c: i64,
        h_m: i64,
        d_m: i64,
        k: i32,
        w: i32,
        a: i64,
    ) -> bool {
        let mut found = false;
        let mut i: i32 = 0;
        while i <= k {
            let ki = (k - i) as i64;
            let hc_e = h_c + ki * a;
            let ii = i as i64;
            let dc_e = d_c + ii * (w as i64);
            let win_i = Self::player_wins_battle(hc_e, dc_e, h_m, d_m);
            if win_i {
                found = true;
            }
            i = i + 1;
        }
        found
    }
}

fn main() {
    let mut input = String::new();
    io::stdin().read_to_string(&mut input).expect("read input");
    let mut tokens = input.split_whitespace();
    if let Some(t_str) = tokens.next() {
        let t: usize = t_str.parse().expect("t");
        for _ in 0..t {
            let h_c: i64 = tokens.next().expect("h_c").parse().expect("h_c");
            let d_c: i64 = tokens.next().expect("d_c").parse().expect("d_c");
            let h_m: i64 = tokens.next().expect("h_m").parse().expect("h_m");
            let d_m: i64 = tokens.next().expect("d_m").parse().expect("d_m");
            let k: i32 = tokens.next().expect("k").parse().expect("k");
            let w: i32 = tokens.next().expect("w").parse().expect("w");
            let a: i64 = tokens.next().expect("a").parse().expect("a");
            let ans = Solution::can_slay_monster(h_c, d_c, h_m, d_m, k, w, a);
            if ans {
                println!("YES");
            } else {
                println!("NO");
            }
        }
    }
}
