use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    home_vals: Vec<i32>,
    away_raw: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= home_vals.len() <= 100_000,
        home_vals.len() == away_raw.len(),
        forall|i: int| 0 <= i < home_vals.len() ==> 1 <= #[trigger] home_vals[i] && home_vals[i] <= 100_000,
        forall|i: int| 0 <= i < away_raw.len() ==> 1 <= #[trigger] away_raw[i] && away_raw[i] <= 100_000,
    ensures
        2 <= result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] && result.0[i] <= 100_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] && result.1[i] <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] != result.1[i],
{
    let n = home_vals.len();
    // Build away vector: fix conflicts where home[i] == away_raw[i]
    let mut away: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == home_vals.len(),
            2 <= n <= 100_000,
            away_raw.len() == n,
            away.len() == idx,
            idx <= n,
            forall|i: int| 0 <= i < home_vals.len() ==> 1 <= #[trigger] home_vals[i] && home_vals[i] <= 100_000,
            forall|i: int| 0 <= i < away_raw.len() ==> 1 <= #[trigger] away_raw[i] && away_raw[i] <= 100_000,
            forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] away[j] && away[j] <= 100_000,
            forall|j: int| 0 <= j < idx as int ==> #[trigger] away[j] != home_vals[j],
        decreases n - idx,
    {
        let h = home_vals[idx];
        let a = away_raw[idx];
        if h == a {
            // Replace: shift by 1, wrapping within [1, 100_000]
            let fixed = (h % 100_000) + 1;
            assert(1 <= fixed <= 100_000);
            assert(fixed != h) by {
                // h is in [1, 100_000]
                // If h < 100_000: fixed = h + 1 != h
                // If h == 100_000: fixed = 0 + 1 = 1 != 100_000
            }
            away.push(fixed);
        } else {
            away.push(a);
        }
        idx += 1;
    }

    if mutation_kind == 0 {
        // identity
        (home_vals, away)
    } else if mutation_kind == 1 && n >= 2 {
        // swap first two elements of home
        let mut h = home_vals;
        let tmp = h[0];
        h.set(0, h[1]);
        h.set(1, tmp);
        // need to re-fix away if the swap causes conflict
        // but home swapped doesn't change away constraints since
        // away was built from original home. We need to rebuild away.
        // Actually, we need away[i] != h[i] for all i.
        // After swap: h[0] = old home[1], h[1] = old home[0]
        // away[0] was built to != old home[0], away[1] != old home[1]
        // So away[0] might == h[0] now. Fix index 0 and 1.
        let a0 = away[0];
        if a0 == h[0] {
            let fixed = (h[0] % 100_000) + 1;
            away.set(0, fixed);
        }
        let a1 = away[1];
        if a1 == h[1] {
            let fixed2 = (h[1] % 100_000) + 1;
            away.set(1, fixed2);
        }
        assert(away[0] != h[0]);
        assert(away[1] != h[1]);
        (h, away)
    } else if mutation_kind == 2 {
        // set first element of home to 1
        let mut h = home_vals;
        h.set(0, 1);
        let a0 = away[0];
        if a0 == 1 {
            away.set(0, 2);
        }
        assert(away[0] != h[0]);
        (h, away)
    } else if mutation_kind == 3 {
        // set first element of home to 100_000
        let mut h = home_vals;
        h.set(0, 100_000);
        let a0 = away[0];
        if a0 == 100_000 {
            away.set(0, 1);
        }
        assert(away[0] != h[0]);
        (h, away)
    } else if mutation_kind == 4 {
        // set all away to 1, fix conflicts
        let mut new_away: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                n == home_vals.len(),
                2 <= n <= 100_000,
                new_away.len() == k,
                k <= n,
                forall|i: int| 0 <= i < home_vals.len() ==> 1 <= #[trigger] home_vals[i] && home_vals[i] <= 100_000,
                forall|j: int| 0 <= j < k as int ==> 1 <= #[trigger] new_away[j] && new_away[j] <= 100_000,
                forall|j: int| 0 <= j < k as int ==> #[trigger] new_away[j] != home_vals[j],
            decreases n - k,
        {
            if home_vals[k] == 1 {
                new_away.push(2);
            } else {
                new_away.push(1);
            }
            k += 1;
        }
        (home_vals, new_away)
    } else if mutation_kind == 5 {
        // set all home to same value, away to different value
        let mut new_home: Vec<i32> = Vec::new();
        let mut new_away2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                n == home_vals.len(),
                2 <= n <= 100_000,
                new_home.len() == k,
                new_away2.len() == k,
                k <= n,
                forall|j: int| 0 <= j < k as int ==> #[trigger] new_home[j] == 1,
                forall|j: int| 0 <= j < k as int ==> #[trigger] new_away2[j] == 2,
            decreases n - k,
        {
            new_home.push(1);
            new_away2.push(2);
            k += 1;
        }
        (new_home, new_away2)
    } else {
        // fallback: identity
        (home_vals, away)
    }
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn build_input(home: &[i32], away: &[i32]) -> String {
    let n = home.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", home[i], away[i]));
    }
    s
}

fn build_output(gh: &[i32], ga: &[i32]) -> String {
    let mut s = String::new();
    for i in 0..gh.len() {
        s.push_str(&format!("{} {}\n", gh[i], ga[i]));
    }
    s
}

fn random_pair(rng: &mut Rng, max_color: i32) -> (i32, i32) {
    loop {
        let a = rng.gen_range_i32(1, max_color);
        let b = rng.gen_range_i32(1, max_color);
        if a != b { return (a, b); }
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |home: Vec<i32>, away: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let n = home.len();
        if !(2 <= n && n <= 100_000 && away.len() == n) { return; }
        for i in 0..n {
            if !(1 <= home[i] && home[i] <= 100_000 && 1 <= away[i] && away[i] <= 100_000 && home[i] != away[i]) { return; }
        }
        let key = format!("{:?}|{:?}", home, away);
        if !seen.insert(key) { return; }
        let inp = build_input(&home, &away);
        let (gh, ga) = Solution::football_kit_games(home.clone(), away.clone());
        let outs = build_output(&gh, &ga);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![1, 2], vec![2, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 1], vec![2, 1, 3], &mut seen, &mut out, &mut count);
    emit(vec![1, 1], vec![2, 2], &mut seen, &mut out, &mut count);
    emit(vec![100_000, 99_999], vec![1, 2], &mut seen, &mut out, &mut count);

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 5 {
            0 => 2,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(5, 30),
            3 => rng.gen_range_usize(30, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let max_color = match tries % 3 {
            0 => 5,
            1 => 20,
            _ => 100_000,
        };
        let mut home = Vec::with_capacity(n);
        let mut away = Vec::with_capacity(n);
        for _ in 0..n {
            let (a, b) = random_pair(&mut rng, max_color);
            home.push(a);
            away.push(b);
        }
        emit(home, away, &mut seen, &mut out, &mut count);
    }
}

