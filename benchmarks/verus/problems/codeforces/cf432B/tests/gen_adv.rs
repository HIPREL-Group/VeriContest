use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    home_vals: &Vec<i32>,
    away_vals: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= n <= 100_000,
        home_vals.len() == n,
        away_vals.len() == n,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] home_vals[i] && home_vals[i] <= 100_000,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] away_vals[i] && away_vals[i] <= 100_000,
        forall|i: int| 0 <= i < n ==> #[trigger] home_vals[i] != away_vals[i],
    ensures
        2 <= result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] && result.0[i] <= 100_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] && result.1[i] <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] != result.1[i],
{
    let mut home: Vec<i32> = Vec::new();
    let mut away: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            2 <= n <= 100_000,
            home_vals.len() == n,
            away_vals.len() == n,
            idx <= n,
            home.len() == idx,
            away.len() == idx,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] home_vals[i] && home_vals[i] <= 100_000,
            forall|i: int| 0 <= i < n ==> 1 <= #[trigger] away_vals[i] && away_vals[i] <= 100_000,
            forall|i: int| 0 <= i < n ==> #[trigger] home_vals[i] != away_vals[i],
            forall|i: int| 0 <= i < idx ==> #[trigger] home[i] == home_vals[i],
            forall|i: int| 0 <= i < idx ==> #[trigger] away[i] == away_vals[i],
        decreases n - idx,
    {
        home.push(home_vals[idx]);
        away.push(away_vals[idx]);
        idx = idx + 1;
    }

    proof {
        assert forall|i: int| 0 <= i < home.len() implies 1 <= #[trigger] home[i] && home[i] <= 100_000 by {
            assert(home[i] == home_vals[i]);
        }
        assert forall|i: int| 0 <= i < away.len() implies 1 <= #[trigger] away[i] && away[i] <= 100_000 by {
            assert(away[i] == away_vals[i]);
        }
        assert forall|i: int| 0 <= i < home.len() implies #[trigger] home[i] != away[i] by {
            assert(home[i] == home_vals[i]);
            assert(away[i] == away_vals[i]);
        }
    }

    (home, away)
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
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let mode = tries % 8;
        let n = match mode {
            0 => 2,
            1 => 100_000,
            2 => rng.gen_range_usize(2, 10),
            3 => rng.gen_range_usize(10, 100),
            4 => rng.gen_range_usize(100, 1000),
            5 => rng.gen_range_usize(1000, 10_000),
            6 => 10000,
            _ => rng.gen_range_usize(2, 1000),
        };
        let max_color = match mode {
            0 => 100_000,
            1 => 10,
            2 => 5,
            3 => 100,
            4 => 100_000,
            5 => 100_000,
            _ => rng.gen_range_i32(2, 100_000),
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

