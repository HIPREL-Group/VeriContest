use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    home: Vec<i32>,
    away_raw: Vec<i32>,
    mutation_kind: u8,
) -> (ret: (Vec<i32>, Vec<i32>, usize))
    requires
        2 <= home.len() <= 30,
        home.len() == away_raw.len(),
        forall|i: int| 0 <= i < home.len() ==> 1 <= #[trigger] home[i] <= 100,
        forall|i: int| 0 <= i < away_raw.len() ==> 1 <= #[trigger] away_raw[i] <= 99,
    ensures
        2 <= ret.2 <= 30,
        ret.0.len() == ret.2,
        ret.1.len() == ret.2,
        forall|i: int| 0 <= i < ret.0.len() as int ==> 1 <= #[trigger] ret.0[i] <= 100,
        forall|i: int| 0 <= i < ret.1.len() as int ==> 1 <= #[trigger] ret.1[i] <= 100,
        forall|i: int| 0 <= i < ret.0.len() as int ==> ret.0[i] as int != ret.1[i] as int,
{
    let n = home.len();
    let mut away: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == home.len(),
            n == away_raw.len(),
            2 <= n <= 30,
            0 <= i <= n,
            away.len() == i,
            forall|j: int| 0 <= j < home.len() as int ==> 1 <= #[trigger] home[j] <= 100,
            forall|j: int| 0 <= j < away_raw.len() as int ==> 1 <= #[trigger] away_raw[j] <= 99,
            forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] away[j] <= 100,
            forall|j: int| 0 <= j < i as int ==> away[j] as int != home[j] as int,
        decreases n - i,
    {
        let h = home[i];
        let a = away_raw[i];
        if a >= h {
            away.push(a + 1);
        } else {
            away.push(a);
        }
        i += 1;
    }
    if mutation_kind == 1 {
        // Swap home and away for diversity
        (away, home, n)
    } else {
        (home, away, n)
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn random_team_pair(rng: &mut Rng) -> (i32, i32) {
    loop {
        let h = rng.gen_range_i64(1, 100) as i32;
        let a = rng.gen_range_i64(1, 100) as i32;
        if h != a { return (h, a); }
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(268);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // examples
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 3], vec![2, 4, 4]),
        (vec![100, 42, 5, 100], vec![42, 100, 42, 5]),
    ];
    for (h, a) in &examples {
        if count >= target { break; }
        let inp = build_input(h, a);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_host_guest_uniforms(h.clone(), a.clone(), h.len());
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = rng.gen_range_usize(2, 30);
        let mut home = Vec::with_capacity(n);
        let mut away = Vec::with_capacity(n);
        for _ in 0..n {
            let (h, a) = random_team_pair(&mut rng);
            home.push(h);
            away.push(a);
        }
        let inp = build_input(&home, &away);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::count_host_guest_uniforms(home, away, n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

