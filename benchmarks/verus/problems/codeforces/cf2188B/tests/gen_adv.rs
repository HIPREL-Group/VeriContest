use vstd::prelude::*;

verus! {

pub fn generate_test_case(fillers: &Vec<i32>) -> (s: Vec<i32>)
    requires
        1 <= fillers.len() <= 200_000,
        forall|k: int| 0 <= k < fillers.len() ==> #[trigger] fillers[k] == 0 || fillers[k] == 1,
        forall|k: int| 0 <= k < fillers.len() as int - 1 ==> !(#[trigger] fillers[k] == 1 && fillers[k + 1] == 1),
    ensures
        1 <= s.len() <= 200_000,
        s.len() == fillers.len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] s[k] == 0 || s[k] == 1,
        forall|k: int| 0 <= k < s.len() as int - 1 ==> !(#[trigger] s[k] == 1 && s[k + 1] == 1),
{
    let n = fillers.len();
    let mut s: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers.len(),
            1 <= n <= 200_000,
            0 <= i <= n,
            s.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> #[trigger] fillers[k] == 0 || fillers[k] == 1,
            forall|k: int| 0 <= k < fillers.len() as int - 1 ==> !(#[trigger] fillers[k] == 1 && fillers[k + 1] == 1),
            forall|k: int| 0 <= k < i as int ==> #[trigger] s[k] == fillers[k],
        decreases n - i,
    {
        s.push(fillers[i]);
        i = i + 1;
    }
    s
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

fn build_input_multi(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{}\n", c.len()));
        for &v in c {
            s.push(if v == 1 { '1' } else { '0' });
        }
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[i64]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn solve(s: &Vec<i32>) -> i64 {
    Solution::min_total_seated_students(s)
}

fn random_valid(rng: &mut Rng, n: usize, density: u64) -> Vec<i32> {
    let mut v = vec![0; n];
    let mut i = 0;
    while i < n {
        if rng.next_u64() % density == 0 {
            v[i] = 1;
            i += 2;
        } else {
            i += 1;
        }
    }
    v
}

fn random_seed(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode {
        0 => rng.gen_range_usize(1, 5),
        1 => rng.gen_range_usize(6, 50),
        2 => rng.gen_range_usize(51, 200),
        3 => rng.gen_range_usize(201, 1000),
        4 => rng.gen_range_usize(1001, 5000),
        _ => rng.gen_range_usize(1, 100),
    };
    match mode % 4 {
        0 => random_valid(rng, n, 3),
        1 => random_valid(rng, n, 2),
        2 => random_valid(rng, n, 5),
        _ => vec![0; n],
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x2188B);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 50 { rng.gen_range_usize(1, 5) }
                       else if count < 150 { rng.gen_range_usize(2, 20) }
                       else { rng.gen_range_usize(15, 50) };
        let mut cases: Vec<Vec<i32>> = Vec::with_capacity(t);
        let mut total_n = 0usize;
        for _ in 0..t {
            let mode = rng.gen_range_usize(0, 5);
            let seed_v = random_seed(&mut rng, mode);
            // Validate preconditions
            if seed_v.len() < 1 || seed_v.len() > 200_000 { continue; }
            let mut ok = true;
            for &x in &seed_v {
                if x != 0 && x != 1 { ok = false; break; }
            }
            if !ok { continue; }
            for k in 0..seed_v.len().saturating_sub(1) {
                if seed_v[k] == 1 && seed_v[k+1] == 1 { ok = false; break; }
            }
            if !ok { continue; }
            if total_n + seed_v.len() > 200_000 { break; }
            total_n += seed_v.len();
            let v = generate_test_case(&seed_v);
            cases.push(v);
        }
        if cases.is_empty() { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
