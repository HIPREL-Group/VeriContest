use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_a: Vec<i64>, seed_k: i64) -> (result: (Vec<i64>, i64))
    requires
        1 <= seed_a.len() <= 200_000,
        0 <= seed_k <= 1_000_000_000_000_000,
        forall |j: int| 0 <= j < seed_a.len() ==> 1 <= #[trigger] seed_a[j] <= 1_000_000_000,
        forall |x: int, y: int| 0 <= x <= y < seed_a.len() ==> seed_a[x] >= seed_a[y],
    ensures
        1 <= result.0.len() <= 200_000,
        0 <= result.1 <= 1_000_000_000_000_000,
        forall |j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 1_000_000_000,
        forall |x: int, y: int| 0 <= x <= y < result.0.len() ==> result.0[x] >= result.0[y],
{
    (seed_a, seed_k)
}

} // verus!

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn build_input(cases: &[(Vec<i64>, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, k) in cases {
        s.push_str(&format!("{} {}\n", a.len(), k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn rand_arr_sorted_desc(rng: &mut Rng, n: usize, lo: i64, hi: i64) -> Vec<i64> {
    let mut a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(lo, hi)).collect();
    a.sort_unstable_by(|x, y| y.cmp(x));
    a
}

fn gen_case(rng: &mut Rng, mode: usize) -> (Vec<i64>, i64) {
    match mode {
        0 => {
            let n = rng.gen_range_usize(2, 5);
            (rand_arr_sorted_desc(rng, n, 1, 100), 0)
        }
        1 => {
            let n = rng.gen_range_usize(50, 200);
            (rand_arr_sorted_desc(rng, n, 1, 1_000_000_000), rng.gen_range_i64(0, 1_000_000_000))
        }
        2 => {
            let n = (rng.gen_range_usize(1, 20)) * 2;
            (rand_arr_sorted_desc(rng, n, 1, 1000), rng.gen_range_i64(0, 1000))
        }
        3 => {
            let n = rng.gen_range_usize(1, 20) * 2 + 1;
            (rand_arr_sorted_desc(rng, n, 1, 1000), rng.gen_range_i64(0, 1000))
        }
        4 => {
            let n = rng.gen_range_usize(2, 20);
            let v = rng.gen_range_i64(1, 1000);
            (vec![v; n], rng.gen_range_i64(0, 100))
        }
        5 => {
            let n = rng.gen_range_usize(2, 30);
            (rand_arr_sorted_desc(rng, n, 1, 1000), 1_000_000_000)
        }
        6 => {
            let n = rng.gen_range_usize(2, 20);
            (rand_arr_sorted_desc(rng, n, 1, 1000), rng.gen_range_i64(0, 100))
        }
        7 => {
            let n = rng.gen_range_usize(2, 20);
            (rand_arr_sorted_desc(rng, n, 1, 1000), rng.gen_range_i64(0, 100))
        }
        _ => {
            let n = rng.gen_range_usize(2, 50);
            (rand_arr_sorted_desc(rng, n, 1, 1000), rng.gen_range_i64(0, 1000))
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let modes = 9usize;
    let mut attempts = 0usize;

    while count < target && attempts < target * 10 {
        attempts += 1;
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };

        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        let mut total_n = 0usize;
        for sub in 0..t {
            let mode = (count * 7 + sub) % modes;
            let (seed_a, seed_k) = gen_case(&mut rng, mode);
            if total_n + seed_a.len() > 5000 { break; }
            total_n += seed_a.len();
            // The seed is already valid; pass through the verified function
            let (a, k) = generate_test_case(seed_a, seed_k);
            cases.push((a, k));
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<u64> = cases.iter().map(|(a, k)| Solution::optimal_score(a.clone(), *k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
