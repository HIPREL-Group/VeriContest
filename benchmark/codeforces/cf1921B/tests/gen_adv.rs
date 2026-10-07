use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_s: Vec<u8>, seed_f: Vec<u8>) -> (result: (Vec<u8>, Vec<u8>))
    requires
        1 <= seed_s.len() <= 50,
        seed_s.len() == seed_f.len(),
        forall |i: int| 0 <= i < seed_s.len() ==> #[trigger] seed_s[i] <= 1,
        forall |i: int| 0 <= i < seed_f.len() ==> #[trigger] seed_f[i] <= 1,
    ensures
        1 <= result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= 1,
        forall |i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 1,
{
    (seed_s, seed_f)
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

fn vec_to_str(v: &Vec<u8>) -> String {
    let mut s = String::with_capacity(v.len());
    for x in v {
        if *x == 1 { s.push('1'); } else { s.push('0'); }
    }
    s
}

fn build_input(cases: &[(Vec<u8>, Vec<u8>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (sv, fv) in cases {
        s.push_str(&format!("{}\n{}\n{}\n", sv.len(), vec_to_str(sv), vec_to_str(fv)));
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn gen_seed(rng: &mut Rng, mode: usize) -> (Vec<u8>, Vec<u8>) {
    let n = match mode % 5 {
        0 => rng.gen_range_usize(1, 5),
        1 => rng.gen_range_usize(2, 10),
        2 => rng.gen_range_usize(10, 25),
        3 => rng.gen_range_usize(25, 40),
        _ => rng.gen_range_usize(40, 50),
    };
    let s: Vec<u8> = (0..n).map(|_| (rng.next_u64() & 1) as u8).collect();
    let f: Vec<u8> = match mode % 4 {
        0 => (0..n).map(|_| (rng.next_u64() & 1) as u8).collect(),
        1 => vec![0u8; n],
        2 => vec![1u8; n],
        _ => (0..n).map(|i| (i & 1) as u8).collect(),
    };
    (s, f)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1921B);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;
    let mut seen = HashSet::new();

    while count < target {
        let t: usize = if count < 20 { 1 }
                       else if count < 80 { rng.gen_range_usize(2, 6) }
                       else if count < 150 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<(Vec<u8>, Vec<u8>)> = Vec::with_capacity(t);
        for sub in 0..t {
            let mode = (count + sub) % 8;
            let (seed_s, seed_f) = gen_seed(&mut rng, mode);
            let (sv, fv) = generate_test_case(seed_s, seed_f);
            cases.push((sv, fv));
        }
        let answers: Vec<usize> = cases.iter().map(|(sv, fv)| Solution::min_days(sv.clone(), fv.clone())).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
