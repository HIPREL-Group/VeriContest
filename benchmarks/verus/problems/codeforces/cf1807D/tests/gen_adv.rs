use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_a: Vec<u32>,
    raw_ls: Vec<u32>,
    raw_rs: Vec<u32>,
    raw_ks: Vec<u32>,
) -> (result: (Vec<u32>, usize, Vec<u32>, Vec<u32>, Vec<u32>, usize))
    requires
        1 <= raw_a.len() <= 200_000,
        1 <= raw_ls.len() <= 200_000,
        raw_ls.len() == raw_rs.len(),
        raw_ls.len() == raw_ks.len(),
        forall|i: int| 0 <= i < raw_a.len() ==> 1 <= #[trigger] raw_a[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < raw_ls.len() ==> 1 <= #[trigger] raw_ls[i] && raw_ls[i] as int <= raw_rs[i] as int && raw_rs[i] as int <= raw_a.len() as int,
        forall|i: int| 0 <= i < raw_rs.len() ==> 1 <= #[trigger] raw_rs[i] && raw_rs[i] as int <= raw_a.len() as int,
        forall|i: int| 0 <= i < raw_ks.len() ==> 1 <= #[trigger] raw_ks[i] <= 1_000_000_000,
    ensures
        1 <= result.1 <= 200_000,
        1 <= result.5 <= 200_000,
        result.0.len() == result.1,
        result.2.len() == result.5,
        result.3.len() == result.5,
        result.4.len() == result.5,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] && result.2[i] as int <= result.3[i] as int && result.3[i] as int <= result.1 as int,
        forall|i: int| 0 <= i < result.3.len() ==> 1 <= #[trigger] result.3[i] && result.3[i] as int <= result.1 as int,
        forall|i: int| 0 <= i < result.4.len() ==> 1 <= #[trigger] result.4[i] <= 1_000_000_000,
{
    let n = raw_a.len();
    let q = raw_ls.len();
    (raw_a, n, raw_ls, raw_rs, raw_ks, q)
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        let r = (hi as u64 - lo as u64 + 1);
        lo + (self.next_u64() % r) as u32
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

type TC = (Vec<u32>, Vec<u32>, Vec<u32>, Vec<u32>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, ls, rs, ks) in cases {
        s.push_str(&format!("{} {}\n", a.len(), ls.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
        for i in 0..ls.len() {
            s.push_str(&format!("{} {} {}\n", ls[i], rs[i], ks[i]));
        }
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (a, ls, rs, ks) in cases {
        let n = a.len();
        let q = ls.len();
        let res = Solution::odd_queries(a.clone(), n, ls.clone(), rs.clone(), ks.clone(), q);
        for v in res {
            s.push_str(if v { "YES\n" } else { "NO\n" });
        }
    }
    s
}

fn random_a(rng: &mut Rng, n: usize) -> Vec<u32> {
    (0..n).map(|_| rng.gen_range_u32(1, 1_000_000_000)).collect()
}

fn random_queries(rng: &mut Rng, q: usize, n: usize) -> (Vec<u32>, Vec<u32>, Vec<u32>) {
    let mut ls = Vec::with_capacity(q);
    let mut rs = Vec::with_capacity(q);
    let mut ks = Vec::with_capacity(q);
    for _ in 0..q {
        let l = rng.gen_range_u32(1, n as u32);
        let r = rng.gen_range_u32(l, n as u32);
        let k = rng.gen_range_u32(1, 1_000_000_000);
        ls.push(l); rs.push(r); ks.push(k);
    }
    (ls, rs, ks)
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1807D);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let t = rng.gen_range_usize(1, 4);
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let n = match tries % 4 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 20),
                2 => rng.gen_range_usize(20, 100),
                _ => rng.gen_range_usize(50, 500),
            };
            let q = match tries % 4 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 20),
                2 => rng.gen_range_usize(10, 50),
                _ => rng.gen_range_usize(20, 200),
            };
            let raw_a = random_a(&mut rng, n);
            let (raw_ls, raw_rs, raw_ks) = random_queries(&mut rng, q, n);
            let (a, _, ls, rs, ks, _) = generate_test_case(raw_a, raw_ls, raw_rs, raw_ks);
            cases.push((a, ls, rs, ks));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
