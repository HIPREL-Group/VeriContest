use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_a: Vec<u32>,
    raw_qtypes: Vec<u32>,
    raw_qxs: Vec<u32>,
) -> (result: (Vec<u32>, usize, Vec<u32>, Vec<u32>, usize))
    requires
        1 <= raw_a.len() <= 100_000,
        1 <= raw_qtypes.len() <= 100_000,
        raw_qtypes.len() == raw_qxs.len(),
        forall|i: int| 0 <= i < raw_a.len() ==> 1 <= #[trigger] raw_a[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < raw_qtypes.len() ==> #[trigger] raw_qtypes[i] <= 1,
        forall|i: int| 0 <= i < raw_qxs.len() ==> 1 <= #[trigger] raw_qxs[i] <= 10_000,
    ensures
        1 <= result.1 <= 100_000,
        1 <= result.4 <= 100_000,
        result.0.len() == result.1,
        result.2.len() == result.4,
        result.3.len() == result.4,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.2.len() ==> #[trigger] result.2[i] <= 1,
        forall|i: int| 0 <= i < result.3.len() ==> 1 <= #[trigger] result.3[i] <= 10_000,
{
    let n = raw_a.len();
    let q = raw_qtypes.len();
    (raw_a, n, raw_qtypes, raw_qxs, q)
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

type TC = (Vec<u32>, Vec<u32>, Vec<u32>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, qt, qx) in cases {
        s.push_str(&format!("{} {}\n", a.len(), qt.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
        for i in 0..qt.len() {
            s.push_str(&format!("{} {}\n", qt[i], qx[i]));
        }
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (a, qt, qx) in cases {
        let n = a.len();
        let q = qt.len();
        let res = Solution::even_odd_sums(a.clone(), n, qt.clone(), qx.clone(), q);
        for v in res {
            s.push_str(&format!("{}\n", v));
        }
    }
    s
}

fn random_a(rng: &mut Rng, n: usize) -> Vec<u32> {
    (0..n).map(|_| rng.gen_range_u32(1, 1_000_000_000)).collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1744B);
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
            let raw_qt: Vec<u32> = (0..q).map(|_| (rng.next_u64() & 1) as u32).collect();
            let raw_qx: Vec<u32> = (0..q).map(|_| rng.gen_range_u32(1, 10_000)).collect();
            let (a, _, qt, qx, _) = generate_test_case(raw_a, raw_qt, raw_qx);
            cases.push((a, qt, qx));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outp = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
