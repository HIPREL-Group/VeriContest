use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fillers_a: &Vec<u32>,
    fillers_b: &Vec<u32>,
    forced_small_idx: usize,
) -> (result: (Vec<u32>, Vec<u32>, usize))
    requires
        1 <= n <= 50,
        fillers_a.len() == n,
        fillers_b.len() == n,
        forall|i: int| 0 <= i < fillers_a.len() ==> 1 <= #[trigger] fillers_a[i] <= 50,
        forall|i: int| 0 <= i < fillers_b.len() ==> 1 <= #[trigger] fillers_b[i] <= 50,
        0 <= forced_small_idx < n,
    ensures
        1 <= result.2 <= 50,
        result.0.len() == result.2,
        result.1.len() == result.2,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 50,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 50,
        result.0[forced_small_idx as int] <= 10,
        exists|i: int| 0 <= i < result.0.len() && #[trigger] result.0[i] <= 10,
{
    let mut a: Vec<u32> = Vec::new();
    let mut b: Vec<u32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == fillers_a.len(),
            n == fillers_b.len(),
            1 <= n <= 50,
            0 <= i <= n,
            a.len() == i,
            b.len() == i,
            forall|j: int| 0 <= j < fillers_a.len() ==> 1 <= #[trigger] fillers_a[j] <= 50,
            forall|j: int| 0 <= j < fillers_b.len() ==> 1 <= #[trigger] fillers_b[j] <= 50,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 50,
            forall|j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 50,
            forced_small_idx < n,
            i > forced_small_idx ==> a[forced_small_idx as int] <= 10,
        decreases n - i,
    {
        if i == forced_small_idx {
            // ensure a[i] <= 10
            if fillers_a[i] <= 10 {
                a.push(fillers_a[i]);
            } else {
                a.push(5u32);
            }
        } else {
            a.push(fillers_a[i]);
        }
        b.push(fillers_b[i]);
        i = i + 1;
    }
    proof {
        assert(a[forced_small_idx as int] <= 10);
        assert(0 <= forced_small_idx < a.len());
        assert(exists|i: int| 0 <= i < a.len() && #[trigger] a[i] <= 10) by {
            assert(a[forced_small_idx as int] <= 10);
        }
    }
    (a, b, n)
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
        lo + (self.next_u64() as u32) % (hi - lo + 1)
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

fn build_input(cases: &[(Vec<u32>, Vec<u32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, b) in cases {
        s.push_str(&format!("{}\n", a.len()));
        for i in 0..a.len() {
            s.push_str(&format!("{} {}\n", a[i], b[i]));
        }
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(0x1850B);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let t = rng.gen_range_usize(1, 5);
        let mut cases: Vec<(Vec<u32>, Vec<u32>)> = Vec::new();
        for _ in 0..t {
            let n = match tries % 4 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(2, 10),
                2 => rng.gen_range_usize(10, 30),
                _ => rng.gen_range_usize(20, 50),
            };
            let mut fa: Vec<u32> = Vec::with_capacity(n);
            let mut fb: Vec<u32> = Vec::with_capacity(n);
            let mut b_used: HashSet<u32> = HashSet::new();
            for _ in 0..n {
                fa.push(rng.gen_range_u32(1, 50));
                let mut bv = rng.gen_range_u32(1, 50);
                while b_used.contains(&bv) {
                    bv = rng.gen_range_u32(1, 50);
                }
                b_used.insert(bv);
                fb.push(bv);
            }
            let forced = rng.gen_range_usize(0, n - 1);
            let (a, b, _) = generate_test_case(n, &fa, &fb, forced);
            cases.push((a, b));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let mut answers: Vec<usize> = Vec::new();
        for (a, b) in &cases {
            let nlen = a.len();
            answers.push(Solution::find_winner(a.clone(), b.clone(), nlen));
        }
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
