use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= a.len() <= 200_000,
        forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= a.len(),
    ensures
        1 <= result.len() <= 200_000,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= result.len(),
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 1
        let mut r = a;
        r.set(0, 1);
        r
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 3 {
        // set all elements to 1 (uniform array → answer 0)
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                1 <= r.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> r[j] == 1i64,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        r
    } else if mutation_kind == 4 && a.len() >= 2 {
        // swap first two elements
        let mut r = a;
        let x = r[0];
        let y = r[1];
        r.set(0, y);
        r.set(1, x);
        r
    } else if mutation_kind == 5 {
        // set first element to a.len() (max boundary value)
        let mut r = a;
        r.set(0, r.len() as i64);
        r
    } else if mutation_kind == 6 {
        // set last element to a.len() (max boundary value)
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r.len() as i64);
        r
    } else if mutation_kind == 7 && a.len() >= 2 {
        // set first and last to same value (1) — reduces ops for value 1
        let mut r = a;
        r.set(0, 1);
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else {
        // fallback: identity
        a
    }
}

}

use std::io::Write;

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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[u64]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let cases: Vec<Vec<i64>> = vec![
            vec![1, 1, 1],
            vec![1, 2, 3, 4, 5],
            vec![1, 2, 3, 2, 1],
            vec![1, 2, 3, 1, 2, 3, 1],
            vec![2, 2, 1, 2, 3, 2, 1, 2, 3, 1, 2],
        ];
        let answers: Vec<u64> = cases.iter().map(|a| Solution::min_ops(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    // edge singles
    let edges: Vec<Vec<i64>> = vec![
        vec![1],
        vec![1, 1],
        vec![1, 2],
        vec![2, 1],
        vec![1, 2, 1],
    ];
    for e in edges {
        if count >= target { break; }
        let cases: Vec<Vec<i64>> = vec![e];
        let answers: Vec<u64> = cases.iter().map(|a| Solution::min_ops(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 1,
                1 => rng.gen_range_usize(2, 5),
                2 => rng.gen_range_usize(5, 30),
                3 => rng.gen_range_usize(30, 100),
                _ => rng.gen_range_usize(100, 500),
            };
            let mut a: Vec<i64> = Vec::with_capacity(n);
            let max_val = (n as i64).max(1);
            for _ in 0..n {
                a.push(rng.gen_range_i64(1, max_val));
            }
            cases.push(a);
        }
        let answers: Vec<u64> = cases.iter().map(|a| Solution::min_ops(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

