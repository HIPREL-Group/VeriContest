use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        2 <= a.len() <= 200_000,
        forall|i: int|
            0 <= i < a.len() ==> 1 <= #[trigger] a[i] && a[i] <= 1_000_000_000,
    ensures
        2 <= result.len() <= 200_000,
        forall|i: int|
            0 <= i < result.len() ==> 1 <= #[trigger] result[i] && result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1);
        r
    } else if mutation_kind == 2 {
        // set last element to max boundary
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1_000_000_000);
        r
    } else if mutation_kind == 3 {
        // set second-to-last element to 1 (min boundary for the subtracted element)
        let mut r = a;
        let idx = r.len() - 2;
        r.set(idx, 1);
        r
    } else if mutation_kind == 4 {
        // set second-to-last element to max boundary
        let mut r = a;
        let idx = r.len() - 2;
        r.set(idx, 1_000_000_000);
        r
    } else if mutation_kind == 5 {
        // nudge last element up
        let mut r = a;
        let last = r.len() - 1;
        if r[last] < 1_000_000_000 {
            r.set(last, r[last] + 1);
        }
        r
    } else if mutation_kind == 6 {
        // nudge last element down
        let mut r = a;
        let last = r.len() - 1;
        if r[last] > 1 {
            r.set(last, r[last] - 1);
        }
        r
    } else if mutation_kind == 7 && a.len() < 200_000 {
        // grow: push element 1
        let mut r = a;
        r.push(1);
        r
    } else if mutation_kind == 8 && a.len() > 2 {
        // shrink: pop last element
        let mut r = a;
        r.pop();
        r
    } else if mutation_kind == 9 {
        // set all elements to 1
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                2 <= r.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> r[j] == 1i64,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        r
    } else if mutation_kind == 10 {
        // set all elements to max
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == a.len(),
                2 <= r.len() <= 200_000,
                forall|j: int| 0 <= j < i ==> r[j] == 1_000_000_000i64,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1_000_000_000);
            i += 1;
        }
        r
    } else {
        // fallback: identity
        a
    }
}

}

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

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<Vec<i64>> = vec![
        vec![2, 1],
        vec![2, 2, 8],
        vec![1, 2, 3, 4],
    ];
    {
        let answers: Vec<i64> = example.iter().map(|a| Solution::battle_for_survive(a.clone())).collect();
        let inp = build_input(&example);
        let outp = build_output(&answers);
        let key = format!("{:?}", example);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 20) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 50);
            let max_a = if count < 30 { 100 } else { 1_000_000_000 };
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_a)).collect();
            cases.push(a);
        }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::battle_for_survive(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

