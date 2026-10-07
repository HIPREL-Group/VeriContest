use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let limit = 1000000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            limit == 1000000000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= limit,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > limit { limit } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= a.len() <= 100_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 1 (divisible by all d, likely NO for i=0)
        let mut v = a;
        v.set(0, 1);
        v
    } else if mutation_kind == 2 {
        // set first element to 2 (divisible by 2, the only d checked at i=0)
        let mut v = a;
        v.set(0, 2);
        v
    } else if mutation_kind == 3 {
        // set first element to 3 (not divisible by 2, always YES at i=0)
        let mut v = a;
        v.set(0, 3);
        v
    } else if mutation_kind == 4 && a.len() < 100_000 {
        // grow: append element 1
        let mut v = a;
        v.push(1);
        v
    } else if mutation_kind == 5 && a.len() > 1 {
        // shrink: remove last element
        let mut v = a;
        v.pop();
        v
    } else if mutation_kind == 6 {
        // nudge first element up (if < 1_000_000_000)
        let mut v = a;
        if v[0] < 1_000_000_000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 7 {
        // nudge first element down (if > 1)
        let mut v = a;
        if v[0] > 1 {
            v.set(0, v[0] - 1);
        }
        v
    } else if mutation_kind == 8 {
        // set all elements to 1 (all divisible by every d, answer NO for n>1)
        let mut v = a;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == a.len(),
                1 <= v.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> v[j] == 1i64,
                forall|j: int| i <= j < v.len() ==> v[j] == a[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else if mutation_kind == 9 {
        // set first element to max boundary
        let mut v = a;
        v.set(0, 1_000_000_000);
        v
    } else if mutation_kind == 10 {
        // set first element to min boundary
        let mut v = a;
        v.set(0, 1);
        v
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
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(if a { "YES\n" } else { "NO\n" }); }
    s
}

fn random_array(rng: &mut Rng, n: usize) -> Vec<i64> {
    (0..n).map(|_| rng.gen_range_i64(1, 1_000_000_000)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[Vec<i64>], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_erase_all(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<Vec<i64>> = vec![
        vec![1, 2, 3],
        vec![2],
        vec![7, 7],
        vec![384836991, 191890310, 576823355, 782177068, 404011431, 818008580, 954291757, 160449218, 155374934, 840594328],
        vec![6, 69, 696, 69696, 696969, 6969696, 69696969, 696969696],
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let arr = random_array(&mut rng, n);
            cases.push(arr);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}
