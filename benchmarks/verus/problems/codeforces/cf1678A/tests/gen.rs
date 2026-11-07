use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= a.len() <= 100,
        forall|t: int|
            #![trigger a[t]]
            0 <= t < a.len() ==> 0 <= (a[t] as int) <= 100,
    ensures
        2 <= result.len() <= 100,
        forall|t: int|
            #![trigger result[t]]
            0 <= t < result.len() ==> 0 <= (result[t] as int) <= 100,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 0 (min boundary)
        let mut d = a;
        d.set(0, 0);
        d
    } else if mutation_kind == 2 {
        // set first element to 100 (max boundary)
        let mut d = a;
        d.set(0, 100);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                2 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                2 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 100i32,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 100);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && a.len() < 100 {
        // grow by one element (push 0)
        let mut d = a;
        d.push(0);
        d
    } else if mutation_kind == 6 && a.len() > 2 {
        // shrink by one element (pop)
        let mut d = a;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // nudge first element up (if < 100)
        let mut d = a;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge first element down (if > 0)
        let mut d = a;
        if d[0] > 0 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set last element to 0
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 10 {
        // set last element to 100
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 11 {
        // set first two elements equal (duplicate creation)
        let mut d = a;
        d.set(1, d[0]);
        d
    } else {
        a // fallback
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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[Vec<i32>], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_ops_to_all_zero(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],
        vec![1, 1, 2],
        vec![1, 1],
        vec![0, 0],
        vec![0, 1],
        vec![5, 5, 5],
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 30);
            let arr: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
            cases.push(arr);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

