use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        2 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    let n = if values.len() < 2 { 2usize }
            else if values.len() > 50 { 50usize } else { values.len() };
    let limit = 1000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 50,
            limit == 1000,
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
        1 <= a.len() <= 50,
        forall|k: int| 0 <= k < a.len() as int ==> 1 <= #[trigger] a[k] as int <= 1000,
    ensures
        1 <= result.len() <= 50,
        forall|k: int| 0 <= k < result.len() as int ==> 1 <= #[trigger] result[k] as int <= 1000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set all elements to the same even value
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 2i64,
                forall|j: int| i <= j < d.len() as int ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 2 {
        // set all elements to the same odd value
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 1i64,
                forall|j: int| i <= j < d.len() as int ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 3 {
        // set even-indexed elements to one parity, odd-indexed to another (mixed)
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> (
                    if j % 2 == 0 { d[j] == 2i64 } else { d[j] == 3i64 }
                ),
                forall|j: int| i <= j < d.len() as int ==> d[j] == a[j],
            decreases d.len() - i,
        {
            if i % 2 == 0 {
                d.set(i, 2);
            } else {
                d.set(i, 3);
            }
            i += 1;
        }
        d
    } else if mutation_kind == 4 && a.len() < 50 {
        // grow by one element
        let mut d = a;
        d.push(1);
        d
    } else if mutation_kind == 5 && a.len() > 1 {
        // shrink by one element
        let mut d = a;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first element up (if < 1000)
        let mut d = a;
        if d[0] < 1000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge first element down (if > 1)
        let mut d = a;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set first element to boundary 1
        let mut d = a;
        d.set(0, 1);
        d
    } else if mutation_kind == 9 {
        // set first element to boundary 1000
        let mut d = a;
        d.set(0, 1000);
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
        let answers: Vec<bool> = cases.iter().map(|a| Solution::can_make_same_parity(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<Vec<i64>> = vec![
        vec![1, 2, 3, 4],
        vec![1, 1],
        vec![1],
        vec![1, 2],
        vec![2, 4, 6],
        vec![1, 3, 5],
        vec![1, 2, 3],
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 20);
            let arr: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1000)).collect();
            cases.push(arr);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}
