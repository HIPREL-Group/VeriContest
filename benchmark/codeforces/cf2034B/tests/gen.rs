use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s: Vec<i32>,
    m: usize,
    k: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, usize, usize))
    requires
        1 <= s.len() <= 200_000,
        1 <= m <= s.len(),
        1 <= k <= s.len(),
        forall|t: int| 0 <= t < s.len() as int ==> s[t] == 0 || s[t] == 1,
    ensures
        1 <= result.0.len() <= 200_000,
        1 <= (result.1 as int) <= result.0.len() as int,
        1 <= (result.2 as int) <= result.0.len() as int,
        forall|t: int| 0 <= t < result.0.len() as int ==> #[trigger] result.0[t] == 0 || result.0[t] == 1,
{
    if mutation_kind == 0 {
        // identity
        (s, m, k)
    } else if mutation_kind == 1 {
        // all zeros
        let mut rs = s;
        let mut i: usize = 0;
        while i < rs.len()
            invariant
                i <= rs.len(),
                rs.len() == s.len(),
                1 <= rs.len() <= 200_000,
                forall|j: int| 0 <= j < i as int ==> rs[j] == 0i32,
                forall|j: int| i as int <= j < rs.len() as int ==> rs[j] == s[j],
            decreases rs.len() - i,
        {
            rs.set(i, 0);
            i += 1;
        }
        (rs, m, k)
    } else if mutation_kind == 2 {
        // all ones
        let mut rs = s;
        let mut i: usize = 0;
        while i < rs.len()
            invariant
                i <= rs.len(),
                rs.len() == s.len(),
                1 <= rs.len() <= 200_000,
                forall|j: int| 0 <= j < i as int ==> rs[j] == 1i32,
                forall|j: int| i as int <= j < rs.len() as int ==> rs[j] == s[j],
            decreases rs.len() - i,
        {
            rs.set(i, 1);
            i += 1;
        }
        (rs, m, k)
    } else if mutation_kind == 3 {
        // flip first element
        let mut rs = s;
        if rs[0] == 0 {
            rs.set(0, 1);
        } else {
            rs.set(0, 0);
        }
        (rs, m, k)
    } else if mutation_kind == 4 {
        // flip last element
        let mut rs = s;
        let last = rs.len() - 1;
        if rs[last] == 0 {
            rs.set(last, 1);
        } else {
            rs.set(last, 0);
        }
        (rs, m, k)
    } else if mutation_kind == 5 {
        // m = 1
        (s, 1usize, k)
    } else if mutation_kind == 6 {
        // k = 1
        (s, m, 1usize)
    } else if mutation_kind == 7 {
        // m = n
        let n = s.len();
        (s, n, k)
    } else if mutation_kind == 8 {
        // k = n
        let n = s.len();
        (s, m, n)
    } else if mutation_kind == 9 && s.len() < 200_000 {
        // grow by pushing 0
        let mut rs = s;
        rs.push(0);
        (rs, m, k)
    } else if mutation_kind == 10 && s.len() > 1 && m < s.len() && k < s.len() {
        // shrink by popping
        let mut rs = s;
        rs.pop();
        (rs, m, k)
    } else {
        // fallback: identity
        (s, m, k)
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

fn build_input(cases: &[(Vec<i32>, usize, usize)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, m, k) in cases {
        let n = a.len();
        s.push_str(&format!("{} {} {}\n", n, m, k));
        let mut row = String::with_capacity(n);
        for &v in a {
            row.push(if v == 1 { '1' } else { '0' });
        }
        row.push('\n');
        s.push_str(&row);
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

fn make_string(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    match mode {
        0 => vec![0i32; n],
        1 => vec![1i32; n],
        2 => (0..n).map(|i| if i % 2 == 0 { 0 } else { 1 }).collect(),
        3 => (0..n).map(|i| if i % 2 == 0 { 1 } else { 0 }).collect(),
        _ => (0..n).map(|_| if rng.next_u64() % 2 == 0 { 0 } else { 1 }).collect(),
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<(Vec<i32>, usize, usize)> = vec![
        (vec![1,0,1,0,1], 1, 1),
        (vec![1,1,0,1,0], 2, 5),
        (vec![0,0,0,0,0,0], 3, 2),
    ];
    {
        let answers: Vec<i64> = example.iter().map(|(s, m, k)| Solution::min_timar_operations(s.clone(), *m, *k)).collect();
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
        let mut cases: Vec<(Vec<i32>, usize, usize)> = Vec::new();
        let mut total = 0usize;
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let m = rng.gen_range_usize(1, n);
            let k = rng.gen_range_usize(1, n);
            let mode = rng.gen_range_usize(0, 5);
            let s = make_string(&mut rng, n, mode);
            if total + n > 5000 { break; }
            total += n;
            cases.push((s, m, k));
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i64> = cases.iter().map(|(s, m, k)| Solution::min_timar_operations(s.clone(), *m, *k)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

