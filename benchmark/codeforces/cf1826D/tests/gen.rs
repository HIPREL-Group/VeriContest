use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= values.len() <= 100_000,
        forall|j: int|
            #![trigger values[j]]
            0 <= j && j < values.len() ==> 1 <= values[j] as int && values[j] as int <= 100_000_000,
    ensures
        3 <= result.len() <= 100_000,
        forall|j: int|
            #![trigger result[j]]
            0 <= j && j < result.len() ==> 1 <= result[j] as int && result[j] as int <= 100_000_000,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = values;
        v.set(0, 1);
        v
    } else if mutation_kind == 2 {
        // set first element to 100_000_000 (max boundary)
        let mut v = values;
        v.set(0, 100_000_000);
        v
    } else if mutation_kind == 3 {
        // set all elements to the first element's value
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                3 <= len <= 100_000,
                1 <= val <= 100_000_000,
                forall|j: int| 0 <= j && j < i ==> #[trigger] v[j] == val,
                forall|j: int| i <= j && j < len ==> #[trigger] v[j] == values[j],
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && values.len() < 100_000 {
        // grow by one element (push 1)
        let mut v = values;
        v.push(1);
        v
    } else if mutation_kind == 5 && values.len() > 3 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        v
    } else if mutation_kind == 6 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        v
    } else if mutation_kind == 7 {
        // set last element to 1 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 8 {
        // set last element to 100_000_000 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 100_000_000);
        v
    } else if mutation_kind == 9 {
        // nudge first element up (if below max)
        let mut v = values;
        if v[0] < 100_000_000 {
            v.set(0, v[0] + 1);
        }
        v
    } else if mutation_kind == 10 {
        // nudge first element down (if above min)
        let mut v = values;
        if v[0] > 1 {
            v.set(0, v[0] - 1);
        }
        v
    } else {
        // fallback: identity
        values
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

fn random_array(rng: &mut Rng, len: usize, max_v: i32) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(1, max_v as i64) as i32).collect()
}

fn mutate(values: Vec<i32>, mk: u8) -> Vec<i32> {
    let mut v = values;
    match mk % 11 {
        0 => v,
        1 => { if !v.is_empty() { v[0] = 1; } v }
        2 => { if !v.is_empty() { v[0] = 100_000_000; } v }
        3 => { let val = if v.is_empty() {1} else {v[0]}; for i in 0..v.len() { v[i] = val; } v }
        4 => { v.push(1); v }
        5 => { if v.len() > 3 { v.pop(); } v }
        6 => { if v.len() >= 2 { v.swap(0, 1); } v }
        7 => { let n = v.len(); if n > 0 { v[n-1] = 1; } v }
        8 => { let n = v.len(); if n > 0 { v[n-1] = 100_000_000; } v }
        9 => { if !v.is_empty() && v[0] < 100_000_000 { v[0] += 1; } v }
        10 => { if !v.is_empty() && v[0] > 1 { v[0] -= 1; } v }
        _ => v,
    }
}

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for b in cases {
        s.push_str(&format!("{}\n", b.len()));
        let parts: Vec<String> = b.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1826);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let example_cases: Vec<Vec<i32>> = vec![
        vec![5, 1, 4, 2, 3],
        vec![1, 1, 1, 1],
        vec![9, 8, 7, 6, 5, 4],
        vec![100000000, 1, 100000000, 1, 100000000, 1, 100000000],
    ];
    {
        let answers: Vec<i64> = example_cases.iter().map(|b| Solution::best_running_miles(b)).collect();
        let inp = build_input(&example_cases);
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Single-case entries with hand-crafted seeds
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1, 1],
        vec![100000000, 100000000, 100000000],
        vec![1, 100000000, 1],
        vec![100000000, 1, 100000000],
        vec![50000000, 50000000, 50000000, 50000000],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
    ];
    for s in &seeds {
        for mk in 0..11u8 {
            if count >= target { break; }
            let b = mutate(s.clone(), mk);
            if b.len() < 3 { continue; }
            let cases = vec![b];
            let answers: Vec<i64> = cases.iter().map(|b| Solution::best_running_miles(b)).collect();
            let inp = build_input(&cases);
            if !seen.insert(inp.clone()) { continue; }
            let outs = build_output(&answers);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Bundled multi-test entries
    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let len = match rng.next_u64() % 5 {
                0 => rng.gen_range_usize(3, 5),
                1 => rng.gen_range_usize(3, 20),
                2 => rng.gen_range_usize(3, 100),
                3 => rng.gen_range_usize(3, 500),
                _ => rng.gen_range_usize(3, 1000),
            };
            if total_n + len > 100_000 { break; }
            total_n += len;
            let arr = random_array(&mut rng, len, 100_000_000);
            cases.push(arr);
        }
        if cases.len() < 1 { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|b| Solution::best_running_miles(b)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

