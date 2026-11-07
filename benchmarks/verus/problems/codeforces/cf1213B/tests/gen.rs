use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= a.len() <= 150_000,
        forall|k: int| 0 <= k < a.len() ==> 1 <= (#[trigger] a[k]) <= 1_000_000,
    ensures
        1 <= result.len() <= 150_000,
        forall|k: int| 0 <= k < result.len() ==> 1 <= (#[trigger] result[k]) <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum boundary)
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 1_000_000 (maximum boundary)
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 1_000_000);
        d
    } else if mutation_kind == 3 {
        // set all elements to the same value (no bad prices)
        let mut d = a;
        let val = d[0];
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 150_000,
                1 <= val <= 1_000_000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
                forall|j: int| i <= j < d.len() ==> 1 <= (#[trigger] d[j]) <= 1_000_000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 4 && a.len() < 150_000 {
        // grow: append element 1
        let mut d = a;
        d.push(1);
        d
    } else if mutation_kind == 5 && a.len() > 1 {
        // shrink: pop last element
        let mut d = a;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge last element up (if < 1_000_000)
        let mut d = a;
        let last = d.len() - 1;
        if d[last] < 1_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down (if > 1)
        let mut d = a;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set first element to 1_000_000 (make it likely "bad")
        let mut d = a;
        d.set(0, 1_000_000);
        d
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut d = a;
        if d.len() > 1 {
            let first = d[0];
            let last_idx = d.len() - 1;
            let last_val = d[last_idx];
            d.set(0, last_val);
            d.set(last_idx, first);
        }
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() as u64 % r) as i64) as i32
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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for case in cases {
        s.push_str(&format!("{}\n", case.len()));
        let parts: Vec<String> = case.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_array(rng: &mut Rng, len: usize, max_val: i32) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i32(1, max_val)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<Vec<i32>>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if cases.iter().any(|c| c.is_empty()) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for case in &cases {
            h ^= case.len() as u64; h = h.wrapping_mul(1099511628211);
            for &x in case { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i32> = cases.iter().map(|c| Solution::count_bad_prices(c.clone())).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Example
    let example = vec![
        vec![3,9,4,6,7,5],
        vec![1_000_000],
        vec![2,1],
        vec![31,41,59,26,53,58,97,93,23,84],
        vec![3,2,1,2,3,4,5],
    ];
    emit(example, &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![vec![1]], &mut seen, &mut out, &mut count);
    emit(vec![vec![1,2,3,4,5]], &mut seen, &mut out, &mut count);
    emit(vec![vec![5,4,3,2,1]], &mut seen, &mut out, &mut count);
    emit(vec![vec![1; 10]], &mut seen, &mut out, &mut count);
    emit(vec![vec![1_000_000; 10]], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = if tries < 5 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        for _ in 0..t {
            let n = match tries % 5 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(2, 10),
                2 => rng.gen_range_usize(5, 50),
                3 => rng.gen_range_usize(20, 200),
                _ => rng.gen_range_usize(50, 500),
            };
            let max_val = match tries % 4 {
                0 => 10i32,
                1 => 100,
                2 => 10_000,
                _ => 1_000_000,
            };
            cases.push(random_array(&mut rng, n, max_val));
        }
        emit(cases, &mut seen, &mut out, &mut count);
    }
}

