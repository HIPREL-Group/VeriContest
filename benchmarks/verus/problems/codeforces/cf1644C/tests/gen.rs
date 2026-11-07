use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>, x: i64, mutation_kind: u8) -> (result: (Vec<i64>, i64))
    requires
        1 <= values.len() <= 5000,
        0 <= x <= 100000,
        forall|i: int| 0 <= i < values.len() ==> -100000 <= #[trigger] values@[i] <= 100000,
    ensures
        1 <= result.0.len() <= 5000,
        0 <= result.1 <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> -100000 <= #[trigger] result.0@[i] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        (values, x)
    } else if mutation_kind == 1 {
        // set first element to -100000 (min boundary)
        let mut v = values;
        v.set(0, -100000i64);
        (v, x)
    } else if mutation_kind == 2 {
        // set first element to 100000 (max boundary)
        let mut v = values;
        v.set(0, 100000i64);
        (v, x)
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut v = values;
        v.set(0, 0i64);
        (v, x)
    } else if mutation_kind == 4 {
        // set x to 0
        (values, 0i64)
    } else if mutation_kind == 5 {
        // set x to 100000 (max boundary)
        (values, 100000i64)
    } else if mutation_kind == 6 && values.len() < 5000 {
        // grow by one element (push 0)
        let mut v = values;
        v.push(0i64);
        (v, x)
    } else if mutation_kind == 7 && values.len() > 1 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        (v, x)
    } else if mutation_kind == 8 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        (v, x)
    } else if mutation_kind == 9 {
        // set all elements to the first element's value
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                1 <= len <= 5000,
                -100000 <= val <= 100000,
                forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == val,
                forall|j: int| i <= j && j < len ==> #[trigger] v@[j] == values@[j],
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        (v, x)
    } else if mutation_kind == 10 {
        // set last element to -100000 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, -100000i64);
        (v, x)
    } else if mutation_kind == 11 {
        // set last element to 100000 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 100000i64);
        (v, x)
    } else if mutation_kind == 12 && x > 0 {
        // nudge x down
        (values, (x - 1) as i64)
    } else if mutation_kind == 13 && x < 100000 {
        // nudge x up
        (values, (x + 1) as i64)
    } else {
        // fallback: identity
        (values, x)
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

fn build_input(cases: &[(Vec<i64>, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, x) in cases {
        s.push_str(&format!("{} {}\n", a.len(), x));
        let parts: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i64>]) -> String {
    let mut s = String::new();
    for ans in answers {
        let parts: Vec<String> = ans.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn random_array(rng: &mut Rng, n: usize) -> Vec<i64> {
    (0..n).map(|_| rng.gen_range_i64(-100, 100)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[(Vec<i64>, i64)], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<Vec<i64>> = cases.iter().map(|(a, x)| Solution::increase_subarray_sums(a.clone(), *x)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<(Vec<i64>, i64)> = vec![
        (vec![4, 1, 3, 2], 2),
        (vec![-2, -7, -1], 5),
        (vec![-6, -1, -2, 4, -6, -1, -4, 4, -5, -4], 2),
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 30);
            let x = rng.gen_range_i64(0, 100);
            let arr = random_array(&mut rng, n);
            cases.push((arr, x));
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

