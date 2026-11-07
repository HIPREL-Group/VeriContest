use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        1 <= result.len() <= 200000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= result.len() as int,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 200000 { 200000usize } else { values.len() };
    let limit = n as i64;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000,
            limit == n as i64,
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


pub fn generate_candidate(values: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= values.len() <= 200000,
    ensures
        1 <= result.len() <= 200000,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set first element to value of last (same borders → triggers combined run)
        let last_val = values[values.len() - 1];
        let mut v = values;
        v.set(0, last_val);
        v
    } else if mutation_kind == 2 {
        // set last element to value of first (same borders)
        let first_val = values[0];
        let mut v = values;
        let idx = v.len() - 1;
        v.set(idx, first_val);
        v
    } else if mutation_kind == 3 {
        // set all elements to the first element's value (answer = 0)
        let val = values[0];
        let len = values.len();
        let mut v = values;
        let mut i: usize = 1;
        while i < len
            invariant
                1 <= i <= len,
                v.len() == len,
                1 <= len <= 200000,
                forall|j: int| 0 <= j && j < i ==> #[trigger] v@[j] == val,
            decreases len - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && values.len() < 200000 {
        // grow by one element (push copy of first)
        let first_val = values[0];
        let mut v = values;
        v.push(first_val);
        v
    } else if mutation_kind == 5 && values.len() > 1 {
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
        // set first element to 0
        let mut v = values;
        v.set(0, 0);
        v
    } else if mutation_kind == 8 {
        // set last element to 0
        let mut v = values;
        let idx = v.len() - 1;
        v.set(idx, 0);
        v
    } else if mutation_kind == 9 && values.len() >= 2 {
        // set first and last to the same value (triggers combined run path)
        let first_val = values[0];
        let mut v = values;
        let idx = v.len() - 1;
        v.set(idx, first_val);
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
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_input_multi(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[i64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    let mut arr = Vec::with_capacity(len);
    let mv = if max_val < 1 { 1 } else { max_val };
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, mv));
    }
    arr
}

fn make_array(rng: &mut Rng, mode: usize) -> Vec<i64> {
    match mode {
        0 => {
            // all equal
            let n = rng.gen_range_usize(1, 50);
            let x = rng.gen_range_i64(1, n.max(1) as i64);
            vec![x; n]
        }
        1 => {
            // single element
            vec![rng.gen_range_i64(1, 10)]
        }
        2 => {
            // first==last, middle varies
            let n = rng.gen_range_usize(3, 100);
            let x = rng.gen_range_i64(1, n as i64);
            let mut v = Vec::with_capacity(n);
            v.push(x);
            for _ in 1..n-1 {
                v.push(rng.gen_range_i64(1, n as i64));
            }
            v.push(x);
            v
        }
        3 => {
            // long left prefix equal
            let n = rng.gen_range_usize(2, 100);
            let x = rng.gen_range_i64(1, n as i64);
            let k = rng.gen_range_usize(1, n - 1);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i < k { v.push(x); } else { v.push(rng.gen_range_i64(1, n as i64)); }
            }
            v
        }
        4 => {
            // long right suffix equal
            let n = rng.gen_range_usize(2, 100);
            let x = rng.gen_range_i64(1, n as i64);
            let k = rng.gen_range_usize(1, n - 1);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i >= k { v.push(x); } else { v.push(rng.gen_range_i64(1, n as i64)); }
            }
            v
        }
        _ => {
            // pure random
            let n = rng.gen_range_usize(1, 100);
            random_array(rng, n, n.max(1) as i64)
        }
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1931);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // examples first (each as t=1)
    let examples: Vec<Vec<i64>> = vec![
        vec![1, 2, 3, 4, 5, 1],
        vec![1, 1, 1, 1, 1, 1],
        vec![2],
        vec![1, 2, 3],
        vec![3, 3, 1, 3],
        vec![1, 2, 1, 2, 1, 2, 1],
    ];
    for ex in &examples {
        let cases = vec![ex.clone()];
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_cost_make_equal(a.clone())).collect();
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        let key = format!("{:?}", cases);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };

        let mut cases: Vec<Vec<i64>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let mode = (rng.next_u64() % 6) as usize;
            let a = make_array(&mut rng, mode);
            if total_n + a.len() > 5000 { break; }
            total_n += a.len();
            cases.push(a);
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_cost_make_equal(a.clone())).collect();
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
