use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>) -> (result: Vec<i64>)
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 10000000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 50 { 50usize } else { values.len() };
    let limit = 10000000;
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 50,
            limit == 10000000,
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


pub fn generate_candidate(
    values: Vec<i64>,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        1 <= values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] as int <= 1_000_000_000,
    ensures
        1 <= result.len() <= 50,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] as int <= 1_000_000_000,
{
    let mut candies = values;

    if mutation_kind == 0 {
        // Identity: return as-is
        candies
    } else if mutation_kind == 1 && candies.len() < 50 {
        // Grow: push element equal to first element
        let v = candies[0];
        candies.push(v);
        proof {
            assert(candies@.len() == values@.len() + 1);
            assert forall|i: int| 0 <= i < candies@.len() implies
                1 <= #[trigger] candies@[i] as int <= 1_000_000_000 by {
                if i < values@.len() as int {
                    assert(candies@[i] == values@[i]);
                } else {
                    assert(candies@[i] == v);
                }
            }
        }
        candies
    } else if mutation_kind == 2 && candies.len() > 1 {
        // Shrink: pop last element
        candies.pop();
        proof {
            assert(candies@.len() == values@.len() - 1);
            assert forall|i: int| 0 <= i < candies@.len() implies
                1 <= #[trigger] candies@[i] as int <= 1_000_000_000 by {
                assert(candies@[i] == values@[i]);
            }
        }
        candies
    } else if mutation_kind == 3 {
        // Set all elements to first element (all equal)
        let v = candies[0];
        let n = candies.len();
        let mut result: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == values.len(),
                1 <= n <= 50,
                1 <= v as int <= 1_000_000_000,
                result.len() == j,
                forall|k: int| 0 <= k < j as int ==> #[trigger] result[k] == v,
            decreases n - j,
        {
            result.push(v);
            j += 1;
        }
        proof {
            assert(result@.len() == n as int);
            assert forall|i: int| 0 <= i < result@.len() implies
                1 <= #[trigger] result@[i] as int <= 1_000_000_000 by {
                assert(result@[i] == v);
            }
        }
        result
    } else if mutation_kind == 4 {
        // Set first element to 1 (minimum boundary)
        candies.set(0, 1);
        proof {
            assert forall|i: int| 0 <= i < candies@.len() implies
                1 <= #[trigger] candies@[i] as int <= 1_000_000_000 by {
                if i == 0 {
                    assert(candies@[i] == 1);
                } else {
                    assert(candies@[i] == values@[i]);
                }
            }
        }
        candies
    } else if mutation_kind == 5 {
        // Set first element to max boundary
        candies.set(0, 1_000_000_000);
        proof {
            assert forall|i: int| 0 <= i < candies@.len() implies
                1 <= #[trigger] candies@[i] as int <= 1_000_000_000 by {
                if i == 0 {
                    assert(candies@[i] == 1_000_000_000);
                } else {
                    assert(candies@[i] == values@[i]);
                }
            }
        }
        candies
    } else if mutation_kind == 6 && candies.len() >= 2 {
        // Swap first two elements
        let a = candies[0];
        let b = candies[1];
        candies.set(0, b);
        candies.set(1, a);
        proof {
            assert forall|i: int| 0 <= i < candies@.len() implies
                1 <= #[trigger] candies@[i] as int <= 1_000_000_000 by {
                if i == 0 {
                    assert(candies@[i] == b);
                } else if i == 1 {
                    assert(candies@[i] == a);
                } else {
                    assert(candies@[i] == values@[i]);
                }
            }
        }
        candies
    } else {
        // Fallback: identity
        candies
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

fn build_output(answers: &[i64]) -> String {
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

    let emit = |cases: &[Vec<i64>], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let cases: Vec<_> = cases.iter().cloned().map(generate_test_case).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_operations_to_equal(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<Vec<i64>> = vec![
        vec![1, 2, 3, 4, 5],
        vec![1000, 1000, 5, 1000],
        vec![1, 2, 3, 4, 5, 6],
        vec![3, 5, 6, 5, 7, 5, 6],
        vec![8],
        vec![1, 2],
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let arr: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 1_000_000)).collect();
            cases.push(arr);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}
