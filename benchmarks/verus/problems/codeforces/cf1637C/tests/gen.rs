use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        3 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] && values[i] <= 1_000_000_000,
    ensures
        3 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] && result[i] <= 1_000_000_000,
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
        // set first element to 1_000_000_000 (max boundary)
        let mut v = values;
        v.set(0, 1_000_000_000);
        v
    } else if mutation_kind == 3 {
        // set last element to 1 (min boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 4 {
        // set last element to 1_000_000_000 (max boundary)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 5 {
        // set middle element to 1 (all-ones middle -> impossible case)
        let mid = values.len() / 2;
        let mut v = values;
        v.set(mid, 1);
        v
    } else if mutation_kind == 6 {
        // set all middle elements to 1 (impossible case for n > 3)
        let len = values.len();
        let mut v = values;
        let mut j: usize = 1;
        while j < len - 1
            invariant
                1 <= j <= len - 1,
                v.len() == len,
                3 <= len <= 100_000,
                v[0] == values[0],
                forall|k: int| 0 <= k < j ==> 1 <= #[trigger] v[k] && v[k] <= 1_000_000_000,
                forall|k: int| j <= k < len ==> #[trigger] v[k] == values[k],
            decreases len - 1 - j,
        {
            v.set(j, 1);
            j += 1;
        }
        // last element unchanged
        assert(v[len as int - 1] == values[len as int - 1]);
        v
    } else if mutation_kind == 7 && values.len() < 100_000 {
        // grow by one element (push 1)
        let mut v = values;
        v.push(1);
        v
    } else if mutation_kind == 8 && values.len() > 3 {
        // shrink by one element (pop)
        let mut v = values;
        v.pop();
        v
    } else if mutation_kind == 9 && values.len() >= 3 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        v
    } else if mutation_kind == 10 {
        // set middle element to 2 (even value, n==3 solvable)
        let mid = values.len() / 2;
        let mut v = values;
        v.set(mid, 2);
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

fn build_output(answers: &[Option<i64>]) -> String {
    let mut s = String::new();
    for &a in answers {
        match a {
            None => s.push_str("-1\n"),
            Some(k) => s.push_str(&format!("{}\n", k)),
        }
    }
    s
}

fn random_array(rng: &mut Rng, n: usize) -> Vec<i64> {
    (0..n).map(|_| rng.gen_range_i64(1, 100)).collect()
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
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<Option<i64>> = cases.iter().map(|a| Solution::minimum_stone_operations(a.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<Vec<i64>> = vec![
        vec![1, 2, 2, 3, 6],
        vec![1, 3, 1],
        vec![1, 2, 1],
        vec![3, 1, 1, 2],
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 30) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(3, 100);
            let arr = random_array(&mut rng, n);
            cases.push(arr);
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

