use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: Vec<i64>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i64>))
    requires
        1 <= vals.len() <= 3000,
        forall|i: int| 0 <= i && i < vals.len() ==> 1 <= #[trigger] vals[i] && vals[i] <= 100000,
    ensures
        1 <= result.0 && result.0 <= 3000,
        result.1.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> 1 <= result.1@[i] && result.1@[i] <= 100000,
{
    let n = vals.len();
    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;

    if mutation_kind == 1 {
        // All elements set to vals[0]
        let v0 = vals[0];
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 3000,
                a.len() == idx,
                idx <= n,
                1 <= v0 && v0 <= 100000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] && a[j] <= 100000,
            decreases n - idx,
        {
            a.push(v0);
            idx = idx + 1;
        }
    } else if mutation_kind == 2 {
        // All elements set to 1 (minimum)
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 3000,
                a.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] && a[j] <= 100000,
            decreases n - idx,
        {
            a.push(1i64);
            idx = idx + 1;
        }
    } else if mutation_kind == 3 {
        // All elements set to 100000 (maximum)
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 3000,
                a.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] && a[j] <= 100000,
            decreases n - idx,
        {
            a.push(100000i64);
            idx = idx + 1;
        }
    } else if mutation_kind == 4 && n >= 2 {
        // Swap first two elements
        a.push(vals[1]);
        a.push(vals[0]);
        idx = 2;
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 3000,
                a.len() == idx,
                2 <= idx <= n,
                forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] && vals[i] <= 100000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] && a[j] <= 100000,
            decreases n - idx,
        {
            a.push(vals[idx]);
            idx = idx + 1;
        }
    } else if mutation_kind == 5 {
        // Set last element to 1
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 3000,
                a.len() == idx,
                idx <= n,
                forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] && vals[i] <= 100000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] && a[j] <= 100000,
            decreases n - idx,
        {
            if idx == n - 1 {
                a.push(1i64);
            } else {
                a.push(vals[idx]);
            }
            idx = idx + 1;
        }
    } else if mutation_kind == 6 {
        // Set last element to 100000
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 3000,
                a.len() == idx,
                idx <= n,
                forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] && vals[i] <= 100000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] && a[j] <= 100000,
            decreases n - idx,
        {
            if idx == n - 1 {
                a.push(100000i64);
            } else {
                a.push(vals[idx]);
            }
            idx = idx + 1;
        }
    } else {
        // Default (mutation_kind == 0 or fallback): identity
        while idx < n
            invariant
                n == vals.len(),
                1 <= n <= 3000,
                a.len() == idx,
                idx <= n,
                forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] && vals[i] <= 100000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] && a[j] <= 100000,
            decreases n - idx,
        {
            a.push(vals[idx]);
            idx = idx + 1;
        }
    }

    (n, a)
}

}

use std::io::Write;

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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let cases: Vec<Vec<i64>> = vec![
            vec![3, 1, 6, 6, 2],
            vec![1, 2, 2, 1],
            vec![2, 2, 2],
            vec![6, 3, 2, 1],
        ];
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_operations(a.len(), a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    // edge singles
    let edges: Vec<Vec<i64>> = vec![
        vec![1],
        vec![5],
        vec![1, 1],
        vec![1, 2],
        vec![2, 2],
        vec![100000],
        vec![1; 50],
    ];
    for e in edges {
        if count >= target { break; }
        let cases: Vec<Vec<i64>> = vec![e];
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_operations(a.len(), a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 5 {
                0 => 1,
                1 => rng.gen_range_usize(2, 5),
                2 => rng.gen_range_usize(5, 20),
                3 => rng.gen_range_usize(20, 50),
                _ => rng.gen_range_usize(50, 100),
            };
            let mut a: Vec<i64> = Vec::with_capacity(n);
            for _ in 0..n {
                a.push(rng.gen_range_i64(1, 20));
            }
            cases.push(a);
        }
        let answers: Vec<i64> = cases.iter().map(|a| Solution::min_operations(a.len(), a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

