use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    // Construction parameters: build an array of length n with elements from vals
    n: usize,
    vals: Vec<i64>,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        1 <= n <= 200_000,
        vals.len() == n,
        forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000,
    ensures
        1 <= result.len() <= 200_000,
        forall |k: int| 0 <= k < result.len() ==> 0 <= #[trigger] result[k] <= 10_000,
{
    if mutation_kind == 0 {
        // Identity: return vals as-is
        vals
    } else if mutation_kind == 1 && n >= 2 {
        // Shrink: drop last element
        let mut out: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                out.len() == i,
                n >= 2,
                1 <= n <= 200_000,
                vals.len() == n,
                forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000,
                forall |k: int| 0 <= k < out.len() ==> 0 <= #[trigger] out[k] <= 10_000,
            decreases n - 1 - i,
        {
            let v = vals[i];
            assert(0 <= vals[i as int] <= 10_000);
            out.push(v);
            i += 1;
        }
        out
    } else if mutation_kind == 2 && n < 200_000 {
        // Grow: push a 0
        let mut out: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                out.len() == i,
                1 <= n <= 200_000,
                vals.len() == n,
                forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000,
                forall |k: int| 0 <= k < out.len() ==> 0 <= #[trigger] out[k] <= 10_000,
            decreases n - i,
        {
            let v = vals[i];
            assert(0 <= vals[i as int] <= 10_000);
            out.push(v);
            i += 1;
        }
        out.push(0i64);
        assert(out[out.len() - 1] == 0i64);
        assert forall |k: int| 0 <= k < out.len() implies 0 <= #[trigger] out[k] <= 10_000 by {
            if k < n as int {
                assert(0 <= out[k] <= 10_000);
            } else {
                assert(k == out.len() - 1);
                assert(out[k] == 0i64);
            }
        }
        out
    } else if mutation_kind == 3 {
        // Set all elements to 0
        let mut out: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                out.len() == i,
                1 <= n <= 200_000,
                forall |k: int| 0 <= k < out.len() ==> #[trigger] out[k] == 0i64,
            decreases n - i,
        {
            out.push(0i64);
            i += 1;
        }
        assert forall |k: int| 0 <= k < out.len() implies 0 <= #[trigger] out[k] <= 10_000 by {
            assert(out[k] == 0i64);
        }
        out
    } else if mutation_kind == 4 {
        // Set all elements to 10_000
        let mut out: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                out.len() == i,
                1 <= n <= 200_000,
                forall |k: int| 0 <= k < out.len() ==> #[trigger] out[k] == 10_000i64,
            decreases n - i,
        {
            out.push(10_000i64);
            i += 1;
        }
        assert forall |k: int| 0 <= k < out.len() implies 0 <= #[trigger] out[k] <= 10_000 by {
            assert(out[k] == 10_000i64);
        }
        out
    } else if mutation_kind == 5 && n >= 2 {
        // Nudge first element up by 1 (if possible)
        let mut out: Vec<i64> = Vec::new();
        let v0 = if vals[0] < 10_000 { vals[0] + 1 } else { vals[0] };
        out.push(v0);
        assert(0 <= v0 <= 10_000);
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                out.len() == i,
                1 <= n <= 200_000,
                n >= 2,
                vals.len() == n,
                forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000,
                forall |k: int| 0 <= k < out.len() ==> 0 <= #[trigger] out[k] <= 10_000,
            decreases n - i,
        {
            let v = vals[i];
            assert(0 <= vals[i as int] <= 10_000);
            out.push(v);
            i += 1;
        }
        out
    } else {
        // Fallback: identity
        vals
    }
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

fn build_output(answers: &[i32]) -> String {
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
            vec![4, 5, 2, 5],
            vec![0, 4],
            vec![10, 8, 5, 1, 4],
            vec![10000],
            vec![1, 1, 1, 1, 1, 1, 1],
        ];
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_friends_for_equal_candies(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    // edges
    let edges: Vec<Vec<i64>> = vec![
        vec![0],
        vec![10000],
        vec![0, 0],
        vec![1, 1],
        vec![5, 5, 5, 5],
        vec![0, 10000],
        vec![10000, 0],
    ];
    for e in edges {
        if count >= target { break; }
        let cases: Vec<Vec<i64>> = vec![e];
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_friends_for_equal_candies(a.clone())).collect();
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
                2 => rng.gen_range_usize(5, 30),
                3 => rng.gen_range_usize(30, 100),
                _ => rng.gen_range_usize(100, 500),
            };
            let mut a: Vec<i64> = Vec::with_capacity(n);
            for _ in 0..n {
                a.push(rng.gen_range_i64(0, 100));
            }
            cases.push(a);
        }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::min_friends_for_equal_candies(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

