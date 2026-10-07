use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_vals: Vec<i32>,
    mutation_kind: u8,
) -> (a: Vec<i32>)
    requires
        1 <= raw_vals.len() <= 300_000,
        forall|i: int| 0 <= i < raw_vals.len() ==> 1 <= #[trigger] raw_vals[i] <= 300_000,
    ensures
        a.len() >= 1,
        a.len() <= 300_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= a.len() as int,
{
    let n = raw_vals.len();
    let n_i32 = n as i32;
    let mut a: Vec<i32> = Vec::new();
    let mut idx: usize = 0;

    if mutation_kind == 1 {
        // All elements = 1
        while idx < n
            invariant
                n == raw_vals.len(),
                1 <= n <= 300_000,
                n_i32 == n as int,
                a.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] a[j] == 1,
            decreases n - idx,
        {
            a.push(1i32);
            idx = idx + 1;
        }
        proof {
            assert(a.len() == n);
            assert forall|j: int| 0 <= j < a.len() implies 1 <= #[trigger] a[j] <= a.len() as int by {
                assert(a[j] == 1);
            }
        }
    } else if mutation_kind == 2 {
        // All elements = n
        while idx < n
            invariant
                n == raw_vals.len(),
                1 <= n <= 300_000,
                n_i32 == n as int,
                a.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] a[j] == n_i32,
            decreases n - idx,
        {
            a.push(n_i32);
            idx = idx + 1;
        }
        proof {
            assert(a.len() == n);
            assert forall|j: int| 0 <= j < a.len() implies 1 <= #[trigger] a[j] <= a.len() as int by {
                assert(a[j] == n_i32);
            }
        }
    } else if mutation_kind == 3 {
        // Ascending: element i = min(i+1, n)
        while idx < n
            invariant
                n == raw_vals.len(),
                1 <= n <= 300_000,
                n_i32 == n as int,
                a.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] <= n_i32,
            decreases n - idx,
        {
            let v = (idx as i32) + 1;
            let clamped = if v <= n_i32 { v } else { n_i32 };
            a.push(clamped);
            idx = idx + 1;
        }
        proof {
            assert(a.len() == n);
            assert forall|j: int| 0 <= j < a.len() implies 1 <= #[trigger] a[j] <= a.len() as int by {}
        }
    } else if mutation_kind == 4 {
        // Descending: element i = max(n - i, 1)
        while idx < n
            invariant
                n == raw_vals.len(),
                1 <= n <= 300_000,
                n_i32 == n as int,
                a.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] <= n_i32,
            decreases n - idx,
        {
            let v = n_i32 - (idx as i32);
            let clamped = if v >= 1 { v } else { 1i32 };
            a.push(clamped);
            idx = idx + 1;
        }
        proof {
            assert(a.len() == n);
            assert forall|j: int| 0 <= j < a.len() implies 1 <= #[trigger] a[j] <= a.len() as int by {}
        }
    } else if mutation_kind == 5 {
        // Alternating 1 and n
        while idx < n
            invariant
                n == raw_vals.len(),
                1 <= n <= 300_000,
                n_i32 == n as int,
                a.len() == idx,
                idx <= n,
                forall|j: int| 0 <= j < idx as int ==> (
                    #[trigger] a[j] == 1 || a[j] == n_i32
                ),
            decreases n - idx,
        {
            if idx % 2 == 0 {
                a.push(1i32);
            } else {
                a.push(n_i32);
            }
            idx = idx + 1;
        }
        proof {
            assert(a.len() == n);
            assert forall|j: int| 0 <= j < a.len() implies 1 <= #[trigger] a[j] <= a.len() as int by {
                assert(a[j] == 1 || a[j] == n_i32);
            }
        }
    } else {
        // Default (mutation_kind == 0 or any other): clamp raw_vals to [1, n]
        while idx < n
            invariant
                n == raw_vals.len(),
                1 <= n <= 300_000,
                n_i32 == n as int,
                a.len() == idx,
                idx <= n,
                forall|i2: int| 0 <= i2 < raw_vals.len() ==> 1 <= #[trigger] raw_vals[i2] <= 300_000,
                forall|j: int| 0 <= j < idx as int ==> 1 <= #[trigger] a[j] <= n_i32,
            decreases n - idx,
        {
            let v = raw_vals[idx];
            let clamped = if v <= n_i32 { v } else { n_i32 };
            a.push(clamped);
            idx = idx + 1;
        }
        proof {
            assert(a.len() == n);
            assert forall|j: int| 0 <= j < a.len() implies 1 <= #[trigger] a[j] <= a.len() as int by {}
        }
    }

    a
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

fn build_input(cases: &[Vec<i32>]) -> String {
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
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 4, 5, 6],
        vec![1, 2, 1, 1, 1, 3, 4],
        vec![1],
        vec![9, 9, 8, 2, 4, 4, 3, 5, 3],
        vec![1, 2, 3, 4, 1, 3, 2, 1, 1, 10],
    ];
    {
        let answers: Vec<i32> = example.iter().map(|a| Solution::max_rating(a.clone())).collect();
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
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 50);
            let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, n as i64) as i32).collect();
            if total_n + n > 5000 { break; }
            total_n += n;
            cases.push(a);
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = cases.iter().map(|a| Solution::max_rating(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

