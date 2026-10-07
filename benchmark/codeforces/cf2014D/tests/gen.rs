use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    d: i32,
    a_vals: Vec<i32>,
    b_vals: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, i32, Vec<i32>, Vec<i32>))
    requires
        1 <= n,
        n <= 100000,
        1 <= d <= n,
        1 <= a_vals.len() <= n as nat,
        a_vals.len() == b_vals.len(),
        forall|j: int| 0 <= j < a_vals.len() as int ==> 1 <= #[trigger] a_vals[j] <= n,
        forall|j: int| 0 <= j < b_vals.len() as int ==> 1 <= #[trigger] b_vals[j] <= n,
    ensures
        1 <= result.0,
        result.0 <= 100000,
        1 <= result.1 <= result.0,
        1 <= result.2.len() <= result.0 as nat,
        result.2.len() == result.3.len(),
        forall|j: int| 0 <= j < result.2.len() as int ==> 1 <= #[trigger] result.2[j] <= result.3[j] <= result.0,
{
    let mut left: Vec<i32> = Vec::new();
    let mut right: Vec<i32> = Vec::new();
    let k = a_vals.len();

    if mutation_kind == 1 {
        // All single-day jobs: left[j] = right[j] = a_vals[j]
        let mut j: usize = 0;
        while j < k
            invariant
                k == a_vals.len(),
                1 <= n <= 100000,
                left.len() == j,
                right.len() == j,
                j <= k,
                forall|i: int| 0 <= i < a_vals.len() as int ==> 1 <= #[trigger] a_vals[i] <= n,
                forall|i: int| 0 <= i < j as int ==> 1 <= #[trigger] left[i] <= right[i] <= n,
            decreases k - j,
        {
            left.push(a_vals[j]);
            right.push(a_vals[j]);
            j = j + 1;
        }
    } else if mutation_kind == 2 {
        // All maximal jobs: left = 1, right = n
        let mut j: usize = 0;
        while j < k
            invariant
                k == a_vals.len(),
                1 <= n <= 100000,
                left.len() == j,
                right.len() == j,
                j <= k,
                forall|i: int| 0 <= i < j as int ==> 1 <= #[trigger] left[i] <= right[i] <= n,
            decreases k - j,
        {
            left.push(1);
            right.push(n);
            j = j + 1;
        }
    } else if mutation_kind == 3 {
        // All jobs on day 1: left = right = 1
        let mut j: usize = 0;
        while j < k
            invariant
                k == a_vals.len(),
                1 <= n <= 100000,
                left.len() == j,
                right.len() == j,
                j <= k,
                forall|i: int| 0 <= i < j as int ==> 1 <= #[trigger] left[i] <= right[i] <= n,
            decreases k - j,
        {
            left.push(1);
            right.push(1);
            j = j + 1;
        }
    } else if mutation_kind == 4 {
        // All jobs on last day: left = right = n
        let mut j: usize = 0;
        while j < k
            invariant
                k == a_vals.len(),
                1 <= n <= 100000,
                left.len() == j,
                right.len() == j,
                j <= k,
                forall|i: int| 0 <= i < j as int ==> 1 <= #[trigger] left[i] <= right[i] <= n,
            decreases k - j,
        {
            left.push(n);
            right.push(n);
            j = j + 1;
        }
    } else if mutation_kind == 5 {
        // All jobs span first half: left = 1, right = midpoint
        let mid = if n / 2 >= 1 { n / 2 } else { 1 };
        let mut j: usize = 0;
        while j < k
            invariant
                k == a_vals.len(),
                1 <= n <= 100000,
                1 <= mid <= n,
                left.len() == j,
                right.len() == j,
                j <= k,
                forall|i: int| 0 <= i < j as int ==> 1 <= #[trigger] left[i] <= right[i] <= n,
            decreases k - j,
        {
            left.push(1);
            right.push(mid);
            j = j + 1;
        }
    } else {
        // Default (mutation_kind == 0 or fallback): sort pairs via min/max
        let mut j: usize = 0;
        while j < k
            invariant
                k == a_vals.len(),
                k == b_vals.len(),
                1 <= n <= 100000,
                left.len() == j,
                right.len() == j,
                j <= k,
                forall|i: int| 0 <= i < a_vals.len() as int ==> 1 <= #[trigger] a_vals[i] <= n,
                forall|i: int| 0 <= i < b_vals.len() as int ==> 1 <= #[trigger] b_vals[i] <= n,
                forall|i: int| 0 <= i < j as int ==> 1 <= #[trigger] left[i] <= right[i] <= n,
            decreases k - j,
        {
            let a = a_vals[j];
            let b = b_vals[j];
            if a <= b {
                left.push(a);
                right.push(b);
            } else {
                left.push(b);
                right.push(a);
            }
            j = j + 1;
        }
    }

    (n, d, left, right)
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

fn build_input(cases: &[(i32, i32, Vec<i32>, Vec<i32>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, d, left, right) in cases {
        let k = left.len();
        s.push_str(&format!("{} {} {}\n", n, d, k));
        for i in 0..k {
            s.push_str(&format!("{} {}\n", left[i], right[i]));
        }
    }
    s
}

fn build_output(answers: &[(i32, i32)]) -> String {
    let mut s = String::new();
    for &(b, m) in answers {
        s.push_str(&format!("{} {}\n", b, m));
    }
    s
}

fn make_case(rng: &mut Rng) -> (i32, i32, Vec<i32>, Vec<i32>) {
    let n = rng.gen_range_i64(1, 50) as i32;
    let d = rng.gen_range_i64(1, n as i64) as i32;
    let k = rng.gen_range_usize(1, n as usize);
    let mut left = Vec::with_capacity(k);
    let mut right = Vec::with_capacity(k);
    for _ in 0..k {
        let l = rng.gen_range_i64(1, n as i64) as i32;
        let r = rng.gen_range_i64(l as i64, n as i64) as i32;
        left.push(l);
        right.push(r);
    }
    (n, d, left, right)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 20) };
        let mut cases: Vec<(i32, i32, Vec<i32>, Vec<i32>)> = Vec::with_capacity(t);
        let mut total_nk = 0usize;
        for _ in 0..t {
            let case = make_case(&mut rng);
            let nn = case.0 as usize + case.2.len();
            if total_nk + nn > 5000 { break; }
            total_nk += nn;
            cases.push(case);
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<(i32, i32)> = cases.iter().map(|(n, d, l, r)| Solution::best_start_days(*n, *d, l.clone(), r.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

