use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i32>,
    period: u32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, u32))
    requires
        a.len() >= 1,
        a.len() <= 200_000,
        1 <= period <= a.len(),
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
    ensures
        result.0.len() >= 1,
        result.0.len() <= 200_000,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (a, period)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = a;
        d.set(0, 1);
        (d, period)
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut d = a;
        d.set(0, 1_000_000_000);
        (d, period)
    } else if mutation_kind == 3 && a[0] < 1_000_000_000 {
        // nudge first element up
        let mut d = a;
        d.set(0, d[0] + 1);
        (d, period)
    } else if mutation_kind == 4 && a[0] > 1 {
        // nudge first element down
        let mut d = a;
        d.set(0, d[0] - 1);
        (d, period)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let n = a.len();
        let mut d = a;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == n,
                n >= 1,
                n <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
            decreases n - i,
        {
            d.set(i, 1);
            i += 1;
        }
        assert forall|j: int| 0 <= j < d.len() implies 1 <= #[trigger] d[j] <= 1_000_000_000 by {
            assert(d[j] == 1i32);
        }
        (d, period)
    } else if mutation_kind == 6 {
        // set all elements to 1_000_000_000
        let n = a.len();
        let mut d = a;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                d.len() == n,
                n >= 1,
                n <= 200_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000_000i32,
            decreases n - i,
        {
            d.set(i, 1_000_000_000);
            i += 1;
        }
        assert forall|j: int| 0 <= j < d.len() implies 1 <= #[trigger] d[j] <= 1_000_000_000 by {
            assert(d[j] == 1_000_000_000i32);
        }
        (d, period)
    } else if mutation_kind == 7 {
        // set period to 1
        (a, 1)
    } else if mutation_kind == 8 {
        // set period to n (max valid period)
        let n = a.len() as u32;
        (a, n)
    } else if mutation_kind == 9 && a.len() >= 2 {
        // swap first two elements
        let mut d = a;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        (d, period)
    } else if mutation_kind == 10 && a.len() < 200_000 {
        // grow: push element with value 1, adjust period if needed
        let mut d = a;
        d.push(1);
        assert(1 <= 1i32 <= 1_000_000_000);
        assert forall|j: int| 0 <= j < d.len() implies 1 <= #[trigger] d[j] <= 1_000_000_000 by {
            if j < d.len() - 1 {
                assert(1 <= d[j] <= 1_000_000_000);
            } else {
                assert(d[j] == 1i32);
            }
        }
        (d, period)
    } else if mutation_kind == 11 && a.len() > 1 && period < a.len() as u32 {
        // shrink: pop last element
        let mut d = a;
        d.pop();
        (d, period)
    } else {
        // fallback: identity
        (a, period)
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

fn build_input_multi(cases: &[(Vec<i32>, u32)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, k) in cases {
        s.push_str(&format!("{} {}\n", a.len(), k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output_multi(answers: &[i32]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn make_distinct(rng: &mut Rng, n: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut used = HashSet::new();
    let mut a: Vec<i32> = Vec::with_capacity(n);
    let mut tries = 0;
    let max_tries = n * 30 + 100;
    while a.len() < n && tries < max_tries {
        tries += 1;
        let v = rng.gen_range_i64(lo, hi) as i32;
        if used.insert(v) { a.push(v); }
    }
    a
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // The example from description (already a multi-test bundle of 9)
    let example_cases: Vec<(Vec<i32>, u32)> = vec![
        (vec![2,3,4,5], 4),
        (vec![2,3,4,5], 3),
        (vec![3,4,8,9], 3),
        (vec![6,2,1,1], 1),  // careful: distinct? main expects distinct, but description shows that test... we shouldn't include if not safe. Actually description had different test cases, let me just use simpler ones below.
    ];
    // Skip; create our own cleaner examples
    let _ = example_cases;

    let init_cases: Vec<(Vec<i32>, u32)> = vec![
        (vec![2,3,4,5], 4),
        (vec![2,3,4,5], 3),
        (vec![3,4,8,9], 3),
    ];
    {
        let cases = init_cases;
        let answers: Vec<i32> = cases.iter().map(|(a, k)| Solution::light_switches(a.clone(), *k)).collect();
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
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 25) };

        let mut cases: Vec<(Vec<i32>, u32)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 30);
            let k = rng.gen_range_usize(1, n) as u32;
            // small a values to make brute force work
            let max_a = (n * 30 + 50) as i64;
            let a = make_distinct(&mut rng, n, 1, max_a);
            if a.is_empty() || a.len() != n { continue; }
            cases.push((a, k));
        }
        if cases.is_empty() { continue; }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = cases.iter().map(|(a, k)| Solution::light_switches(a.clone(), *k)).collect();
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

