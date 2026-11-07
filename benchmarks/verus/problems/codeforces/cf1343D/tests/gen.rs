use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i64>, k: i64, mutation_kind: u8,
) -> (result: (usize, i64, Vec<i64>))
    requires
        2 <= a.len() <= 200000,
        a.len() % 2 == 0,
        1 <= k <= 200000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= k,
    ensures
        2 <= result.0 && result.0 <= 200000,
        result.0 % 2 == 0,
        1 <= result.1 && result.1 <= 200000,
        result.2.len() == result.0,
        forall|i: int| 0 <= i && i < result.0 ==> 1 <= result.2@[i] && result.2@[i] <= result.1,
{
    let n = a.len();
    if mutation_kind == 0 {
        // identity
        (n, k, a)
    } else if mutation_kind == 1 {
        // set first element to 1
        let mut d = a;
        d.set(0, 1);
        (n, k, d)
    } else if mutation_kind == 2 {
        // set first element to k
        let mut d = a;
        d.set(0, k);
        (n, k, d)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                d.len() == n,
                2 <= n <= 200000,
                n % 2 == 0usize,
                1 <= k <= 200000,
                0 <= i <= d.len(),
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= k,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (n, k, d)
    } else if mutation_kind == 4 {
        // set all elements to k
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                d.len() == n,
                2 <= n <= 200000,
                n % 2 == 0usize,
                1 <= k <= 200000,
                0 <= i <= d.len(),
                forall|j: int| 0 <= j < d.len() ==> 1 <= #[trigger] d[j] <= k,
            decreases d.len() - i,
        {
            d.set(i, k);
            i += 1;
        }
        (n, k, d)
    } else if mutation_kind == 5 && a.len() > 2 {
        // shrink by removing last 2 elements (keep even length)
        let mut d = a;
        d.pop();
        d.pop();
        let new_n = d.len();
        (new_n, k, d)
    } else if mutation_kind == 6 && a.len() <= 199998 {
        // grow by pushing 2 copies of first element (keep even length)
        let val = a[0];
        let mut d = a;
        d.push(val);
        d.push(val);
        let new_n = d.len();
        (new_n, k, d)
    } else if mutation_kind == 7 && a.len() >= 2 {
        // swap first and last elements
        let first = a[0];
        let last_idx = a.len() - 1;
        let last = a[last_idx];
        let mut d = a;
        d.set(0, last);
        d.set(last_idx, first);
        (n, k, d)
    } else if mutation_kind == 8 {
        // set last element to 1
        let mut d = a;
        let last_idx = d.len() - 1;
        d.set(last_idx, 1);
        (n, k, d)
    } else if mutation_kind == 9 {
        // set last element to k
        let mut d = a;
        let last_idx = d.len() - 1;
        d.set(last_idx, k);
        (n, k, d)
    } else {
        // fallback: identity
        (n, k, a)
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

fn random_array(rng: &mut Rng, len: usize, k: i64) -> Vec<i64> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, k));
    }
    arr
}

fn make_even(n: usize) -> usize { if n % 2 == 0 { n } else { n + 1 } }

fn build_input(cases: &[(usize, i64, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, a) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers {
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
    let mut count = 0usize;

    // Examples from description.md as one bundled test
    {
        let cases: Vec<(usize, i64, Vec<i64>)> = vec![
            (4, 2, vec![1, 2, 1, 2]),
            (4, 3, vec![1, 2, 2, 1]),
            (8, 7, vec![6, 1, 1, 7, 6, 3, 4, 6]),
            (6, 6, vec![5, 2, 6, 1, 3, 4]),
        ];
        let answers: Vec<i64> = cases.iter().map(|(n, k, a)| Solution::constant_palindrome_sum(*n, *k, a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    // Several singleton (t=1) edge cases
    let single_cases: Vec<(usize, i64, Vec<i64>)> = vec![
        (2, 1, vec![1, 1]),
        (2, 2, vec![1, 2]),
        (2, 1000, vec![1, 1000]),
        (4, 1, vec![1, 1, 1, 1]),
        (4, 5, vec![3, 3, 3, 3]),
        (6, 6, vec![1, 6, 3, 4, 1, 5]),
        (8, 4, vec![4, 4, 4, 4, 4, 4, 4, 4]),
        (10, 10, vec![1, 10, 5, 5, 10, 1, 5, 5, 5, 5]),
    ];
    for sc in single_cases {
        if count >= target { break; }
        let answers = vec![Solution::constant_palindrome_sum(sc.0, sc.1, sc.2.clone())];
        let inp = build_input(&[sc]);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    // Random cases bundled
    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<(usize, i64, Vec<i64>)> = Vec::new();
        let mut answers: Vec<i64> = Vec::new();
        for _ in 0..t {
            let half_len = match rng.next_u64() % 5 {
                0 => rng.gen_range_usize(1, 2),
                1 => rng.gen_range_usize(1, 5),
                2 => rng.gen_range_usize(2, 25),
                3 => rng.gen_range_usize(2, 50),
                _ => rng.gen_range_usize(2, 100),
            };
            let n = make_even(half_len * 2).max(2);
            let k = match rng.next_u64() % 3 {
                0 => rng.gen_range_i64(1, 10),
                1 => rng.gen_range_i64(1, 100),
                _ => rng.gen_range_i64(1, 1000),
            };
            let a = random_array(&mut rng, n, k);
            let ans = Solution::constant_palindrome_sum(n, k, a.clone());
            cases.push((n, k, a));
            answers.push(ans);
        }
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

