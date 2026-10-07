use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, seed_digits: Vec<u8>, mutation_kind: u8) -> (result: (usize, Vec<u8>))
    requires
        2 <= seed_n <= 50,
        seed_n % 2 == 0,
        seed_digits.len() == seed_n,
        forall|i: int| 0 <= i < seed_digits.len() ==> #[trigger] seed_digits[i] <= 9u8,
    ensures
        2 <= result.0 <= 50,
        result.0 % 2 == 0,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 9u8,
{
    let n = seed_n;
    if mutation_kind == 0 {
        (n, seed_digits)
    } else if mutation_kind == 1 {
        let mut d = seed_digits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                forall|j: int| 0 <= j < i ==> d[j] == 4u8,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 9u8,
            decreases d.len() - i,
        {
            d.set(i, 4u8);
            i += 1;
        }
        (n, d)
    } else if mutation_kind == 2 {
        let mut d = seed_digits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                forall|j: int| 0 <= j < i ==> d[j] == 7u8,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 9u8,
            decreases d.len() - i,
        {
            d.set(i, 7u8);
            i += 1;
        }
        (n, d)
    } else if mutation_kind == 3 {
        let mut d = seed_digits;
        let half = n / 2;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] <= 9u8,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 9u8,
            decreases d.len() - i,
        {
            if i < half {
                d.set(i, 4u8);
            } else {
                d.set(i, 7u8);
            }
            i += 1;
        }
        (n, d)
    } else if mutation_kind == 4 {
        let mut d = seed_digits;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] <= 9u8,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 9u8,
            decreases d.len() - i,
        {
            if i % 2 == 0 {
                d.set(i, 4u8);
            } else {
                d.set(i, 7u8);
            }
            i += 1;
        }
        (n, d)
    } else {
        (n, seed_digits)
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

fn build_input(digits: &[u8]) -> String {
    let mut s = String::new();
    for d in digits {
        s.push((b'0' + d) as char);
    }
    format!("{}\n{}\n", digits.len(), s)
}

fn build_output(ans: bool) -> String {
    if ans { "YES\n".to_string() } else { "NO\n".to_string() }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(146);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let example_digits: Vec<Vec<u8>> = vec![
        vec![4, 7],
        vec![4, 7, 3, 8],
        vec![4, 7, 7, 4],
        vec![4, 4, 4, 4],
        vec![7, 7],
    ];
    for d in &example_digits {
        if count >= target { break; }
        let inp = build_input(d);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::is_lucky_ticket(d.len(), d.clone());
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = 2 * rng.gen_range_usize(1, 25);
        let mut digits: Vec<u8> = Vec::with_capacity(n);
        for _ in 0..n {
            let r = rng.next_u64() % 10;
            let v = match (r, rng.next_u64() % 4) {
                (_, 0) => 4u8,
                (_, 1) => 7u8,
                _ => (r as u8),
            };
            digits.push(v);
        }
        let inp = build_input(&digits);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::is_lucky_ticket(n, digits.clone());
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut force_n = 4;
    while count < target {
        let mut digits = vec![4u8; force_n];
        digits[0] = 7;
        let inp = build_input(&digits);
        if seen.insert(inp.clone()) {
            let ans = Solution::is_lucky_ticket(force_n, digits.clone());
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
        force_n += 2;
        if force_n > 50 { force_n = 4; }
    }
}
