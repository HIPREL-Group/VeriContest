use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw_a: Vec<i64>, raw_b: Vec<i64>) -> (result: (usize, Vec<i64>, Vec<i64>))
    ensures
        2 <= result.1.len() <= 200000,
        result.1.len() == result.2.len(),
        result.0 == result.1.len(),
        forall|j: int| 0 <= j < result.1.len() ==> 1 <= #[trigger] result.1[j] <= 1000000000,
        forall|j: int| 0 <= j < result.2.len() ==> 1 <= #[trigger] result.2[j] <= 10000,
{
    let n = if raw_a.len() < 2 { 2usize } else if raw_a.len() > 200000 { 200000usize } else { raw_a.len() };
    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 200000, 0 <= i <= n, a.len() == i, b.len() == i,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000000000,
            forall|j: int| 0 <= j < b.len() ==> 1 <= #[trigger] b[j] <= 10000,
        decreases n - i,
    {
        let av = if i < raw_a.len() { raw_a[i] } else { 1 };
        let bv = if i < raw_b.len() { raw_b[i] } else { 1 };
        a.push(if av < 1 { 1 } else if av > 1000000000 { 1000000000 } else { av });
        b.push(if bv < 1 { 1 } else if bv > 10000 { 10000 } else { bv });
        i += 1;
    }
    (n, a, b)
}


pub fn generate_candidate(a: Vec<i64>, b: Vec<i64>, mutation_kind: u8) -> (result: (Vec<i64>, Vec<i64>))
    requires
        a.len() == b.len(),
        1 <= a.len() <= 200_000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < b.len() ==> 1 <= #[trigger] b[i] <= 10_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 200_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (a, b)
    } else if mutation_kind == 1 {
        // set last a to min boundary (1)
        let mut a2 = a;
        let last = a2.len() - 1;
        a2.set(last, 1);
        (a2, b)
    } else if mutation_kind == 2 {
        // set last a to max boundary (1_000_000_000)
        let mut a2 = a;
        let last = a2.len() - 1;
        a2.set(last, 1_000_000_000);
        (a2, b)
    } else if mutation_kind == 3 {
        // set last b to min boundary (1)
        let mut b2 = b;
        let last = b2.len() - 1;
        b2.set(last, 1);
        (a, b2)
    } else if mutation_kind == 4 {
        // set last b to max boundary (10_000)
        let mut b2 = b;
        let last = b2.len() - 1;
        b2.set(last, 10_000);
        (a, b2)
    } else if mutation_kind == 5 {
        // set first a to 1
        let mut a2 = a;
        a2.set(0, 1);
        (a2, b)
    } else if mutation_kind == 6 && a.len() >= 2 {
        // set b[1] = b[0] to encourage merging groups
        let mut b2 = b;
        let val = b2[0];
        b2.set(1, val);
        (a, b2)
    } else if mutation_kind == 7 {
        // nudge last a element up if possible
        let mut a2 = a;
        let last = a2.len() - 1;
        if a2[last] < 1_000_000_000 {
            a2.set(last, a2[last] + 1);
        }
        (a2, b)
    } else if mutation_kind == 8 {
        // nudge last b element up if possible
        let mut b2 = b;
        let last = b2.len() - 1;
        if b2[last] < 10_000 {
            b2.set(last, b2[last] + 1);
        }
        (a, b2)
    } else {
        // fallback: identity
        (a, b)
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

// (n, a, b)
type TC = (usize, Vec<i64>, Vec<i64>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, a, b) in cases {
        s.push_str(&format!("{}\n", n));
        for i in 0..*n {
            s.push_str(&format!("{} {}\n", a[i], b[i]));
        }
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (_n, a, b) in cases {
        let ans = Solution::min_tags(a.clone(), b.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_case(rng: &mut Rng, max_n: usize, max_v: i64) -> TC {
    let n = rng.gen_range_usize(1, max_n);
    let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
    let b: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
    (n, a, b)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1798);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (4, vec![20, 6, 14, 20], vec![3, 2, 7, 5]),
        (1, vec![1], vec![1]),
        (2, vec![10, 10], vec![5, 5]),
        (3, vec![6, 12, 18], vec![1, 2, 3]),
        (5, vec![1, 2, 3, 4, 5], vec![1, 2, 3, 4, 5]),
        (3, vec![100, 200, 300], vec![1, 1, 1]),
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let cases: Vec<_> = cases.iter().map(|c| generate_test_case(c.1.clone(), c.2.clone())).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let max_n = match rng.gen_range_usize(0, 4) {
                0 => 5,
                1 => 20,
                2 => 50,
                3 => 100,
                _ => 30,
            };
            cases.push(random_case(&mut rng, max_n, 100));
        }
        let cases: Vec<_> = cases.iter().map(|c| generate_test_case(c.1.clone(), c.2.clone())).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
