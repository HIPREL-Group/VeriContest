use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, seed_a: Vec<u32>, mutation_kind: u8) -> (result: (usize, Vec<u32>))
    requires
        1 <= seed_n <= 40,
        seed_a.len() == seed_n,
        forall|i: int| 0 <= i < seed_a.len() ==> #[trigger] seed_a[i] <= 1000u32,
    ensures
        1 <= result.0 <= 40,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 1000u32,
{
    let n = seed_n;
    if mutation_kind == 0 {
        (n, seed_a)
    } else if mutation_kind == 1 {
        let mut d = seed_a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                forall|j: int| 0 <= j < i ==> d[j] == 0u32,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 1000u32,
            decreases d.len() - i,
        {
            d.set(i, 0u32);
            i += 1;
        }
        (n, d)
    } else if mutation_kind == 2 {
        let mut d = seed_a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                forall|j: int| 0 <= j < i ==> d[j] == 1u32,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 1000u32,
            decreases d.len() - i,
        {
            d.set(i, 1u32);
            i += 1;
        }
        (n, d)
    } else if mutation_kind == 3 {
        let mut d = seed_a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                forall|j: int| 0 <= j < i ==> #[trigger] d[j] <= 1000u32,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 1000u32,
            decreases d.len() - i,
        {
            if i % 2 == 0 {
                d.set(i, 2u32);
            } else {
                d.set(i, 1u32);
            }
            i += 1;
        }
        (n, d)
    } else {
        (n, seed_a)
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

fn build_one_case(a: &[u32]) -> (String, String) {
    let n = a.len();
    let mut inp = format!("1\n{}\n", n);
    for (i, x) in a.iter().enumerate() {
        if i > 0 { inp.push(' '); }
        inp.push_str(&x.to_string());
    }
    inp.push('\n');
    let ans = Solution::min_swaps(n, a.to_vec());
    let outp = format!("{}\n", ans);
    (inp, outp)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1367);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Vec<u32>> = vec![
        vec![3, 2, 7, 6],
        vec![3, 2, 6],
        vec![7],
        vec![4, 9, 2, 1, 18, 3, 0],
    ];
    for a in &examples {
        if count >= target { break; }
        let (inp, outp) = build_one_case(a);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = rng.gen_range_usize(1, 40);
        let mut a: Vec<u32> = Vec::with_capacity(n);
        for _ in 0..n {
            let r = rng.next_u64() % 5;
            let v = match r {
                0 => 0u32,
                1 => 1u32,
                2 => (rng.next_u64() % 1001) as u32,
                3 => (rng.next_u64() % 100) as u32,
                _ => (rng.next_u64() % 10) as u32,
            };
            a.push(v);
        }
        let (inp, outp) = build_one_case(&a);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
