use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, seed_a: Vec<u64>, seed_b: Vec<u64>, mutation_kind: u8) -> (result: (usize, Vec<u64>, Vec<u64>))
    requires
        1 <= seed_n <= 50,
        seed_a.len() == seed_n,
        seed_b.len() == seed_n,
        forall|i: int| 0 <= i < seed_a.len() ==> 1 <= #[trigger] seed_a[i] <= 1_000_000_000u64,
        forall|i: int| 0 <= i < seed_b.len() ==> 1 <= #[trigger] seed_b[i] <= 1_000_000_000u64,
    ensures
        1 <= result.0 <= 50,
        result.1.len() == result.0,
        result.2.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000_000u64,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= 1_000_000_000u64,
{
    let n = seed_n;
    if mutation_kind == 0 {
        (n, seed_a, seed_b)
    } else if mutation_kind == 1 {
        let mut da = seed_a;
        let mut db = seed_b;
        let mut i: usize = 0;
        while i < da.len()
            invariant
                0 <= i <= da.len(),
                da.len() == n,
                db.len() == n,
                forall|j: int| 0 <= j < i ==> da[j] == 1u64 && db[j] == 1u64,
                forall|j: int| i <= j < da.len() ==> 1 <= #[trigger] da[j] <= 1_000_000_000u64,
                forall|j: int| i <= j < db.len() ==> 1 <= #[trigger] db[j] <= 1_000_000_000u64,
            decreases da.len() - i,
        {
            da.set(i, 1u64);
            db.set(i, 1u64);
            i += 1;
        }
        (n, da, db)
    } else if mutation_kind == 2 {
        (n, seed_b, seed_a)
    } else {
        (n, seed_a, seed_b)
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

fn build_one_case(a: &[u64], b: &[u64]) -> (String, String) {
    let n = a.len();
    let mut inp = format!("1\n{}\n", n);
    for (i, x) in a.iter().enumerate() {
        if i > 0 { inp.push(' '); }
        inp.push_str(&x.to_string());
    }
    inp.push('\n');
    for (i, x) in b.iter().enumerate() {
        if i > 0 { inp.push(' '); }
        inp.push_str(&x.to_string());
    }
    inp.push('\n');
    let ans = Solution::min_moves_to_equalize(n, a.to_vec(), b.to_vec());
    let outp = format!("{}\n", ans);
    (inp, outp)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1399);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<(Vec<u64>, Vec<u64>)> = vec![
        (vec![3, 5, 6], vec![3, 2, 3]),
        (vec![1, 2, 3, 4, 5], vec![5, 4, 3, 2, 1]),
        (vec![1, 1, 1], vec![2, 2, 2]),
        (vec![1, 1000000000, 1000000000, 1000000000, 1000000000, 1000000000], vec![1, 1, 1, 1, 1, 1]),
        (vec![10, 12, 8], vec![7, 5, 4]),
    ];
    for (a, b) in &examples {
        if count >= target { break; }
        let (inp, outp) = build_one_case(a, b);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = rng.gen_range_usize(1, 50);
        let mut a: Vec<u64> = Vec::with_capacity(n);
        let mut b: Vec<u64> = Vec::with_capacity(n);
        for _ in 0..n {
            let r = rng.next_u64() % 4;
            let v = match r {
                0 => 1 + (rng.next_u64() % 10),
                1 => 1 + (rng.next_u64() % 100),
                2 => 1 + (rng.next_u64() % 1_000_000_000),
                _ => 1u64,
            };
            a.push(v);
            let r2 = rng.next_u64() % 4;
            let v2 = match r2 {
                0 => 1 + (rng.next_u64() % 10),
                1 => 1 + (rng.next_u64() % 100),
                2 => 1 + (rng.next_u64() % 1_000_000_000),
                _ => 1u64,
            };
            b.push(v2);
        }
        let (inp, outp) = build_one_case(&a, &b);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
