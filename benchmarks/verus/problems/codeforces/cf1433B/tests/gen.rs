use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_n: usize, seed_a: Vec<u8>, mutation_kind: u8) -> (result: (usize, Vec<u8>))
    requires
        1 <= seed_n <= 50,
        seed_a.len() == seed_n,
        forall|i: int| 0 <= i < seed_a.len() ==> #[trigger] seed_a[i] <= 1u8,
    ensures
        1 <= result.0 <= 50,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 1u8,
        exists|i: int| 0 <= i < result.1.len() && #[trigger] result.1[i] == 1u8,
{
    let n = seed_n;
    let mut d = seed_a;
    // Ensure at least one 1: place 1 at position 0
    d.set(0, 1u8);
    assert(d[0] == 1u8);
    if mutation_kind == 0 {
        (n, d)
    } else if mutation_kind == 1 {
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                d[0] == 1u8,
                forall|j: int| 0 <= j < i ==> d[j] == 1u8,
                forall|j: int| i <= j < d.len() ==> #[trigger] d[j] <= 1u8,
            decreases d.len() - i,
        {
            d.set(i, 1u8);
            i += 1;
        }
        assert(d[0] == 1u8);
        (n, d)
    } else if mutation_kind == 2 && n > 1 {
        // last element 1 only
        let mut i: usize = 1;
        while i < d.len() - 1
            invariant
                1 <= i <= d.len() - 1,
                d.len() == n,
                d[0] == 1u8,
                forall|j: int| 0 <= j < d.len() ==> #[trigger] d[j] <= 1u8,
            decreases d.len() - i,
        {
            d.set(i, 0u8);
            i += 1;
        }
        d.set(d.len() - 1, 1u8);
        assert(d[0] == 1u8);
        (n, d)
    } else {
        (n, d)
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
        // Shift to use higher-quality bits
        (self.0 >> 17) ^ (self.0 >> 33)
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

fn build_one_case(a: &[u8]) -> (String, String) {
    let n = a.len();
    let mut inp = format!("1\n{}\n", n);
    for (i, x) in a.iter().enumerate() {
        if i > 0 { inp.push(' '); }
        inp.push_str(&x.to_string());
    }
    inp.push('\n');
    let ans = Solution::min_moves_books(n, a.to_vec());
    let outp = format!("{}\n", ans);
    (inp, outp)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1433);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Vec<u8>> = vec![
        vec![0, 0, 1, 0, 1, 0, 1],
        vec![1, 0, 0],
        vec![1, 1, 0, 0, 1],
        vec![1, 0, 0, 0, 0, 1],
        vec![1, 1, 0, 1, 1],
    ];
    for a in &examples {
        if count >= target { break; }
        let (inp, outp) = build_one_case(a);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 1000 {
        tries += 1;
        let n = rng.gen_range_usize(1, 50);
        let mut a: Vec<u8> = Vec::with_capacity(n);
        let mut has_one = false;
        for _ in 0..n {
            let v = (rng.next_u64() % 2) as u8;
            if v == 1 { has_one = true; }
            a.push(v);
        }
        if !has_one {
            a[0] = 1;
        }
        let (inp, outp) = build_one_case(&a);
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
