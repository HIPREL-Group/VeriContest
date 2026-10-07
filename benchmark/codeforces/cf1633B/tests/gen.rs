use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed: &Vec<u8>, mutation_kind: u8) -> (result: Vec<u8>)
    requires
        1 <= seed.len() <= 200_000,
        forall|i: int| 0 <= i < seed.len() ==> #[trigger] seed[i] == 0u8 || seed[i] == 1u8,
    ensures
        1 <= result.len() <= 200_000,
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == 0u8 || result[i] == 1u8,
{
    let n = seed.len();
    if mutation_kind == 0 {
        let mut v: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                v.len() == i,
                seed.len() == n,
                forall|j: int| 0 <= j < seed.len() ==> #[trigger] seed[j] == 0u8 || seed[j] == 1u8,
                forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == 0u8 || v[j] == 1u8,
            decreases n - i,
        {
            v.push(seed[i]);
            i = i + 1;
        }
        v
    } else if mutation_kind == 1 {
        // all zeros
        let mut v: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                v.len() == i,
                forall|j: int| 0 <= j < v.len() ==> v[j] == 0u8,
            decreases n - i,
        {
            v.push(0u8);
            i = i + 1;
        }
        v
    } else if mutation_kind == 2 {
        // single
        let mut v: Vec<u8> = Vec::new();
        v.push(seed[0]);
        v
    } else {
        let mut v: Vec<u8> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                v.len() == i,
                seed.len() == n,
                forall|j: int| 0 <= j < seed.len() ==> #[trigger] seed[j] == 0u8 || seed[j] == 1u8,
                forall|j: int| 0 <= j < v.len() ==> #[trigger] v[j] == 0u8 || v[j] == 1u8,
            decreases n - i,
        {
            v.push(seed[i]);
            i = i + 1;
        }
        v
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
    fn gen_range_u64(&mut self, lo: u64, hi: u64) -> u64 {
        lo + self.next_u64() % (hi - lo + 1)
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

fn build_case(s: &str) -> (String, String) {
    let inp = format!("{}\n", s);
    let v: Vec<u8> = s.bytes().map(|b| if b == b'0' { 0u8 } else { 1u8 }).collect();
    let res = Solution::minority_count(&v);
    let outp = format!("{}\n", res);
    (inp, outp)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1633);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let examples: Vec<Vec<&str>> = vec![
        vec!["01", "1010101010111", "011000100", "0"],
        vec!["1", "00", "11", "10"],
    ];
    for ex in &examples {
        if count >= target { break; }
        let mut inp = format!("{}\n", ex.len());
        let mut outp = String::new();
        for s in ex {
            let (i, o) = build_case(s);
            inp.push_str(&i);
            outp.push_str(&o);
        }
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 200 {
        tries += 1;
        let t = rng.gen_range_u64(1, 5) as usize;
        let mut inp = format!("{}\n", t);
        let mut outp = String::new();
        for _ in 0..t {
            let n = match rng.next_u64() % 4 {
                0 => rng.gen_range_u64(1, 5) as usize,
                1 => rng.gen_range_u64(1, 20) as usize,
                2 => rng.gen_range_u64(1, 50) as usize,
                _ => rng.gen_range_u64(1, 100) as usize,
            };
            let s: String = (0..n).map(|_| if rng.next_u64() % 2 == 0 { '0' } else { '1' }).collect();
            let (i, o) = build_case(&s);
            inp.push_str(&i);
            outp.push_str(&o);
        }
        if !seen.insert(inp.clone()) { continue; }
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
