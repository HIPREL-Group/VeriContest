use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_l: i32,
    seed_gap_lr: i32,
    seed_big_l: i32,
    seed_gap_big_lr: i32,
    mutation_kind: u8,
) -> (res: (i32, i32, i32, i32))
    requires
        1 <= seed_l <= 99,
        1 <= seed_gap_lr <= 99,
        1 <= seed_big_l <= 99,
        1 <= seed_gap_big_lr <= 99,
    ensures
        1 <= res.0 < res.1 <= 100,
        1 <= res.2 < res.3 <= 100,
{
    // Base construction: l = seed_l, r = min(seed_l + seed_gap_lr, 100)
    let l: i32 = seed_l;
    let r: i32 = if seed_l + seed_gap_lr <= 100 { seed_l + seed_gap_lr } else { 100i32 };
    let big_l: i32 = seed_big_l;
    let big_r: i32 = if seed_big_l + seed_gap_big_lr <= 100 { seed_big_l + seed_gap_big_lr } else { 100i32 };

    if mutation_kind == 0u8 {
        (l, r, big_l, big_r)                        // identity
    } else if mutation_kind == 1u8 {
        (l, r, l, r)                                // identical segments
    } else if mutation_kind == 2u8 {
        (big_l, big_r, l, r)                        // swap segments
    } else if mutation_kind == 3u8 {
        (1i32, 2i32, 99i32, 100i32)                 // disjoint far apart
    } else if mutation_kind == 4u8 {
        (1i32, 100i32, 1i32, 100i32)                // both full range
    } else if mutation_kind == 5u8 {
        (1i32, 2i32, 1i32, 2i32)                    // both minimal
    } else if mutation_kind == 6u8 {
        (99i32, 100i32, 99i32, 100i32)              // both maximal-minimal
    } else if mutation_kind == 7u8 {
        // nudge l down
        let new_l: i32 = if l > 1i32 { (l - 1i32) as i32 } else { 1i32 };
        (new_l, r, big_l, big_r)
    } else if mutation_kind == 8u8 {
        // nudge r up
        let new_r: i32 = if r < 100i32 { (r + 1i32) as i32 } else { 100i32 };
        (l, new_r, big_l, big_r)
    } else if mutation_kind == 9u8 {
        // set l to 1
        (1i32, r, big_l, big_r)
    } else if mutation_kind == 10u8 {
        // set r to 100
        (l, 100i32, big_l, big_r)
    } else if mutation_kind == 11u8 {
        // set L to 1
        (l, r, 1i32, big_r)
    } else if mutation_kind == 12u8 {
        // set R to 100
        (l, r, big_l, 100i32)
    } else {
        (l, r, big_l, big_r)                        // fallback = identity
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

fn build_input(cases: &[(i32, i32, i32, i32)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(l, r, ll, rr) in cases {
        s.push_str(&format!("{} {}\n{} {}\n", l, r, ll, rr));
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn rand_pair(rng: &mut Rng) -> (i32, i32) {
    let l = rng.gen_range_i64(1, 99) as i32;
    let r = rng.gen_range_i64(l as i64 + 1, 100) as i32;
    (l, r)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<(i32, i32, i32, i32)> = vec![
        (1, 2, 3, 4),
        (2, 5, 2, 5),
        (3, 7, 6, 7),
        (4, 5, 2, 8),
    ];
    {
        let answers: Vec<i32> = example.iter().map(|&(l, r, ll, rr)| Solution::min_doors_to_lock(l, r, ll, rr)).collect();
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
                       else if count < 60 { rng.gen_range_usize(3, 15) }
                       else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<(i32, i32, i32, i32)> = Vec::with_capacity(t);
        for _ in 0..t {
            let (l, r) = rand_pair(&mut rng);
            let (ll, rr) = rand_pair(&mut rng);
            cases.push((l, r, ll, rr));
        }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i32> = cases.iter().map(|&(l, r, ll, rr)| Solution::min_doors_to_lock(l, r, ll, rr)).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

