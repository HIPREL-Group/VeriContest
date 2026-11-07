use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_n: i64,
    seed_m: i64,
    seed_t1: i32,
    seed_t2: i32,
    seed_y1: i64,
    seed_y2: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i32, i64, i32, i64))
    requires
        1 <= seed_n <= 1_000_000_000_000_000_000i64,
        1 <= seed_m <= 1_000_000_000_000_000_000i64,
        1 <= seed_y1 <= 1_000_000_000_000_000_000i64,
        1 <= seed_y2 <= 1_000_000_000_000_000_000i64,
    ensures
        1 <= result.0 <= 1_000_000_000_000_000_000,
        1 <= result.1 <= 1_000_000_000_000_000_000,
        result.2 == 1 || result.2 == 2,
        result.4 == 1 || result.4 == 2,
        result.2 == 1 ==> 1 <= result.3 <= result.0,
        result.2 == 2 ==> 1 <= result.3 <= result.1,
        result.4 == 1 ==> 1 <= result.5 <= result.0,
        result.4 == 2 ==> 1 <= result.5 <= result.1,
{
    let n: i64 = if mutation_kind == 5 {
        seed_m
    } else if mutation_kind == 6 {
        1i64
    } else if mutation_kind == 8 {
        1i64
    } else {
        seed_n
    };

    let m: i64 = if mutation_kind == 7 {
        1i64
    } else if mutation_kind == 8 {
        1i64
    } else {
        seed_m
    };

    let t1: i32 = if seed_t1 % 2 == 0 { 1i32 } else { 2i32 };
    let t2: i32 = if seed_t2 % 2 == 0 { 1i32 } else { 2i32 };

    let upper1: i64 = if t1 == 1 { n } else { m };
    let upper2: i64 = if t2 == 1 { n } else { m };

    let y1_clamped: i64 = if seed_y1 > upper1 { upper1 } else { seed_y1 };
    let y2_clamped: i64 = if seed_y2 > upper2 { upper2 } else { seed_y2 };

    let y1: i64 = if mutation_kind == 1 {
        1i64
    } else if mutation_kind == 2 {
        upper1
    } else {
        y1_clamped
    };

    let y2: i64 = if mutation_kind == 3 {
        1i64
    } else if mutation_kind == 4 {
        upper2
    } else {
        y2_clamped
    };

    (n, m, t1, y1, t2, y2)
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

fn build_input(n: i64, m: i64, queries: &[(i32,i64,i32,i64)]) -> String {
    let mut s = format!("{} {} {}\n", n, m, queries.len());
    for &(t1,y1,t2,y2) in queries {
        s.push_str(&format!("{} {} {} {}\n", t1, y1, t2, y2));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a { "YES\n" } else { "NO\n" });
    }
    s
}

fn solve(n: i64, m: i64, queries: &[(i32,i64,i32,i64)]) -> Vec<bool> {
    queries.iter().map(|&(t1,y1,t2,y2)| Solution::corridor_same_component(n, m, t1, y1, t2, y2)).collect()
}

fn random_query(rng: &mut Rng, n: i64, m: i64) -> (i32, i64, i32, i64) {
    let t1: i32 = rng.gen_range_i64(1, 2) as i32;
    let y1: i64 = if t1 == 1 { rng.gen_range_i64(1, n) } else { rng.gen_range_i64(1, m) };
    let t2: i32 = rng.gen_range_i64(1, 2) as i32;
    let y2: i64 = if t2 == 1 { rng.gen_range_i64(1, n) } else { rng.gen_range_i64(1, m) };
    (t1, y1, t2, y2)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: i64, m: i64, queries: Vec<(i32,i64,i32,i64)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= n as u64; h = h.wrapping_mul(1099511628211);
        h ^= m as u64; h = h.wrapping_mul(1099511628211);
        h ^= queries.len() as u64; h = h.wrapping_mul(1099511628211);
        for &(t1,y1,t2,y2) in &queries {
            h ^= t1 as u64; h = h.wrapping_mul(1099511628211);
            h ^= y1 as u64; h = h.wrapping_mul(1099511628211);
            h ^= t2 as u64; h = h.wrapping_mul(1099511628211);
            h ^= y2 as u64; h = h.wrapping_mul(1099511628211);
        }
        if !seen.insert(h) { return; }
        let answers = solve(n, m, &queries);
        let inp = build_input(n, m, &queries);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Example
    emit(4, 6, vec![(1,1,2,3),(2,6,1,2),(2,6,2,4)], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(1, 1, vec![(1,1,2,1)], &mut seen, &mut out, &mut count);
    emit(2, 2, vec![(1,1,1,2),(1,1,2,1),(1,1,2,2)], &mut seen, &mut out, &mut count);
    emit(1_000_000_000_000_000_000, 1_000_000_000_000_000_000, vec![(1,1,2,1)], &mut seen, &mut out, &mut count);
    emit(1, 1_000_000_000_000_000_000, vec![(1,1,2,1),(1,1,2,1_000_000_000_000_000_000)], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_i64(1, 10),
            1 => rng.gen_range_i64(1, 100),
            2 => rng.gen_range_i64(1, 1000),
            3 => rng.gen_range_i64(1, 1_000_000),
            _ => rng.gen_range_i64(1, 1_000_000_000_000_000_000),
        };
        let m = match tries % 4 {
            0 => rng.gen_range_i64(1, 10),
            1 => rng.gen_range_i64(1, 100),
            2 => rng.gen_range_i64(1, 1_000_000),
            _ => rng.gen_range_i64(1, 1_000_000_000_000_000_000),
        };
        let q = rng.gen_range_usize(1, 50);
        let queries: Vec<_> = (0..q).map(|_| random_query(&mut rng, n, m)).collect();
        emit(n, m, queries, &mut seen, &mut out, &mut count);
    }
}

