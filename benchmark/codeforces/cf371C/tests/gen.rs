use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    recipe_b: i64,
    recipe_s: i64,
    recipe_c: i64,
    stock_b: i64,
    stock_s: i64,
    stock_c: i64,
    price_b: i64,
    price_s: i64,
    price_c: i64,
    money: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64))
    requires
        0 <= recipe_b <= 100,
        0 <= recipe_s <= 100,
        0 <= recipe_c <= 100,
        1 <= recipe_b + recipe_s + recipe_c <= 100,
        1 <= stock_b <= 100,
        1 <= stock_s <= 100,
        1 <= stock_c <= 100,
        1 <= price_b <= 100,
        1 <= price_s <= 100,
        1 <= price_c <= 100,
        1 <= money <= 1_000_000_000_000,
    ensures
        0 <= result.0 <= 100,
        0 <= result.1 <= 100,
        0 <= result.2 <= 100,
        1 <= result.0 + result.1 + result.2 <= 100,
        1 <= result.3 <= 100,
        1 <= result.4 <= 100,
        1 <= result.5 <= 100,
        1 <= result.6 <= 100,
        1 <= result.7 <= 100,
        1 <= result.8 <= 100,
        1 <= result.9 <= 1_000_000_000_000,
{
    if mutation_kind == 0 {
        // Identity
        (recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c, money)
    } else if mutation_kind == 1 && recipe_s + recipe_c >= 1 {
        // Zero out bread recipe
        (0, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c, money)
    } else if mutation_kind == 2 && recipe_b + recipe_c >= 1 {
        // Zero out sausage recipe
        (recipe_b, 0, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c, money)
    } else if mutation_kind == 3 && recipe_b + recipe_s >= 1 {
        // Zero out cheese recipe
        (recipe_b, recipe_s, 0, stock_b, stock_s, stock_c, price_b, price_s, price_c, money)
    } else if mutation_kind == 4 {
        // Min money
        (recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c, 1)
    } else if mutation_kind == 5 {
        // Max money
        (recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c, 1_000_000_000_000)
    } else if mutation_kind == 6 {
        // All stocks to 1
        (recipe_b, recipe_s, recipe_c, 1, 1, 1, price_b, price_s, price_c, money)
    } else if mutation_kind == 7 {
        // All stocks to 100
        (recipe_b, recipe_s, recipe_c, 100, 100, 100, price_b, price_s, price_c, money)
    } else if mutation_kind == 8 {
        // All prices to 1
        (recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, 1, 1, 1, money)
    } else if mutation_kind == 9 {
        // All prices to 100
        (recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, 100, 100, 100, money)
    } else {
        // Default: identity
        (recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c, money)
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

fn mutate(rb: i64, rs: i64, rc: i64, sb: i64, ss: i64, sc: i64, pb: i64, ps: i64, pc: i64, money: i64, mk: u8) -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) {
    if mk == 0 {
        (rb, rs, rc, sb, ss, sc, pb, ps, pc, money)
    } else if mk == 1 && rs + rc >= 1 {
        (0, rs, rc, sb, ss, sc, pb, ps, pc, money)
    } else if mk == 2 && rb + rc >= 1 {
        (rb, 0, rc, sb, ss, sc, pb, ps, pc, money)
    } else if mk == 3 && rb + rs >= 1 {
        (rb, rs, 0, sb, ss, sc, pb, ps, pc, money)
    } else if mk == 4 {
        (rb, rs, rc, sb, ss, sc, pb, ps, pc, 1)
    } else if mk == 5 {
        (rb, rs, rc, sb, ss, sc, pb, ps, pc, 1_000_000_000_000)
    } else if mk == 6 {
        (rb, rs, rc, 1, 1, 1, pb, ps, pc, money)
    } else if mk == 7 {
        (rb, rs, rc, 100, 100, 100, pb, ps, pc, money)
    } else if mk == 8 {
        (rb, rs, rc, sb, ss, sc, 1, 1, 1, money)
    } else if mk == 9 {
        (rb, rs, rc, sb, ss, sc, 100, 100, 100, money)
    } else {
        (rb, rs, rc, sb, ss, sc, pb, ps, pc, money)
    }
}

fn random_recipe(rng: &mut Rng) -> (i64, i64, i64) {
    loop {
        let b = rng.gen_range_i64(0, 100);
        let s = rng.gen_range_i64(0, 100 - b);
        let c = rng.gen_range_i64(0, 100 - b - s);
        if b + s + c >= 1 { return (b, s, c); }
    }
}

fn build_recipe_string(rb: i64, rs: i64, rc: i64, rng: &mut Rng) -> String {
    // build a string of B, S, C in some order
    let mut chars: Vec<char> = Vec::new();
    for _ in 0..rb { chars.push('B'); }
    for _ in 0..rs { chars.push('S'); }
    for _ in 0..rc { chars.push('C'); }
    // shuffle
    for i in (1..chars.len()).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        chars.swap(i, j);
    }
    chars.into_iter().collect()
}

fn build_input(rb: i64, rs: i64, rc: i64, sb: i64, ss: i64, sc: i64, pb: i64, ps: i64, pc: i64, money: i64, rng: &mut Rng) -> String {
    let r = build_recipe_string(rb, rs, rc, rng);
    format!("{}\n{} {} {}\n{} {} {}\n{}\n", r, sb, ss, sc, pb, ps, pc, money)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |rb: i64, rs: i64, rc: i64, sb: i64, ss: i64, sc: i64, pb: i64, ps: i64, pc: i64, money: i64,
        rng: &mut Rng, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if !(0 <= rb && rb <= 100 && 0 <= rs && rs <= 100 && 0 <= rc && rc <= 100) { return; }
        let sum = rb + rs + rc;
        if !(1 <= sum && sum <= 100) { return; }
        if !(1 <= sb && sb <= 100 && 1 <= ss && ss <= 100 && 1 <= sc && sc <= 100) { return; }
        if !(1 <= pb && pb <= 100 && 1 <= ps && ps <= 100 && 1 <= pc && pc <= 100) { return; }
        if !(1 <= money && money <= 1_000_000_000_000) { return; }
        let key = format!("{},{},{},{},{},{},{},{},{},{}", rb, rs, rc, sb, ss, sc, pb, ps, pc, money);
        if !seen.insert(key) { return; }
        let inp = build_input(rb, rs, rc, sb, ss, sc, pb, ps, pc, money, rng);
        let ans = Solution::max_hamburgers(rb, rs, rc, sb, ss, sc, pb, ps, pc, money);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let mutation_kinds: Vec<u8> = (0..=9).collect();
    let examples: Vec<(i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)> = vec![
        (3, 2, 1, 6, 4, 1, 1, 2, 3, 12),
        (2, 0, 1, 1, 10, 1, 1, 10, 1, 21),
        (1, 1, 1, 1, 1, 1, 1, 1, 1, 1_000_000_000_000),
    ];
    for &(rb, rs, rc, sb, ss, sc, pb, ps, pc, m) in &examples {
        for &mk in &mutation_kinds {
            let (a,b,c,d,e,f,g,h,i,j) = mutate(rb, rs, rc, sb, ss, sc, pb, ps, pc, m, mk);
            emit(a,b,c,d,e,f,g,h,i,j, &mut rng, &mut seen, &mut out, &mut count);
        }
    }

    let seeds: Vec<(i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)> = vec![
        (1, 0, 0, 1, 1, 1, 1, 1, 1, 1),
        (0, 1, 0, 1, 1, 1, 1, 1, 1, 1),
        (0, 0, 1, 1, 1, 1, 1, 1, 1, 1),
        (100, 0, 0, 100, 100, 100, 100, 100, 100, 1_000_000_000_000),
        (0, 100, 0, 100, 100, 100, 100, 100, 100, 1_000_000_000_000),
        (0, 0, 100, 100, 100, 100, 100, 100, 100, 1_000_000_000_000),
        (33, 33, 34, 50, 50, 50, 50, 50, 50, 500_000_000_000),
        (1, 1, 1, 1, 1, 1, 100, 100, 100, 1),
        (50, 25, 25, 1, 1, 1, 1, 1, 1, 1_000_000_000_000),
    ];
    for &(rb, rs, rc, sb, ss, sc, pb, ps, pc, m) in &seeds {
        for &mk in &mutation_kinds {
            let (a,b,c,d,e,f,g,h,i,j) = mutate(rb, rs, rc, sb, ss, sc, pb, ps, pc, m, mk);
            emit(a,b,c,d,e,f,g,h,i,j, &mut rng, &mut seen, &mut out, &mut count);
        }
    }

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let (rb, rs, rc) = random_recipe(&mut rng);
        let sb = rng.gen_range_i64(1, 100);
        let ss = rng.gen_range_i64(1, 100);
        let sc = rng.gen_range_i64(1, 100);
        let pb = rng.gen_range_i64(1, 100);
        let ps = rng.gen_range_i64(1, 100);
        let pc = rng.gen_range_i64(1, 100);
        let money = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_i64(1, 100),
            2 => rng.gen_range_i64(100, 10_000),
            3 => rng.gen_range_i64(10_000, 1_000_000_000),
            _ => rng.gen_range_i64(1_000_000_000, 1_000_000_000_000),
        };
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (a,b,c,d,e,f,g,h,i,j) = mutate(rb, rs, rc, sb, ss, sc, pb, ps, pc, money, mk);
        emit(a,b,c,d,e,f,g,h,i,j, &mut rng, &mut seen, &mut out, &mut count);
    }
}

