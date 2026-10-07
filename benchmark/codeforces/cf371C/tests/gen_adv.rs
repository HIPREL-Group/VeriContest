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
        ({
            let (rb, rs, rc, sb, ss, sc, pb, ps, pc, m) = result;
            &&& 0 <= rb <= 100
            &&& 0 <= rs <= 100
            &&& 0 <= rc <= 100
            &&& 1 <= rb + rs + rc <= 100
            &&& 1 <= sb <= 100
            &&& 1 <= ss <= 100
            &&& 1 <= sc <= 100
            &&& 1 <= pb <= 100
            &&& 1 <= ps <= 100
            &&& 1 <= pc <= 100
            &&& 1 <= m <= 1_000_000_000_000
        }),
{
    (recipe_b, recipe_s, recipe_c, stock_b, stock_s, stock_c, price_b, price_s, price_c, money)
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
    fn gen_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi - lo + 1) as u64;
        lo + (self.next_u64() % r) as i64
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

fn pick_recipe(rng: &mut Rng, mode: usize) -> (i64, i64, i64) {
    let mut tries = 0;
    loop {
        tries += 1;
        let (rb, rs, rc) = match mode {
            0 => (1i64, 0i64, 0i64),
            1 => (0i64, 0i64, 1i64),
            2 => (1i64, 1i64, 1i64),
            3 => (rng.gen_i64(0, 33), rng.gen_i64(0, 33), rng.gen_i64(0, 33)),
            4 => (rng.gen_i64(0, 50), rng.gen_i64(0, 50), 0i64),
            5 => {
                let a = rng.gen_i64(0, 50); let b = rng.gen_i64(0, 50);
                let c = 100 - a - b;
                if c < 0 { (a, b, 0i64) } else { (a, b, c) }
            }
            6 => (100i64, 0i64, 0i64),
            7 => (rng.gen_i64(0, 10), rng.gen_i64(0, 10), rng.gen_i64(0, 10)),
            _ => (rng.gen_i64(0, 20), rng.gen_i64(0, 20), rng.gen_i64(0, 20)),
        };
        let s = rb + rs + rc;
        if rb >= 0 && rb <= 100 && rs >= 0 && rs <= 100 && rc >= 0 && rc <= 100 && s >= 1 && s <= 100 {
            return (rb, rs, rc);
        }
        if tries > 100 { return (1, 1, 1); }
    }
}

fn pick_test(rng: &mut Rng, mode: usize) -> (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64) {
    let (rb, rs, rc) = pick_recipe(rng, mode % 9);
    let (sb, ss, sc) = match mode % 5 {
        0 => (1i64, 1i64, 1i64),
        1 => (100i64, 100i64, 100i64),
        2 => (rng.gen_i64(1, 100), rng.gen_i64(1, 100), rng.gen_i64(1, 100)),
        3 => (rng.gen_i64(1, 10), rng.gen_i64(1, 10), rng.gen_i64(1, 10)),
        _ => (rng.gen_i64(50, 100), rng.gen_i64(50, 100), rng.gen_i64(50, 100)),
    };
    let (pb, ps, pc) = match mode % 4 {
        0 => (1i64, 1i64, 1i64),
        1 => (100i64, 100i64, 100i64),
        2 => (rng.gen_i64(1, 100), rng.gen_i64(1, 100), rng.gen_i64(1, 100)),
        _ => (rng.gen_i64(1, 10), rng.gen_i64(1, 10), rng.gen_i64(1, 10)),
    };
    let money = match mode % 6 {
        0 => 1i64,
        1 => 1_000_000_000_000i64,
        2 => rng.gen_i64(1, 1000),
        3 => rng.gen_i64(1, 1_000_000),
        4 => rng.gen_i64(1, 1_000_000_000_000),
        _ => rng.gen_i64(1, 100_000),
    };
    (rb, rs, rc, sb, ss, sc, pb, ps, pc, money)
}

fn build_recipe_string(rb: i64, rs: i64, rc: i64, rng: &mut Rng) -> String {
    let mut chars: Vec<char> = Vec::new();
    for _ in 0..rb { chars.push('B'); }
    for _ in 0..rs { chars.push('S'); }
    for _ in 0..rc { chars.push('C'); }
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
    let target: usize = 200;
    let mut rng = Rng::new(1);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |t: (i64, i64, i64, i64, i64, i64, i64, i64, i64, i64), rng: &mut Rng, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let (rb, rs, rc, sb, ss, sc, pb, ps, pc, m) = t;
        if *count >= target { return; }
        if !(0 <= rb && rb <= 100 && 0 <= rs && rs <= 100 && 0 <= rc && rc <= 100) { return; }
        let sum = rb + rs + rc;
        if !(1 <= sum && sum <= 100) { return; }
        if !(1 <= sb && sb <= 100 && 1 <= ss && ss <= 100 && 1 <= sc && sc <= 100) { return; }
        if !(1 <= pb && pb <= 100 && 1 <= ps && ps <= 100 && 1 <= pc && pc <= 100) { return; }
        if !(1 <= m && m <= 1_000_000_000_000) { return; }
        let key = format!("{},{},{},{},{},{},{},{},{},{}", rb, rs, rc, sb, ss, sc, pb, ps, pc, m);
        if !seen.insert(key) { return; }
        let inp = build_input(rb, rs, rc, sb, ss, sc, pb, ps, pc, m, rng);
        let ans = Solution::max_hamburgers(rb, rs, rc, sb, ss, sc, pb, ps, pc, m);
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    let fixed: Vec<(i64, i64, i64, i64, i64, i64, i64, i64, i64, i64)> = vec![
        (1, 1, 1, 1, 1, 1, 1, 1, 1, 1),
        (1, 1, 1, 100, 100, 100, 1, 1, 1, 1_000_000_000_000),
        (100, 0, 0, 1, 1, 1, 100, 100, 100, 1_000_000_000_000),
        (1, 0, 0, 1, 1, 1, 1, 1, 1, 1),
        (0, 0, 1, 1, 1, 1, 100, 100, 100, 1),
        (33, 33, 34, 1, 1, 1, 100, 100, 100, 1_000_000_000_000),
        (1, 1, 1, 100, 100, 100, 100, 100, 100, 1_000_000_000_000),
        (50, 25, 25, 50, 25, 25, 1, 1, 1, 1),
        (1, 0, 0, 100, 1, 1, 1, 1, 1, 1),
        (100, 0, 0, 100, 100, 100, 100, 1, 1, 100),
    ];
    for &t in &fixed {
        emit(t, &mut rng, &mut seen, &mut out, &mut count);
    }

    let mut i = 0usize;
    while count < target {
        let mode = i % 10;
        let t = pick_test(&mut rng, mode);
        emit(t, &mut rng, &mut seen, &mut out, &mut count);
        i += 1;
        if i > 100000 { break; }
    }
}

