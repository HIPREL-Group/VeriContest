use vstd::prelude::*;

verus! {

pub fn generate_test_case(seed_x: i32, seed_y: i32, mutation_kind: u8) -> (result: (i32, i32))
    requires
        -50 <= seed_x <= 50,
        -50 <= seed_y <= 50,
    ensures
        -50 <= result.0 <= 50,
        -50 <= result.1 <= 50,
        !(result.0 == 0 && result.1 == 0),
{
    let x: i32;
    let y: i32;

    if mutation_kind == 0 {
        // identity
        x = seed_x;
        y = seed_y;
    } else if mutation_kind == 1 && seed_x < 50 {
        // nudge x up
        x = seed_x + 1;
        y = seed_y;
    } else if mutation_kind == 2 && seed_x > -50 {
        // nudge x down
        x = seed_x - 1;
        y = seed_y;
    } else if mutation_kind == 3 && seed_y < 50 {
        // nudge y up
        x = seed_x;
        y = seed_y + 1;
    } else if mutation_kind == 4 && seed_y > -50 {
        // nudge y down
        x = seed_x;
        y = seed_y - 1;
    } else if mutation_kind == 5 {
        // negate x
        x = -seed_x;
        y = seed_y;
    } else if mutation_kind == 6 {
        // negate y
        x = seed_x;
        y = -seed_y;
    } else if mutation_kind == 7 {
        // x boundary min
        x = -50;
        y = seed_y;
    } else if mutation_kind == 8 {
        // x boundary max
        x = 50;
        y = seed_y;
    } else if mutation_kind == 9 {
        // y boundary min
        x = seed_x;
        y = -50;
    } else if mutation_kind == 10 {
        // y boundary max
        x = seed_x;
        y = 50;
    } else if mutation_kind == 11 {
        // swap x and y
        x = seed_y;
        y = seed_x;
    } else if mutation_kind == 12 {
        // zero x
        x = 0;
        y = seed_y;
    } else if mutation_kind == 13 {
        // zero y
        x = seed_x;
        y = 0;
    } else {
        // fallback
        x = seed_x;
        y = seed_y;
    }

    // Fix (0, 0) case: shift y to 1
    if x == 0 && y == 0 {
        (x, 1i32)
    } else {
        (x, y)
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

fn build_input(coins: &[(i32, i32)]) -> String {
    let mut s = format!("{}\n", coins.len());
    for &(x, y) in coins {
        s.push_str(&format!("{} {}\n", x, y));
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

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // Example
    let example: Vec<(i32, i32)> = vec![(2, 4), (-2, -1), (-1, -2), (0, -5), (15, 0)];
    {
        let answers: Vec<bool> = example.iter().map(|&(x, y)| Solution::can_catch_coin(x, y)).collect();
        let inp = build_input(&example);
        let outp = build_output(&answers);
        let key = format!("{:?}", example);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // Tiny boundary tests as t=1 individual
    let single_seeds: Vec<(i32, i32)> = vec![
        (1, 1), (-1, -1), (0, -1), (0, -2), (50, 50), (-50, -50), (50, 0), (0, 50),
        (1, -1), (-1, 1), (1, -2), (10, -1), (10, -2),
    ];
    for &c in &single_seeds {
        if count >= target { break; }
        let coins = vec![c];
        let key = format!("{:?}", coins);
        if !seen.insert(key) { continue; }
        let answers: Vec<bool> = coins.iter().map(|&(x, y)| Solution::can_catch_coin(x, y)).collect();
        let inp = build_input(&coins);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let n: usize = if count < 30 { rng.gen_range_usize(1, 5) }
                       else if count < 60 { rng.gen_range_usize(2, 20) }
                       else { rng.gen_range_usize(5, 100) };
        let mut used: HashSet<(i32, i32)> = HashSet::new();
        let mut coins: Vec<(i32, i32)> = Vec::with_capacity(n);
        let mut tries = 0;
        while coins.len() < n && tries < n * 10 {
            tries += 1;
            let x = rng.gen_range_i64(-50, 50) as i32;
            let y = rng.gen_range_i64(-50, 50) as i32;
            if x == 0 && y == 0 { continue; }
            if !used.insert((x, y)) { continue; }
            coins.push((x, y));
        }
        if coins.is_empty() { continue; }
        let key = format!("{:?}", coins);
        if !seen.insert(key) { continue; }
        let answers: Vec<bool> = coins.iter().map(|&(x, y)| Solution::can_catch_coin(x, y)).collect();
        let inp = build_input(&coins);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

