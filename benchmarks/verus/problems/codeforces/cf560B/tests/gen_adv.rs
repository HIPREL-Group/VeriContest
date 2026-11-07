use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a1: i32,
    b1: i32,
    a2: i32,
    b2: i32,
    a3: i32,
    b3: i32,
) -> (res: (i32, i32, i32, i32, i32, i32))
    requires
        1 <= a1 <= 1000,
        1 <= b1 <= 1000,
        1 <= a2 <= 1000,
        1 <= b2 <= 1000,
        1 <= a3 <= 1000,
        1 <= b3 <= 1000,
    ensures
        ({
            let (x1, y1, x2, y2, x3, y3) = res;
            1 <= x1 <= 1000 && 1 <= y1 <= 1000
            && 1 <= x2 <= 1000 && 1 <= y2 <= 1000
            && 1 <= x3 <= 1000 && 1 <= y3 <= 1000
        }),
{
    (a1, b1, a2, b2, a3, b3)
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(56006);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |a1: i32, b1: i32, a2: i32, b2: i32, a3: i32, b3: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        for v in [a1, b1, a2, b2, a3, b3].iter() {
            if *v < 1 || *v > 1000 { return; }
        }
        let key = format!("{}_{}_{}_{}_{}_{}", a1, b1, a2, b2, a3, b3);
        if !seen.insert(key) { return; }
        let result = Solution::can_place_paintings(a1, b1, a2, b2, a3, b3);
        let inp = format!("{} {}\n{} {}\n{} {}\n", a1, b1, a2, b2, a3, b3);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: extreme sizes
    emit(1000, 1000, 1000, 1000, 1, 1, &mut seen, &mut out, &mut count);
    emit(1000, 1000, 999, 999, 1, 1, &mut seen, &mut out, &mut count);
    emit(1000, 1000, 500, 500, 500, 500, &mut seen, &mut out, &mut count);
    emit(2, 1000, 1000, 1, 1000, 1, &mut seen, &mut out, &mut count);
    emit(1000, 2, 1, 1000, 1, 1000, &mut seen, &mut out, &mut count);
    emit(1, 1, 2, 2, 2, 2, &mut seen, &mut out, &mut count);

    // Boundaries: exact fits
    for n in [1, 2, 3, 5, 10, 100, 500, 1000].iter() {
        emit(*n, *n, *n / 2, *n, (*n + 1) / 2, *n, &mut seen, &mut out, &mut count);
        emit(*n, *n, *n, *n / 2, *n, (*n + 1) / 2, &mut seen, &mut out, &mut count);
        if *n >= 2 {
            emit(*n, *n, 1, 1, 1, 1, &mut seen, &mut out, &mut count);
            emit(*n, *n, *n / 2, *n / 2, *n / 2, *n / 2, &mut seen, &mut out, &mut count);
        }
    }

    // Random
    while count < target_count {
        let style = count % 3;
        let (a1, b1, a2, b2, a3, b3) = match style {
            0 => {
                // random small values
                (rng.gen_range_i64(1, 50) as i32,
                 rng.gen_range_i64(1, 50) as i32,
                 rng.gen_range_i64(1, 50) as i32,
                 rng.gen_range_i64(1, 50) as i32,
                 rng.gen_range_i64(1, 50) as i32,
                 rng.gen_range_i64(1, 50) as i32)
            }
            1 => {
                // random large values
                (rng.gen_range_i64(1, 1000) as i32,
                 rng.gen_range_i64(1, 1000) as i32,
                 rng.gen_range_i64(1, 1000) as i32,
                 rng.gen_range_i64(1, 1000) as i32,
                 rng.gen_range_i64(1, 1000) as i32,
                 rng.gen_range_i64(1, 1000) as i32)
            }
            _ => {
                // tight cases: paintings nearly fit board
                let board_a = rng.gen_range_i64(50, 1000) as i32;
                let board_b = rng.gen_range_i64(50, 1000) as i32;
                let split = rng.gen_range_i64(1, board_a as i64 - 1) as i32;
                let a2 = split;
                let a3 = board_a - split;
                let b2 = rng.gen_range_i64(1, board_b as i64) as i32;
                let b3 = rng.gen_range_i64(1, board_b as i64) as i32;
                (board_a, board_b, a2, b2, a3, b3)
            }
        };
        emit(a1, b1, a2, b2, a3, b3, &mut seen, &mut out, &mut count);
    }
}

