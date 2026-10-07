use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_r: i128,
    seed_x: i128,
    seed_y: i128,
    seed_x2: i128,
    seed_y2: i128,
    mutation_kind: u8,
) -> (result: (i128, i128, i128, i128, i128))
    requires
        1 <= seed_r <= 100000,
        -100000 <= seed_x <= 100000,
        -100000 <= seed_y <= 100000,
        -100000 <= seed_x2 <= 100000,
        -100000 <= seed_y2 <= 100000,
    ensures
        1 <= result.0 <= 100000,
        -100000 <= result.1 <= 100000,
        -100000 <= result.2 <= 100000,
        -100000 <= result.3 <= 100000,
        -100000 <= result.4 <= 100000,
{
    let mut r = seed_r;
    let mut x = seed_x;
    let mut y = seed_y;
    let mut x2 = seed_x2;
    let mut y2 = seed_y2;

    if mutation_kind == 0 {
        // identity
    } else if mutation_kind == 1 && r < 100000 {
        r = r + 1;                              // nudge r up
    } else if mutation_kind == 2 && r > 1 {
        r = r - 1;                              // nudge r down
    } else if mutation_kind == 3 {
        r = 1;                                  // min r
    } else if mutation_kind == 4 {
        r = 100000;                             // max r
    } else if mutation_kind == 5 && r <= 50000 {
        r = r * 2;                              // double r
    } else if mutation_kind == 6 {
        r = r / 2 + 1;                          // halve r (stay >= 1)
    } else if mutation_kind == 7 && x < 100000 {
        x = x + 1;                              // nudge x up
    } else if mutation_kind == 8 && x > -100000 {
        x = x - 1;                              // nudge x down
    } else if mutation_kind == 9 && y < 100000 {
        y = y + 1;                              // nudge y up
    } else if mutation_kind == 10 && y > -100000 {
        y = y - 1;                              // nudge y down
    } else if mutation_kind == 11 && x2 < 100000 {
        x2 = x2 + 1;                            // nudge x2 up
    } else if mutation_kind == 12 && x2 > -100000 {
        x2 = x2 - 1;                            // nudge x2 down
    } else if mutation_kind == 13 && y2 < 100000 {
        y2 = y2 + 1;                            // nudge y2 up
    } else if mutation_kind == 14 && y2 > -100000 {
        y2 = y2 - 1;                            // nudge y2 down
    } else if mutation_kind == 15 {
        x2 = x;
        y2 = y;                                 // same point (distance 0)
    } else if mutation_kind == 16 {
        x = 0;
        y = 0;                                  // origin start
    } else if mutation_kind == 17 {
        x2 = 0;
        y2 = 0;                                 // origin target
    } else if mutation_kind == 18 {
        x = -100000;
        y = -100000;
        x2 = 100000;
        y2 = 100000;                            // max distance
    } else if mutation_kind == 19 {
        y = seed_x;
        x2 = seed_y;                            // swap some coords
    } else if mutation_kind == 20 {
        x = 0;
        y = 0;
        x2 = 0;
        y2 = 0;                                 // all zeros
    } else if mutation_kind == 21 {
        if seed_x >= -50000 && seed_x <= 50000 {
            x = seed_x * 2;                     // double x
        }
    } else if mutation_kind == 22 {
        if seed_x >= 0 { x = -seed_x; } else { x = seed_x; }  // negate x if possible
    } else {
        // fallback: identity
    }

    (r, x, y, x2, y2)
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
    let target_count: usize = 100;
    let mut rng = Rng::new(507);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |r: i128, x: i128, y: i128, x2: i128, y2: i128, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if r < 1 || r > 100_000 { return; }
        if x < -100_000 || x > 100_000 || y < -100_000 || y > 100_000 { return; }
        if x2 < -100_000 || x2 > 100_000 || y2 < -100_000 || y2 > 100_000 { return; }
        let key = format!("{}_{}_{}_{}_{}", r, x, y, x2, y2);
        if !seen.insert(key) { return; }
        let result = Solution::min_steps_to_target(r, x, y, x2, y2);
        let inp = format!("{} {} {} {} {}\n", r, x, y, x2, y2);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(2, 0, 0, 0, 4, &mut seen, &mut out, &mut count);
    emit(1, 1, 1, 4, 4, &mut seen, &mut out, &mut count);
    emit(4, 5, 6, 5, 6, &mut seen, &mut out, &mut count);

    // Edge
    emit(1, 0, 0, 0, 0, &mut seen, &mut out, &mut count);
    emit(1, 0, 0, 1, 0, &mut seen, &mut out, &mut count);
    emit(1, 0, 0, 2, 0, &mut seen, &mut out, &mut count);
    emit(100_000, 0, 0, 0, 0, &mut seen, &mut out, &mut count);
    emit(100_000, -100_000, -100_000, 100_000, 100_000, &mut seen, &mut out, &mut count);
    emit(1, -100_000, -100_000, 100_000, 100_000, &mut seen, &mut out, &mut count);

    while count < target_count {
        let r = rng.gen_range_i64(1, 100_000) as i128;
        let x = rng.gen_range_i64(-100_000, 100_000) as i128;
        let y = rng.gen_range_i64(-100_000, 100_000) as i128;
        let x2 = rng.gen_range_i64(-100_000, 100_000) as i128;
        let y2 = rng.gen_range_i64(-100_000, 100_000) as i128;
        emit(r, x, y, x2, y2, &mut seen, &mut out, &mut count);
    }
}

