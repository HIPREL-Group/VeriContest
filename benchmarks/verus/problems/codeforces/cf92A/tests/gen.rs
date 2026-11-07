use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_seed: u32, m_seed: u32, mutation_kind: u8) -> (result: (u32, u32))
    requires
        1 <= n_seed <= 50,
        1 <= m_seed <= 10000,
    ensures
        1 <= result.0 <= 50,
        1 <= result.1 <= 10000,
{
    if mutation_kind == 0 {
        (n_seed, m_seed)
    } else if mutation_kind == 1 {
        (1, m_seed)
    } else if mutation_kind == 2 {
        (50, m_seed)
    } else if mutation_kind == 3 {
        (n_seed, 1)
    } else if mutation_kind == 4 {
        (n_seed, 10000)
    } else {
        (n_seed, m_seed)
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
    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        lo + (self.next_u64() as u32) % (hi - lo + 1)
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
    let mut rng = Rng::new(92);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<(u32, u32)> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: u32, m: u32, seen: &mut HashSet<(u32, u32)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if !(1 <= n && n <= 50 && 1 <= m && m <= 10000) { return; }
        if !seen.insert((n, m)) { return; }
        let result = Solution::presenter_chips(n, m);
        let inp = format!("{} {}\n", n, m);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // examples
    emit(4, 11, &mut seen, &mut out, &mut count);
    emit(17, 107, &mut seen, &mut out, &mut count);
    emit(3, 8, &mut seen, &mut out, &mut count);

    // edge cases
    for n in 1..=10 {
        for m in 1..=20 {
            emit(n, m, &mut seen, &mut out, &mut count);
        }
    }

    while count < target_count {
        let n = rng.gen_range_u32(1, 50);
        let m = rng.gen_range_u32(1, 10000);
        emit(n, m, &mut seen, &mut out, &mut count);
    }
}
