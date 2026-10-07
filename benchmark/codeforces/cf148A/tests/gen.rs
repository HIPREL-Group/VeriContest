use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    k_seed: i32,
    l_seed: i32,
    m_seed: i32,
    n_seed: i32,
    d_seed: i32,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32, i32))
    requires
        1 <= k_seed <= 10,
        1 <= l_seed <= 10,
        1 <= m_seed <= 10,
        1 <= n_seed <= 10,
        1 <= d_seed <= 100_000,
    ensures
        1 <= result.0 <= 10,
        1 <= result.1 <= 10,
        1 <= result.2 <= 10,
        1 <= result.3 <= 10,
        1 <= result.4 <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (k_seed, l_seed, m_seed, n_seed, d_seed)
    } else if mutation_kind == 1 && k_seed < 10 {
        // nudge k up
        (k_seed + 1, l_seed, m_seed, n_seed, d_seed)
    } else if mutation_kind == 2 && k_seed > 1 {
        // nudge k down
        (k_seed - 1, l_seed, m_seed, n_seed, d_seed)
    } else if mutation_kind == 3 && l_seed < 10 {
        // nudge l up
        (k_seed, l_seed + 1, m_seed, n_seed, d_seed)
    } else if mutation_kind == 4 && l_seed > 1 {
        // nudge l down
        (k_seed, l_seed - 1, m_seed, n_seed, d_seed)
    } else if mutation_kind == 5 && m_seed < 10 {
        // nudge m up
        (k_seed, l_seed, m_seed + 1, n_seed, d_seed)
    } else if mutation_kind == 6 && m_seed > 1 {
        // nudge m down
        (k_seed, l_seed, m_seed - 1, n_seed, d_seed)
    } else if mutation_kind == 7 && n_seed < 10 {
        // nudge n up
        (k_seed, l_seed, m_seed, n_seed + 1, d_seed)
    } else if mutation_kind == 8 && n_seed > 1 {
        // nudge n down
        (k_seed, l_seed, m_seed, n_seed - 1, d_seed)
    } else if mutation_kind == 9 && d_seed < 100_000 {
        // nudge d up
        (k_seed, l_seed, m_seed, n_seed, d_seed + 1)
    } else if mutation_kind == 10 && d_seed > 1 {
        // nudge d down
        (k_seed, l_seed, m_seed, n_seed, d_seed - 1)
    } else if mutation_kind == 11 {
        // all params at min boundary
        (1, 1, 1, 1, 1)
    } else if mutation_kind == 12 {
        // all params at max boundary
        (10, 10, 10, 10, 100_000)
    } else if mutation_kind == 13 {
        // k=1 means every dragon is damaged
        (1, l_seed, m_seed, n_seed, d_seed)
    } else if mutation_kind == 14 {
        // all divisors equal
        (k_seed, k_seed, k_seed, k_seed, d_seed)
    } else if mutation_kind == 15 && d_seed >= 1 && d_seed <= 99_999 {
        // double d (clamped)
        let d2: i32 = if d_seed <= 50_000 { d_seed * 2 } else { 100_000 };
        (k_seed, l_seed, m_seed, n_seed, d2)
    } else if mutation_kind == 16 {
        // halve d
        let d2: i32 = if d_seed / 2 >= 1 { d_seed / 2 } else { 1 };
        (k_seed, l_seed, m_seed, n_seed, d2)
    } else if mutation_kind == 17 {
        // swap k and l
        (l_seed, k_seed, m_seed, n_seed, d_seed)
    } else if mutation_kind == 18 {
        // d = 1
        (k_seed, l_seed, m_seed, n_seed, 1)
    } else {
        // fallback: identity
        (k_seed, l_seed, m_seed, n_seed, d_seed)
    }
}

}

use std::io::Write;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

fn build_input(k: i32, l: i32, m: i32, n: i32, d: i32) -> String {
    format!("{}\n{}\n{}\n{}\n{}\n", k, l, m, n, d)
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut emit = |k: i32, l: i32, m: i32, n: i32, d: i32, out: &mut std::io::BufWriter<std::fs::File>| {
        let ans = Solution::count_damaged(k, l, m, n, d);
        let inp = build_input(k, l, m, n, d);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    };

    // Examples
    emit(1, 2, 3, 4, 12, &mut out);
    emit(2, 3, 4, 5, 24, &mut out);

    // Edge cases
    emit(1, 1, 1, 1, 1, &mut out);
    emit(10, 10, 10, 10, 1, &mut out);
    emit(10, 10, 10, 10, 100000, &mut out);
    emit(1, 1, 1, 1, 100000, &mut out);
    emit(2, 4, 6, 8, 50, &mut out);

    let mut count = 7usize;
    while count < target {
        let k = rng.gen_range_i32(1, 10);
        let l = rng.gen_range_i32(1, 10);
        let m = rng.gen_range_i32(1, 10);
        let n = rng.gen_range_i32(1, 10);
        let d = match rng.next_u64() % 4 {
            0 => rng.gen_range_i32(1, 100),
            1 => rng.gen_range_i32(1, 1000),
            2 => rng.gen_range_i32(1, 10000),
            _ => rng.gen_range_i32(1, 100000),
        };
        emit(k, l, m, n, d, &mut out);
        count += 1;
    }
}

