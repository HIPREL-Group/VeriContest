use vstd::prelude::*;

verus! {

// Two-parameter scalar generator for construct_game(n, s).
// spec.rs requires: 1 <= n <= s <= 1_000_000
pub fn generate_test_case(n_seed: i64, s_seed: i64, mutation_kind: u8) -> (result: (i64, i64))
    requires
        1 <= n_seed <= 1_000_000i64,
        n_seed <= s_seed <= 1_000_000i64,
    ensures
        1 <= result.0 <= result.1 <= 1_000_000i64,
{
    if mutation_kind == 0 {
        // identity
        (n_seed, s_seed)
    } else if mutation_kind == 1 && n_seed < s_seed {
        // nudge n up
        (n_seed + 1, s_seed)
    } else if mutation_kind == 2 && n_seed > 1 {
        // nudge n down
        (n_seed - 1, s_seed)
    } else if mutation_kind == 3 && s_seed < 1_000_000 {
        // nudge s up
        (n_seed, s_seed + 1)
    } else if mutation_kind == 4 && s_seed > n_seed {
        // nudge s down
        (n_seed, s_seed - 1)
    } else if mutation_kind == 5 {
        // set n = 1 (minimum n)
        (1, s_seed)
    } else if mutation_kind == 6 {
        // set s = 1_000_000 (maximum s)
        (n_seed, 1_000_000)
    } else if mutation_kind == 7 {
        // set n = s (equal)
        (s_seed, s_seed)
    } else if mutation_kind == 8 {
        // minimum both
        (1, 1)
    } else if mutation_kind == 9 {
        // max range
        (1, 1_000_000)
    } else if mutation_kind == 10 {
        // halve n (keep >= 1)
        let half_n = n_seed / 2;
        if half_n >= 1 {
            (half_n, s_seed)
        } else {
            (1, s_seed)
        }
    } else if mutation_kind == 11 {
        // double n (keep <= s)
        if n_seed <= 500_000 && n_seed * 2 <= s_seed {
            (n_seed * 2, s_seed)
        } else {
            (n_seed, s_seed)
        }
    } else {
        // fallback: identity
        (n_seed, s_seed)
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
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

fn build_input(n: i64, s: i64) -> String {
    format!("{} {}\n", n, s)
}

fn build_output(r: &Option<(Vec<i64>, i64)>) -> String {
    match r {
        None => "NO\n".to_string(),
        Some((a, k)) => {
            let mut out = String::from("YES\n");
            let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
            out.push_str(&parts.join(" "));
            out.push('\n');
            out.push_str(&format!("{}\n", k));
            out
        }
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut emit = |n: i64, s: i64, out: &mut std::io::BufWriter<std::fs::File>| {
        let r = Solution::construct_game(n, s);
        let inp = build_input(n, s);
        let outp = build_output(&r);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    };

    // Examples
    emit(1, 4, &mut out);
    emit(3, 4, &mut out);
    emit(3, 8, &mut out);

    // Edge cases
    let edges: Vec<(i64, i64)> = vec![
        (1, 1), (1, 2), (2, 2), (2, 3), (2, 4), (5, 5), (5, 9), (5, 10), (5, 11),
        (1, 1_000_000), (1_000_000, 1_000_000), (500_000, 1_000_000),
        (1, 100), (100, 200),
    ];
    for (n, s) in edges {
        emit(n, s, &mut out);
    }

    let mut count = 17usize;
    while count < target {
        // generate n, s with 1 <= n <= s <= 1_000_000
        let mode = rng.next_u64() % 5;
        let (n, s): (i64, i64) = match mode {
            0 => {
                let n = rng.gen_range_i64(1, 10);
                let s = rng.gen_range_i64(n, n + 10);
                (n, s)
            }
            1 => {
                let n = rng.gen_range_i64(1, 100);
                let s = rng.gen_range_i64(n, n.saturating_mul(3));
                (n, s)
            }
            2 => {
                let n = rng.gen_range_i64(1, 1000);
                let s = rng.gen_range_i64(n, n.saturating_mul(5).min(1_000_000));
                (n, s)
            }
            3 => {
                let n = rng.gen_range_i64(1, 1_000_000);
                let s = rng.gen_range_i64(n, 1_000_000);
                (n, s)
            }
            _ => {
                let n = rng.gen_range_i64(1, 100_000);
                let s = n + rng.gen_range_i64(0, n - 1).max(0);
                (n, s)
            }
        };
        emit(n, s, &mut out);
        count += 1;
    }
}

