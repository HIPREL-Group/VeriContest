use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    h_c_seed: i64,
    d_c_seed: i64,
    h_m_seed: i64,
    d_m_seed: i64,
    k_seed: i32,
    w_seed: i32,
    a_seed: i64,
    mutation_kind: u8,
) -> (result: (i64, i64, i64, i64, i32, i32, i64))
    requires
        1 <= h_c_seed <= 1_000_000_000_000_000,
        1 <= d_c_seed <= 1_000_000_000,
        1 <= h_m_seed <= 1_000_000_000_000_000,
        1 <= d_m_seed <= 1_000_000_000,
        0 <= k_seed <= 200_000,
        0 <= w_seed <= 10_000,
        0 <= a_seed <= 10_000_000_000,
    ensures
        1 <= result.0 <= 1_000_000_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000_000_000,
        1 <= result.3 <= 1_000_000_000,
        0 <= result.4 <= 200_000,
        0 <= result.5 <= 10_000,
        0 <= result.6 <= 10_000_000_000,
{
    if mutation_kind == 0 {
        (h_c_seed, d_c_seed, h_m_seed, d_m_seed, k_seed, w_seed, a_seed)
    } else if mutation_kind == 1 && h_c_seed < 1_000_000_000_000_000 {
        (h_c_seed + 1, d_c_seed, h_m_seed, d_m_seed, k_seed, w_seed, a_seed)
    } else if mutation_kind == 2 && h_c_seed > 1 {
        (h_c_seed - 1, d_c_seed, h_m_seed, d_m_seed, k_seed, w_seed, a_seed)
    } else if mutation_kind == 3 {
        (h_c_seed, d_c_seed, h_m_seed, d_m_seed, 0, w_seed, a_seed)
    } else if mutation_kind == 4 {
        (h_c_seed, d_c_seed, h_m_seed, d_m_seed, k_seed, 0, 0)
    } else if mutation_kind == 5 {
        (1, d_c_seed, 1_000_000_000_000_000, d_m_seed, k_seed, w_seed, a_seed)
    } else if mutation_kind == 6 {
        (1_000_000_000_000_000, d_c_seed, 1, d_m_seed, k_seed, w_seed, a_seed)
    } else if mutation_kind == 7 {
        (h_c_seed, 1_000_000_000, h_m_seed, d_m_seed, k_seed, w_seed, a_seed)
    } else if mutation_kind == 8 {
        (h_c_seed, d_c_seed, h_m_seed, 1_000_000_000, k_seed, w_seed, a_seed)
    } else if mutation_kind == 9 {
        (h_c_seed, d_c_seed, h_m_seed, d_m_seed, 200_000, 10_000, a_seed)
    } else if mutation_kind == 10 {
        (h_c_seed, d_c_seed, h_m_seed, d_m_seed, 200_000, w_seed, 10_000_000_000)
    } else if mutation_kind == 11 && d_c_seed < 1_000_000_000 {
        (h_c_seed, d_c_seed + 1, h_m_seed, d_m_seed, k_seed, w_seed, a_seed)
    } else if mutation_kind == 12 && d_m_seed > 1 {
        (h_c_seed, d_c_seed, h_m_seed, d_m_seed - 1, k_seed, w_seed, a_seed)
    } else if mutation_kind == 13 {
        (1, 1, 1, 1, 0, 0, 0)
    } else if mutation_kind == 14 {
        (
            1_000_000_000_000_000,
            1_000_000_000,
            1_000_000_000_000_000,
            1_000_000_000,
            200_000,
            10_000,
            10_000_000_000,
        )
    } else {
        (h_c_seed, d_c_seed, h_m_seed, d_m_seed, k_seed, w_seed, a_seed)
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

#[derive(Clone)]
struct Case { hc: i64, dc: i64, hm: i64, dm: i64, k: i32, w: i32, a: i64 }

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for c in cases {
        s.push_str(&format!("{} {}\n{} {}\n{} {} {}\n", c.hc, c.dc, c.hm, c.dm, c.k, c.w, c.a));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &b in answers { s.push_str(if b { "YES\n" } else { "NO\n" }); }
    s
}

fn make_test(rng: &mut Rng, mode: usize) -> Case {
    match mode {
        0 => Case { hc: 1, dc: 1, hm: 1, dm: 1, k: 0, w: 0, a: 0 },
        1 => Case { hc: 1, dc: 1_000_000_000, hm: 1, dm: 1, k: 0, w: 0, a: 0 },
        2 => Case { hc: 1, dc: 1, hm: 1_000_000_000, dm: 1, k: 0, w: 0, a: 0 },
        3 => Case {
            hc: rng.gen_range_i64(1, 100),
            dc: rng.gen_range_i64(1, 100),
            hm: rng.gen_range_i64(1, 100),
            dm: rng.gen_range_i64(1, 100),
            k: rng.gen_range_i64(0, 20) as i32,
            w: rng.gen_range_i64(0, 100) as i32,
            a: rng.gen_range_i64(0, 100),
        },
        4 => Case {
            hc: rng.gen_range_i64(1, 1_000_000_000),
            dc: rng.gen_range_i64(1, 1_000_000),
            hm: rng.gen_range_i64(1, 1_000_000_000),
            dm: rng.gen_range_i64(1, 1_000_000),
            k: 0, w: 0, a: 0,
        },
        5 => Case {
            hc: rng.gen_range_i64(1, 1000),
            dc: rng.gen_range_i64(1, 1000),
            hm: rng.gen_range_i64(1, 1000),
            dm: rng.gen_range_i64(1, 1000),
            k: 200, w: rng.gen_range_i64(0, 1000) as i32, a: rng.gen_range_i64(0, 1000),
        },
        6 => Case {
            hc: 1_000_000_000_000_000,
            dc: 1, hm: 1_000_000_000_000_000, dm: 1,
            k: 0, w: 0, a: 0,
        },
        7 => Case {
            hc: rng.gen_range_i64(1, 1_000_000_000),
            dc: rng.gen_range_i64(1, 1_000_000_000),
            hm: rng.gen_range_i64(1, 1_000_000_000),
            dm: rng.gen_range_i64(1, 1_000_000_000),
            k: rng.gen_range_i64(0, 100) as i32,
            w: rng.gen_range_i64(0, 10000) as i32,
            a: rng.gen_range_i64(0, 10_000_000_000),
        },
        8 => Case {
            hc: rng.gen_range_i64(1, 100),
            dc: 1,
            hm: rng.gen_range_i64(1, 100),
            dm: 1,
            k: rng.gen_range_i64(0, 50) as i32,
            w: 1, a: 1,
        },
        9 => Case {
            hc: rng.gen_range_i64(1, 1000),
            dc: rng.gen_range_i64(1, 1000),
            hm: rng.gen_range_i64(1, 1000),
            dm: rng.gen_range_i64(1, 1000),
            k: rng.gen_range_i64(0, 30) as i32,
            w: rng.gen_range_i64(0, 100) as i32,
            a: rng.gen_range_i64(0, 100),
        },
        _ => Case {
            hc: rng.gen_range_i64(1, 1_000_000),
            dc: rng.gen_range_i64(1, 1_000_000),
            hm: rng.gen_range_i64(1, 1_000_000),
            dm: rng.gen_range_i64(1, 1_000_000),
            k: rng.gen_range_i64(0, 50) as i32,
            w: rng.gen_range_i64(0, 1000) as i32,
            a: rng.gen_range_i64(0, 1_000_000),
        },
    }
}

fn main() {
    let mut rng = Rng::new(1);
    let modes = 10usize;
    let total = 200usize;

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;
    let mut idx = 0;
    while count < total {
        let t: usize = if count < 10 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            let mode = idx % modes;
            idx += 1;
            cases.push(make_test(&mut rng, mode));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|c| Solution::can_slay_monster(c.hc, c.dc, c.hm, c.dm, c.k, c.w, c.a)).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

