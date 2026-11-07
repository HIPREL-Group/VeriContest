use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_in: i64, m_in: i64) -> (res: (i64, i64))
    ensures
        1 <= res.0 <= 10000000,
        1 <= res.1 <= 10000000,
{
    let n_in = if n_in < 1 { 1 } else if n_in > 10000000 { 10000000 } else { n_in };
    let m_in = if m_in < 1 { 1 } else if m_in > 10000000 { 10000000 } else { m_in };
    (n_in, m_in)
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

fn solve(n: i64, m: i64) -> bool {
    Solution::can_obtain(m, n)
}

fn build_input(cases: &[(i64, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for &(n, m) in cases {
        s.push_str(&format!("{} {}\n", n, m));
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(if a {"YES\n"} else {"NO\n"});
    }
    s
}

fn pick_adv(rng: &mut Rng) -> (i64, i64) {
    match rng.next_u64() % 9 {
        0 => {
            // n = 3^k where k is high
            let mut n = 1i64;
            let k = rng.gen_range_i64(15, 18);
            for _ in 0..k { n *= 3; }
            // m = a power-of-2 * power-of-3 that's reachable
            let mut m = n;
            let depth = rng.gen_range_i64(0, k);
            for _ in 0..depth {
                if m % 3 == 0 {
                    if rng.next_u64() % 2 == 0 { m = m / 3; } else { m = 2 * m / 3; }
                }
            }
            (n, m)
        }
        1 => {
            // Definitely YES (m = n / 3 or 2n/3)
            let mut n = 1i64;
            let k = rng.gen_range_i64(2, 18);
            for _ in 0..k { n *= 3; }
            let m = if rng.next_u64() % 2 == 0 { n / 3 } else { 2 * n / 3 };
            (n, m)
        }
        2 => {
            // n not divisible by 3, m != n -> NO
            let n = rng.gen_range_i64(1, 1_000_000_000);
            let n = if n % 3 == 0 { n + 1 } else { n };
            let m = if n > 1 { n - 1 } else { 2 };
            (n, m)
        }
        3 => (rng.gen_range_i64(1, 1_000_000_000), rng.gen_range_i64(1, 1_000_000_000)),
        4 => {
            // m > n -> NO except m=n
            let n = rng.gen_range_i64(1, 100);
            let m = rng.gen_range_i64(n + 1, 1_000_000_000);
            (n, m)
        }
        5 => (1, 1),
        6 => (1_000_000_000, 1_000_000_000),
        7 => {
            let v = rng.gen_range_i64(1, 1_000_000_000);
            (v, v)
        }
        _ => {
            // 3^k * 2^j combos for n=3^k
            let k = rng.gen_range_i64(5, 18);
            let mut n = 1i64;
            for _ in 0..k { n *= 3; }
            let m = rng.gen_range_i64(1, n);
            (n, m)
        }
    }
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31415);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Big single-cases
    let big_singles: Vec<(i64, i64)> = vec![
        (387_420_489, 1),         // 3^18, target=1: yes
        (387_420_489, 387_420_488),  // -1: probably no
        (387_420_489, 129_140_163),  // 3^18 / 3 = 3^17: yes
        (1_000_000_000, 1_000_000_000),
        (999_999_999, 333_333_333),
    ];
    for &c in &big_singles {
        if count >= target { break; }
        let cases = vec![c];
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| solve(n, m)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(10, 30) } else { rng.gen_range_usize(20, 50) };
        let mut cases: Vec<(i64, i64)> = Vec::new();
        for _ in 0..t {
            cases.push(pick_adv(&mut rng));
        }
        let cases: Vec<_> = cases.into_iter()
            .map(|c| generate_test_case(c.0, c.1)).collect();
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|&(n, m)| solve(n, m)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}
