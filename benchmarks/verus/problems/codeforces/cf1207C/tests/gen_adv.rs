use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<i32>, a: i64, b: i64) -> (result: (usize, i64, i64, Vec<i32>))
    ensures
        2 <= result.0 <= 200000,
        result.3.len() == result.0,
        1 <= result.1 <= 100000000,
        1 <= result.2 <= 100000000,
        forall|i: int| 0 <= i < result.3.len() ==> result.3[i] == 0 || result.3[i] == 1,
        result.3[0] == 0,
        result.3[result.0 as int - 1] == 0,
{
    let n = if raw.len() < 2 { 2usize } else if raw.len() > 200000 { 200000usize } else { raw.len() };
    let a = if a < 1 { 1 } else if a > 100000000 { 100000000 } else { a };
    let b = if b < 1 { 1 } else if b > 100000000 { 100000000 } else { b };
    let mut s: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            2 <= n <= 200000, 0 <= i <= n, s.len() == i,
            forall|j: int| 0 <= j < s.len() ==> s[j] == 0 || s[j] == 1,
        decreases n - i,
    {
        s.push(if i < raw.len() && raw[i] == 1 { 1 } else { 0 });
        i += 1;
    }
    s.set(0, 0);
    s.set(n - 1, 0);
    (n, a, b, s)
}


pub fn generate_candidate(
    n: usize,
    a: i64,
    b: i64,
    middle: &Vec<i32>,
) -> (res: (usize, i64, i64, Vec<i32>))
    requires
        2 <= n <= 200_000,
        1 <= a <= 100_000_000,
        1 <= b <= 100_000_000,
        middle.len() + 2 == n,
        forall|i: int| 0 <= i < middle.len() ==> (#[trigger] middle[i] == 0 || middle[i] == 1),
    ensures
        ({
            let (rn, ra, rb, rs) = res;
            &&& rn == n
            &&& ra == a
            &&& rb == b
            &&& rs.len() == n
            &&& 2 <= rn <= 200_000
            &&& 1 <= ra <= 100_000_000
            &&& 1 <= rb <= 100_000_000
            &&& (forall|j: int|
                #![trigger rs@[j]]
                0 <= j && j < n as int ==> (rs@[j] == 0 || rs@[j] == 1))
            &&& rs@[0] == 0
            &&& rs@[n as int - 1] == 0
        }),
{
    let mut s: Vec<i32> = Vec::new();
    s.push(0i32);
    let mut i: usize = 0;
    while i < middle.len()
        invariant
            0 <= i <= middle.len(),
            s.len() == i + 1,
            s@[0] == 0,
            forall|k: int| 0 <= k < i as int ==> #[trigger] s@[k + 1] == middle@[k],
            forall|k: int| 0 <= k < middle.len() ==> (#[trigger] middle[k] == 0 || middle[k] == 1),
        decreases middle.len() - i,
    {
        s.push(middle[i]);
        i = i + 1;
    }
    s.push(0i32);

    assert(s.len() == n);
    assert(s@[0] == 0);
    assert(s@[n as int - 1] == 0);

    assert forall|j: int|
        0 <= j && j < n as int implies (#[trigger] s@[j] == 0 || s@[j] == 1)
    by {
        if j == 0 {
            assert(s@[j] == 0);
        } else if j == n as int - 1 {
            assert(s@[j] == 0);
        } else {
            let k = j - 1;
            assert(0 <= k < middle.len());
            assert(s@[k + 1] == middle@[k]);
            assert(middle@[k] == 0 || middle@[k] == 1);
        }
    }

    (n, a, b, s)
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

fn build_input(cases: &[(usize, i64, i64, String)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, a, b, st) in cases {
        s.push_str(&format!("{} {} {}\n", n, a, b));
        s.push_str(st);
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for x in answers { s.push_str(&format!("{}\n", x)); }
    s
}

fn solve_one(n: usize, a: i64, b: i64, s: &str) -> i64 {
    let v: Vec<i32> = s.chars().map(|c| if c == '1' { 1 } else { 0 }).collect();
    Solution::gas_pipeline(n, a, b, v)
}

fn make_random_str(rng: &mut Rng, n: usize, prob_mod: usize) -> String {
    let chars: Vec<char> = (0..n).map(|i| {
        if i == 0 || i == n - 1 { '0' }
        else if (rng.gen_range_i64(0, prob_mod as i64 - 1) as usize) > 0 { '0' } else { '1' }
    }).collect();
    chars.into_iter().collect()
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(987654321);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<(usize, i64, i64, String)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let cases: Vec<_> = cases.into_iter().map(|(_, a, b, text)| {
            let raw = text.bytes().map(|c| if c == b'1' { 1 } else { 0 }).collect();
            let (n, a, b, bits) = generate_test_case(raw, a, b);
            let text: String = bits.iter().map(|&v| if v == 0 { '0' } else { '1' }).collect();
            (n, a, b, text)
        }).collect();
        if *count >= target { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for (n, a, b, s) in &cases {
            h ^= *n as u64; h = h.wrapping_mul(1099511628211);
            h ^= *a as u64; h = h.wrapping_mul(1099511628211);
            h ^= *b as u64; h = h.wrapping_mul(1099511628211);
            for c in s.chars() { h ^= c as u64; h = h.wrapping_mul(1099511628211); }
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i64> = cases.iter().map(|(n, a, b, s)| solve_one(*n, *a, *b, s)).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Boundary cases
    let mut large_zeros = String::from("0");
    let mut large_alt = String::from("0");
    let mut large_block = String::from("0");
    for i in 1..200_000 {
        large_zeros.push('0');
        large_alt.push(if i % 2 == 0 { '0' } else { '1' });
        large_block.push(if i < 100_000 { '0' } else if i + 1 == 200_000 { '0' } else { '1' });
    }
    large_zeros.push('0');
    large_alt.push('0');
    large_block.push('0');

    // single-large-string cases
    for s in &[&large_zeros, &large_alt, &large_block] {
        let cases = vec![(s.len(), 100_000_000i64, 100_000_000i64, s.to_string())];
        emit(cases, &mut seen, &mut out, &mut count);
    }

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 5),
        };
        let mut cases: Vec<(usize, i64, i64, String)> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            if total_n >= 150_000 { break; }
            let max_n = (200_000 - total_n).min(50_000);
            let n = match tries % 6 {
                0 => rng.gen_range_usize(2, 5),
                1 => rng.gen_range_usize(5, 50),
                2 => rng.gen_range_usize(50, 500),
                3 => rng.gen_range_usize(500, 5_000),
                4 => rng.gen_range_usize(5_000, max_n.max(5_000)),
                _ => rng.gen_range_usize(2, 100),
            };
            total_n += n;
            let a = match tries % 3 {
                0 => 1i64,
                1 => rng.gen_range_i64(1, 1000),
                _ => rng.gen_range_i64(1, 100_000_000),
            };
            let b = match tries % 3 {
                0 => 100_000_000i64,
                1 => rng.gen_range_i64(1, 1000),
                _ => rng.gen_range_i64(1, 100_000_000),
            };
            let prob_mod = match tries % 4 { 0 => 2usize, 1 => 3, 2 => 5, _ => 10 };
            let s = make_random_str(&mut rng, n, prob_mod);
            cases.push((n, a, b, s));
        }
        if !cases.is_empty() {
            emit(cases, &mut seen, &mut out, &mut count);
        }
    }
}
