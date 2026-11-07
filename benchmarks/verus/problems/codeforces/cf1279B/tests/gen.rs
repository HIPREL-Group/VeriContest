use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i64>,
    s: i64,
    mutation_kind: u8,
) -> (result: (usize, i64, Vec<i64>))
    requires
        1 <= a.len() <= 100000,
        forall|i: int|
            #![trigger a[i]]
            0 <= i && i < a.len() ==> 1 <= a[i] && a[i] <= 1000000000,
        1 <= s <= 1000000000,
    ensures
        1 <= result.0 <= 100000,
        result.2.len() == result.0,
        forall|i: int|
            #![trigger result.2[i]]
            0 <= i && i < result.0 ==> 1 <= result.2[i] && result.2[i] <= 1000000000,
        1 <= result.1 <= 1000000000,
{
    let n = a.len();
    if mutation_kind == 0 {
        // identity
        (n, s, a)
    } else if mutation_kind == 1 {
        // set first element to 1 (min value)
        let mut d = a;
        d.set(0, 1);
        (n, s, d)
    } else if mutation_kind == 2 {
        // set first element to 1000000000 (max value)
        let mut d = a;
        d.set(0, 1000000000);
        (n, s, d)
    } else if mutation_kind == 3 {
        // set s to 1 (min s — forces overflow early)
        (n, 1, a)
    } else if mutation_kind == 4 {
        // set s to 1000000000 (max s — likely no skip)
        (n, 1000000000, a)
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut d = a;
        d.set(n - 1, 1);
        (n, s, d)
    } else if mutation_kind == 6 {
        // set last element to 1000000000
        let mut d = a;
        d.set(n - 1, 1000000000);
        (n, s, d)
    } else if mutation_kind == 7 && a[0] < 1000000000 {
        // nudge first element up
        let mut d = a;
        d.set(0, d[0] + 1);
        (n, s, d)
    } else if mutation_kind == 8 && a[0] > 1 {
        // nudge first element down
        let mut d = a;
        d.set(0, d[0] - 1);
        (n, s, d)
    } else {
        // fallback: identity
        (n, s, a)
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

fn build_input(cases: &[(i64, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (sv, a) in cases {
        s.push_str(&format!("{} {}\n", a.len(), sv));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_array(rng: &mut Rng, len: usize, max_val: i64) -> Vec<i64> {
    (0..len).map(|_| rng.gen_range_i64(1, max_val)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen: HashSet<u64> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |cases: Vec<(i64, Vec<i64>)>, seen: &mut HashSet<u64>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if cases.iter().any(|(_, a)| a.is_empty()) { return; }
        let mut h: u64 = 1469598103934665603;
        h ^= cases.len() as u64; h = h.wrapping_mul(1099511628211);
        for (sv, a) in &cases {
            h ^= *sv as u64; h = h.wrapping_mul(1099511628211);
            h ^= a.len() as u64; h = h.wrapping_mul(1099511628211);
            for &x in a { h ^= x as u64; h = h.wrapping_mul(1099511628211); }
        }
        if !seen.insert(h) { return; }
        let answers: Vec<i32> = cases.iter().map(|(sv, a)| Solution::verse_for_santa(a.len(), *sv, a.clone())).collect();
        let inp = build_input(&cases);
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Example
    let example = vec![
        (11i64, vec![2,9,1,3,18,1,4]),
        (35, vec![11,9,10,7]),
        (8, vec![5]),
    ];
    emit(example, &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![(1i64, vec![1])], &mut seen, &mut out, &mut count);
    emit(vec![(1_000_000_000i64, vec![1; 100])], &mut seen, &mut out, &mut count);
    emit(vec![(1i64, vec![1_000_000_000])], &mut seen, &mut out, &mut count);

    let mut tries = 0;
    while count < target && tries < 5000 {
        tries += 1;
        let t: usize = if tries < 5 { 1 } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<(i64, Vec<i64>)> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            if total_n >= 50_000 { break; }
            let max_n = (100_000 - total_n).min(10_000);
            let n = match tries % 5 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(2, 10),
                2 => rng.gen_range_usize(5, 50),
                3 => rng.gen_range_usize(20, 200),
                _ => rng.gen_range_usize(50, max_n.max(50)),
            };
            total_n += n;
            let max_a = match tries % 4 {
                0 => 10i64,
                1 => 100,
                2 => 10_000,
                _ => 1_000_000_000,
            };
            let a = random_array(&mut rng, n, max_a);
            let sv = rng.gen_range_i64(1, 1_000_000_000);
            cases.push((sv, a));
        }
        if !cases.is_empty() {
            emit(cases, &mut seen, &mut out, &mut count);
        }
    }
}

