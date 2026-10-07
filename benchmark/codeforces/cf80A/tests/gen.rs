use vstd::prelude::*;

verus! {

pub open spec fn divides(d: int, n: int) -> bool {
    d > 0 && n > 0 && n % d == 0
}

pub open spec fn is_prime(n: int) -> bool {
    n >= 2 && (forall|d: int| 2 <= d < n ==> !divides(d, n))
}

spec fn no_div_below(n: int, d: int) -> bool
    decreases if d >= 2 { d } else { 0int },
{
    if d <= 2 {
        true
    } else {
        !divides(d - 1, n) && no_div_below(n, d - 1)
    }
}

proof fn lemma_no_div_below_implies(n: int, d: int)
    requires d >= 2, no_div_below(n, d),
    ensures forall|k: int| 2 <= k < d ==> !divides(k, n),
    decreases if d >= 2 { d } else { 0int },
{
    if d <= 2 {
    } else {
        lemma_no_div_below_implies(n, d - 1);
    }
}

proof fn lemma_is_prime(n: int)
    requires
        n >= 2,
        no_div_below(n, n),
    ensures
        is_prime(n),
{
    lemma_no_div_below_implies(n, n);
}

fn pick_prime(idx: usize) -> (result: u32)
    requires
        idx < 15,
    ensures
        2 <= result <= 47,
        is_prime(result as int),
{
    if idx == 0 {
        proof {
            assert(no_div_below(2int, 2int)) by(compute_only);
            lemma_is_prime(2int);
        }
        2u32
    } else if idx == 1 {
        proof {
            assert(no_div_below(3int, 3int)) by(compute_only);
            lemma_is_prime(3int);
        }
        3u32
    } else if idx == 2 {
        proof {
            assert(no_div_below(5int, 5int)) by(compute_only);
            lemma_is_prime(5int);
        }
        5u32
    } else if idx == 3 {
        proof {
            assert(no_div_below(7int, 7int)) by(compute_only);
            lemma_is_prime(7int);
        }
        7u32
    } else if idx == 4 {
        proof {
            assert(no_div_below(11int, 11int)) by(compute_only);
            lemma_is_prime(11int);
        }
        11u32
    } else if idx == 5 {
        proof {
            assert(no_div_below(13int, 13int)) by(compute_only);
            lemma_is_prime(13int);
        }
        13u32
    } else if idx == 6 {
        proof {
            assert(no_div_below(17int, 17int)) by(compute_only);
            lemma_is_prime(17int);
        }
        17u32
    } else if idx == 7 {
        proof {
            assert(no_div_below(19int, 19int)) by(compute_only);
            lemma_is_prime(19int);
        }
        19u32
    } else if idx == 8 {
        proof {
            assert(no_div_below(23int, 23int)) by(compute_only);
            lemma_is_prime(23int);
        }
        23u32
    } else if idx == 9 {
        proof {
            assert(no_div_below(29int, 29int)) by(compute_only);
            lemma_is_prime(29int);
        }
        29u32
    } else if idx == 10 {
        proof {
            assert(no_div_below(31int, 31int)) by(compute_only);
            lemma_is_prime(31int);
        }
        31u32
    } else if idx == 11 {
        proof {
            assert(no_div_below(37int, 37int)) by(compute_only);
            lemma_is_prime(37int);
        }
        37u32
    } else if idx == 12 {
        proof {
            assert(no_div_below(41int, 41int)) by(compute_only);
            lemma_is_prime(41int);
        }
        41u32
    } else if idx == 13 {
        proof {
            assert(no_div_below(43int, 43int)) by(compute_only);
            lemma_is_prime(43int);
        }
        43u32
    } else {
        proof {
            assert(no_div_below(47int, 47int)) by(compute_only);
            lemma_is_prime(47int);
        }
        47u32
    }
}

pub fn generate_test_case(prime_idx: u8, m_offset: u8) -> (result: (u32, u32))
    ensures
        2 <= result.0 < result.1 <= 50,
        is_prime(result.0 as int),
{
    let idx = (prime_idx as usize) % 15;
    let n: u32 = pick_prime(idx);
    let max_m: u32 = 50;
    let span = max_m - n;
    let off: u32 = 1 + ((m_offset as u32) % span);
    let m = n + off;
    if m > max_m {
        (n, max_m)
    } else {
        (n, m)
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
    let mut rng = Rng::new(80);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<(u32, u32)> = HashSet::new();
    let mut count = 0usize;

    let primes: [u32; 15] = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47];

    let mut emit = |n: u32, m: u32, seen: &mut HashSet<(u32, u32)>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if !(2 <= n && n < m && m <= 50) { return; }
        if !seen.insert((n, m)) { return; }
        let result = Solution::is_next_prime(n, m);
        let inp = format!("{} {}\n", n, m);
        let outp = if result { "YES\n".to_string() } else { "NO\n".to_string() };
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // examples
    emit(3, 5, &mut seen, &mut out, &mut count);
    emit(7, 11, &mut seen, &mut out, &mut count);
    emit(7, 9, &mut seen, &mut out, &mut count);

    // All consecutive prime pairs
    for i in 0..primes.len()-1 {
        emit(primes[i], primes[i+1], &mut seen, &mut out, &mut count);
    }

    // For each prime n, try various m
    for &n in &primes {
        for m in (n+1)..=50 {
            emit(n, m, &mut seen, &mut out, &mut count);
        }
    }

    // Random
    while count < target_count {
        let pidx = (rng.next_u64() % 15) as u8;
        let off = (rng.next_u64() % 50) as u8;
        let (n, m) = generate_test_case(pidx, off);
        emit(n, m, &mut seen, &mut out, &mut count);
    }
}
