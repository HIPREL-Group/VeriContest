use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: Vec<u8>, mutation_kind: u8) -> (result: Vec<char>)
    requires
        1 <= bits.len() <= 100000,
        forall|i: int| 0 <= i < bits.len() ==> bits[i] == 0 || bits[i] == 1,
    ensures
        1 <= result@.len() <= 100000,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == '0' || result@[i] == '1',
{
    let mut bits = bits;

    if mutation_kind == 1 {
        bits.set(0, 0u8);
    } else if mutation_kind == 2 {
        bits.set(0, 1u8);
    } else if mutation_kind == 3 {
        let last = bits.len() - 1;
        bits.set(last, 0u8);
    } else if mutation_kind == 4 {
        let last = bits.len() - 1;
        bits.set(last, 1u8);
    } else if mutation_kind == 5 && bits.len() > 1 {
        bits.pop();
    } else if mutation_kind == 6 && bits.len() < 100000 {
        bits.push(0u8);
    } else if mutation_kind == 7 && bits.len() < 100000 {
        bits.push(1u8);
    } else if mutation_kind == 8 && bits.len() >= 2 {
        let first = bits[0];
        let last_idx = bits.len() - 1;
        let last = bits[last_idx];
        bits.set(0, last);
        bits.set(last_idx, first);
    }

    let mut result: Vec<char> = Vec::new();
    let n = bits.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            1 <= n <= 100000,
            0 <= i <= n,
            result@.len() == i as int,
            forall|j: int| 0 <= j < bits.len() ==> bits[j] == 0 || bits[j] == 1,
            forall|j: int| 0 <= j < i as int ==> result@[j] == '0' || result@[j] == '1',
        decreases n - i,
    {
        if bits[i] == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        i += 1;
    }
    result
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn make_bits(pattern: &str) -> Vec<u8> {
    pattern.bytes().map(|b| b - b'0').collect()
}

fn random_bits(rng: &mut Rng, len: usize) -> Vec<u8> {
    (0..len).map(|_| (rng.next_u64() % 2) as u8).collect()
}

fn all_same(val: u8, len: usize) -> Vec<u8> {
    vec![val; len]
}

fn alternating(start: u8, len: usize) -> Vec<u8> {
    (0..len).map(|i| if i % 2 == 0 { start } else { 1 - start }).collect()
}

fn sorted_bits(len: usize, ones: usize) -> Vec<u8> {
    let zeros = len - ones;
    let mut v = vec![0u8; zeros];
    v.extend(vec![1u8; ones]);
    v
}

fn reverse_sorted_bits(len: usize, ones: usize) -> Vec<u8> {
    let zeros = len - ones;
    let mut v = vec![1u8; ones];
    v.extend(vec![0u8; zeros]);
    v
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut generated = 0usize;

    // Example inputs from description
    let examples = vec!["101", "100", "0111"];
    for ex in &examples {
        if generated >= count { break; }
        let bits = make_bits(ex);
        let chars = generate_test_case(bits, 0);
        let s: String = chars.iter().collect();
        let s_copy = s.clone();
        let output = Solution::minimum_steps(s);
        writeln!(out, "{}", json!({"input": {"s": s_copy}, "output": output})).unwrap();
        generated += 1;
    }

    // Structured seed patterns for diversity
    let structured: Vec<Vec<u8>> = vec![
        all_same(0, 1),
        all_same(1, 1),
        all_same(0, 10),
        all_same(1, 10),
        alternating(0, 10),
        alternating(1, 10),
        sorted_bits(10, 5),
        reverse_sorted_bits(10, 5),
        sorted_bits(100, 50),
        reverse_sorted_bits(100, 50),
        all_same(0, 100000),
        all_same(1, 100000),
    ];

    for bits in structured {
        for mk in 0..=8u8 {
            if generated >= count { break; }
            let chars = generate_test_case(bits.clone(), mk);
            let s: String = chars.iter().collect();
            let s_copy = s.clone();
            let output = Solution::minimum_steps(s);
            writeln!(out, "{}", json!({"input": {"s": s_copy}, "output": output})).unwrap();
            generated += 1;
        }
        if generated >= count { break; }
    }

    // Random test cases with diverse size classes
    while generated < count {
        let n = match generated % 7 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            4 => rng.gen_range_usize(201, 1000),
            5 => rng.gen_range_usize(1001, 10000),
            _ => rng.gen_range_usize(10001, 100000),
        };

        let bits = random_bits(&mut rng, n);
        let mk = (rng.next_u64() % 9) as u8;

        let chars = generate_test_case(bits, mk);
        let s: String = chars.iter().collect();
        let s_copy = s.clone();
        let output = Solution::minimum_steps(s);
        writeln!(out, "{}", json!({"input": {"s": s_copy}, "output": output})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases", generated);
}
