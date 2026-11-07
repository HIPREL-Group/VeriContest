use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1,
{
    let n = if values.len() == 0 { 1usize } else if values.len() > 1000 { 1000usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 1000, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        result.push(if value < 0 { 0 } else if value > 1 { 1 } else { value });
        i += 1;
    }
    result
}

pub fn generate_test_case(bits: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0 || result[i] == 1,
        result[result.len() as int - 1] == 0,
{
    let mut result = bounded_values(&bits);
    let last = result.len() - 1;
    result.set(last, 0);
    result
}


pub fn generate_candidate(bits: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= bits.len() <= 1000,
        forall|i: int| 0 <= i < bits.len() ==> bits[i] == 0 || bits[i] == 1,
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0 || result[i] == 1,
{
    if mutation_kind == 0 {
        // identity
        bits
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut b = bits;
        let last = b.len() - 1;
        b.set(last, 0);
        b
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut b = bits;
        let last = b.len() - 1;
        b.set(last, 1);
        b
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut b = bits;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == bits.len(),
                1 <= b.len() <= 1000,
                forall|j: int| 0 <= j < i ==> b[j] == 0,
                forall|j: int| i <= j < b.len() ==> b[j] == 0 || b[j] == 1,
            decreases b.len() - i,
        {
            b.set(i, 0);
            i += 1;
        }
        b
    } else if mutation_kind == 4 {
        // set all elements to 1
        let mut b = bits;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == bits.len(),
                1 <= b.len() <= 1000,
                forall|j: int| 0 <= j < i ==> b[j] == 1,
                forall|j: int| i <= j < b.len() ==> b[j] == 0 || b[j] == 1,
            decreases b.len() - i,
        {
            b.set(i, 1);
            i += 1;
        }
        b
    } else if mutation_kind == 5 && bits.len() < 1000 {
        // grow by appending 0
        let mut b = bits;
        b.push(0);
        b
    } else if mutation_kind == 6 && bits.len() < 1000 {
        // grow by appending 1
        let mut b = bits;
        b.push(1);
        b
    } else if mutation_kind == 7 && bits.len() > 1 {
        // shrink by removing last element
        let mut b = bits;
        b.pop();
        b
    } else if mutation_kind == 8 {
        // flip first element
        let mut b = bits;
        if b[0] == 0 {
            b.set(0, 1);
        } else {
            b.set(0, 0);
        }
        b
    } else if mutation_kind == 9 {
        // flip last element
        let mut b = bits;
        let last = b.len() - 1;
        if b[last] == 0 {
            b.set(last, 1);
        } else {
            b.set(last, 0);
        }
        b
    } else {
        bits // fallback
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_bits(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut bits = Vec::with_capacity(len);
    for _ in 0..len {
        bits.push(rng.gen_range_usize(0, 1) as i32);
    }
    bits
}

fn random_bits_ending_zero(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut bits = random_bits(rng, len);
    if !bits.is_empty() {
        let last = bits.len() - 1;
        bits[last] = 0;
    }
    bits
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(717);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |bits: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let bits = generate_test_case(bits);
        if *count >= target { return; }
        let key = format!("{:?}", bits);
        if !seen.insert(key) { return; }
        let output = Solution::is_one_bit_character(bits.clone());
        writeln!(out, "{}", json!({"input": {"bits": bits}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 0],
        vec![1, 1, 1, 0],
        vec![0],
        vec![0, 0],
        vec![1, 0],
        vec![1, 1, 0],
        vec![1, 0, 1, 0],
        vec![1, 1, 0, 0],
    ];

    let mutation_kinds: Vec<u8> = (0..=9).collect();

    // Apply every mutation to every example seed
    for seed_bits in &examples {
        for &mk in &mutation_kinds {
            let result = generate_candidate(seed_bits.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 1000),  // max
        };
        // ~50% end with 0 (valid problem input), ~50% arbitrary
        let seed_bits = if rng.gen_range_usize(0, 1) == 0 {
            random_bits_ending_zero(&mut rng, len)
        } else {
            random_bits(&mut rng, len)
        };
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_candidate(seed_bits, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
