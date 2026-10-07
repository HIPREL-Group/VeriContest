use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 9999,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100000,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 9999 { 9999usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 9999,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 100000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let value = if value < 0 { 0 } else if value > 100000 { 100000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(encoded: Vec<i32>, first: i32) -> (result: (Vec<i32>, i32))
    ensures
        1 <= result.0.len() <= 9999,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100000,
        0 <= result.1 <= 100000,
{
    let encoded = bounded_values(&encoded);
    let first = if first < 0 { 0 } else if first > 100000 { 100000 } else { first };
    (encoded, first)
}


pub fn generate_candidate(encoded: Vec<i32>, first: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        encoded.len() <= 100000,
        forall|i: int| 0 <= i && i < encoded.len() ==> 0 <= #[trigger] encoded[i] && encoded[i] <= 100000,
        0 <= first && first <= 100000,
    ensures
        result.0.len() <= 100000,
        forall|i: int| 0 <= i && i < result.0.len() ==> 0 <= #[trigger] result.0[i] && result.0[i] <= 100000,
        0 <= result.1 && result.1 <= 100000,
{
    if mutation_kind == 0 {
        // identity
        (encoded, first)
    } else if mutation_kind == 1 && encoded.len() > 0 {
        // set last element to 0
        let mut e = encoded;
        let last = e.len() - 1;
        e.set(last, 0);
        (e, first)
    } else if mutation_kind == 2 && encoded.len() > 0 {
        // set last element to 100000
        let mut e = encoded;
        let last = e.len() - 1;
        e.set(last, 100000);
        (e, first)
    } else if mutation_kind == 3 && encoded.len() > 0 {
        // set first element to 0
        let mut e = encoded;
        e.set(0, 0);
        (e, first)
    } else if mutation_kind == 4 && encoded.len() < 100000 {
        // grow: push a 0
        let mut e = encoded;
        e.push(0);
        (e, first)
    } else if mutation_kind == 5 && encoded.len() > 0 {
        // shrink: pop last element
        let mut e = encoded;
        e.pop();
        (e, first)
    } else if mutation_kind == 6 {
        // set first to 0
        (encoded, 0)
    } else if mutation_kind == 7 {
        // set first to 100000
        (encoded, 100000)
    } else if mutation_kind == 8 && encoded.len() > 0 {
        // set all elements to same value (first element's value)
        let val = encoded[0];
        let mut e = encoded;
        let mut i: usize = 0;
        while i < e.len()
            invariant
                0 <= i <= e.len(),
                e.len() == encoded.len(),
                e.len() <= 100000,
                0 <= val && val <= 100000,
                forall|j: int| 0 <= j < i ==> e[j] == val,
                forall|j: int| i <= j < e.len() ==> e[j] == encoded[j],
            decreases e.len() - i,
        {
            e.set(i, val);
            i += 1;
        }
        (e, first)
    } else if mutation_kind == 9 && encoded.len() >= 2 {
        // swap first two elements
        let mut e = encoded;
        let a = e[0];
        let b = e[1];
        e.set(0, b);
        e.set(1, a);
        (e, first)
    } else if mutation_kind == 10 && encoded.len() > 0 {
        // nudge last element up if possible
        let mut e = encoded;
        let last = e.len() - 1;
        if e[last] < 100000 {
            e.set(last, e[last] + 1);
        }
        (e, first)
    } else if mutation_kind == 11 && encoded.len() > 0 {
        // nudge last element down if possible
        let mut e = encoded;
        let last = e.len() - 1;
        if e[last] > 0 {
            e.set(last, e[last] - 1);
        }
        (e, first)
    } else {
        // fallback: identity
        (encoded, first)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_encoded(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut encoded = Vec::with_capacity(len);
    for _ in 0..len {
        encoded.push(rng.gen_range_i64(0, 100000) as i32);
    }
    encoded
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1720);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |encoded: Vec<i32>, first: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let (encoded, first) = generate_test_case(encoded, first);
        if *count >= target {
            return;
        }
        let key = format!("{:?}:{}", encoded, first);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::decode(encoded.clone(), first);
        writeln!(out, "{}", json!({"input": {"encoded": encoded, "first": first}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1, 2, 3], 1),
        (vec![6, 2, 7, 3], 4),
    ];
    for (enc, f) in &examples {
        emit(enc.clone(), *f, &mut seen, &mut out, &mut count);
    }

    // Seed inputs for mutation
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        (vec![], 0),
        (vec![0], 0),
        (vec![100000], 100000),
        (vec![0, 0, 0], 0),
        (vec![100000, 100000], 50000),
        (vec![1], 1),
        (vec![0], 100000),
        (vec![42, 7, 99], 12345),
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to every seed
    for (enc, f) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (result_enc, result_first) = generate_candidate(enc.clone(), *f, mk);
            emit(result_enc, result_first, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations, diverse size classes
    while count < target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(0, 3),        // tiny (including empty)
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // very large
        };
        let enc = random_encoded(&mut rng, n);
        let first = rng.gen_range_i64(0, 100000) as i32;
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (result_enc, result_first) = generate_candidate(enc, first, mk);
        emit(result_enc, result_first, &mut seen, &mut out, &mut count);
    }
}
