use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    bits: Vec<i32>,
    k_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= bits.len() <= 100_000,
        forall|i: int| 0 <= i < bits.len() ==> bits[i] == 0 || bits[i] == 1,
        0 <= k_val <= bits.len(),
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> result.0[i] == 0 || result.0[i] == 1,
        0 <= result.1 <= result.0.len(),
{
    if mutation_kind == 0 {
        // identity
        (bits, k_val)
    } else if mutation_kind == 1 {
        // flip last bit
        let mut b = bits;
        let last = b.len() - 1;
        if b[last] == 0 {
            b.set(last, 1);
        } else {
            b.set(last, 0);
        }
        (b, k_val)
    } else if mutation_kind == 2 {
        // set all to 1
        let mut b = bits;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == bits.len(),
                1 <= b.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> b[j] == 1i32,
                forall|j: int| i <= j < b.len() ==> b[j] == bits[j],
            decreases b.len() - i,
        {
            b.set(i, 1);
            i += 1;
        }
        (b, k_val)
    } else if mutation_kind == 3 {
        // set all to 0
        let mut b = bits;
        let mut i: usize = 0;
        while i < b.len()
            invariant
                0 <= i <= b.len(),
                b.len() == bits.len(),
                1 <= b.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> b[j] == 0i32,
                forall|j: int| i <= j < b.len() ==> b[j] == bits[j],
            decreases b.len() - i,
        {
            b.set(i, 0);
            i += 1;
        }
        (b, k_val)
    } else if mutation_kind == 4 && bits.len() < 100_000 {
        // grow by one element (push 0)
        let mut b = bits;
        b.push(0);
        (b, k_val)
    } else if mutation_kind == 5 && bits.len() > 1 && (k_val as usize) < bits.len() {
        // shrink by one element (pop)
        let mut b = bits;
        b.pop();
        (b, k_val)
    } else if mutation_kind == 6 {
        // set k to 0 (no flips allowed)
        (bits, 0i32)
    } else if mutation_kind == 7 {
        // set k to len (all flips allowed)
        let k = bits.len() as i32;
        (bits, k)
    } else if mutation_kind == 8 && bits.len() < 100_000 {
        // grow by one element (push 1)
        let mut b = bits;
        b.push(1);
        (b, k_val)
    } else {
        // fallback: identity
        (bits, k_val)
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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

extern crate serde_json;
use serde_json::json;

fn random_bits(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}:{}", nums, k);
        if !seen.insert(key) { return; }
        let result = Solution::longest_ones(nums.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1,1,1,0,0,0,1,1,1,1,0], 2),
        (vec![0,0,1,1,0,0,1,1,1,0,1,1,0,0,0,1,1,1,1], 3),
    ];
    for (nums, k) in examples {
        emit(nums, k, &mut seen, &mut out, &mut total);
    }

    // Edge case seeds
    let edge_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 0),
        (vec![0], 0),
        (vec![0], 1),
        (vec![1], 1),
        (vec![0, 0, 0], 0),
        (vec![1, 1, 1], 0),
        (vec![0, 0, 0], 3),
        (vec![1, 0, 1, 0, 1], 0),
        (vec![1, 0, 1, 0, 1], 2),
        (vec![1, 0, 1, 0, 1], 5),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply every mutation to every edge seed
    for (bits, k) in &edge_seeds {
        for &mk in &mutation_kinds {
            let (nums, k_out) = generate_test_case(bits.clone(), *k, mk);
            emit(nums, k_out, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse sizes
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 20),       // small
            2 => rng.gen_range_usize(21, 200),     // medium
            3 => rng.gen_range_usize(201, 5000),   // large
            _ => rng.gen_range_usize(5001, 100_000), // max
        };
        let bits = random_bits(&mut rng, n);
        let k = rng.gen_range_i64(0, n as i64) as i32;
        let mk = rng.gen_range_usize(0, 8) as u8;
        let (nums, k_out) = generate_test_case(bits, k, mk);
        emit(nums, k_out, &mut seen, &mut out, &mut total);
    }
}
