use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    happiness: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= happiness.len() <= 200000,
        1 <= k <= happiness.len(),
        forall|i: int| 0 <= i < happiness.len() ==> 1 <= #[trigger] happiness[i] <= 100000000,
    ensures
        1 <= result.0.len() <= 200000,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100000000,
{
    if mutation_kind == 0 {
        // identity
        (happiness, k)
    } else if mutation_kind == 1 {
        // set all values to 1 (minimum happiness)
        let mut h = happiness;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == happiness.len(),
                1 <= h.len() <= 200000,
                forall|j: int| 0 <= j < i ==> h[j] == 1i32,
                forall|j: int| i <= j < h.len() ==> h[j] == happiness[j],
            decreases h.len() - i,
        {
            h.set(i, 1);
            i += 1;
        }
        (h, k)
    } else if mutation_kind == 2 {
        // set all values to max (100_000_000)
        let mut h = happiness;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == happiness.len(),
                1 <= h.len() <= 200000,
                forall|j: int| 0 <= j < i ==> h[j] == 100_000_000i32,
                forall|j: int| i <= j < h.len() ==> h[j] == happiness[j],
            decreases h.len() - i,
        {
            h.set(i, 100_000_000);
            i += 1;
        }
        (h, k)
    } else if mutation_kind == 3 {
        // set k to 1 (select only one child)
        (happiness, 1)
    } else if mutation_kind == 4 {
        // set k to happiness.len() (select all children)
        let new_k = happiness.len() as i32;
        (happiness, new_k)
    } else if mutation_kind == 5 {
        // nudge first element up (clamp at max)
        let mut h = happiness;
        if h[0] < 100_000_000 {
            h.set(0, h[0] + 1);
        }
        (h, k)
    } else if mutation_kind == 6 {
        // nudge first element down (clamp at min)
        let mut h = happiness;
        if h[0] > 1 {
            h.set(0, h[0] - 1);
        }
        (h, k)
    } else if mutation_kind == 7 && happiness.len() > 1 {
        // swap first two elements
        let mut h = happiness;
        let tmp = h[0];
        h.set(0, h[1]);
        h.set(1, tmp);
        (h, k)
    } else if mutation_kind == 8 && happiness.len() < 200000 {
        // grow: push element with value 1
        let mut h = happiness;
        h.push(1);
        (h, k)
    } else if mutation_kind == 9 && happiness.len() > 1 && k < happiness.len() as i32 {
        // shrink: pop last element (only if k < len so k <= new len)
        let mut h = happiness;
        h.pop();
        (h, k)
    } else {
        // fallback: identity
        (happiness, k)
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

fn mutate(happiness: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(happiness, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_happiness(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut h = Vec::with_capacity(len);
    for _ in 0..len {
        h.push(rng.gen_range_i64(1, 100_000_000) as i32);
    }
    h
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |happiness: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?},{}", happiness, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::maximum_happiness_sum(happiness.clone(), k);
        writeln!(out, "{}", json!({"input": {"happiness": happiness, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 2, 3], 2, &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1], 2, &mut seen, &mut out, &mut count);
    emit(vec![2, 3, 4, 5], 1, &mut seen, &mut out, &mut count);

    // Generate diverse random test cases
    let num_mutations: u8 = 10;

    while count < target {
        // Size classes for array length
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 5000),    // big
        };

        let happiness = random_happiness(&mut rng, n);
        let k = rng.gen_range_i64(1, n as i64) as i32;

        // Apply a random mutation
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (h, k) = mutate(happiness, k, mk);
        emit(h, k, &mut seen, &mut out, &mut count);
    }
}
