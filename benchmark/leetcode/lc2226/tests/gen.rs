use vstd::prelude::*;

verus! {

pub fn generate_test_case(candies: Vec<i32>, k: i64, mutation_kind: u8) -> (result: (Vec<i32>, i64))
    requires
        1 <= candies.len() <= 100000,
        forall|i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
        1 <= k <= 1000000000000i64,
    ensures
        1 <= result.0.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000000,
        1 <= result.1 <= 1000000000000i64,
{
    if mutation_kind == 0 {
        // identity
        (candies, k)
    } else if mutation_kind == 1 {
        // set all candies to 1
        let n = candies.len();
        let mut c: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                c.len() == i,
                1 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] c[j] == 1i32,
            decreases n - i,
        {
            c.push(1i32);
            i += 1;
        }
        (c, k)
    } else if mutation_kind == 2 {
        // set all candies to max value (10000000)
        let n = candies.len();
        let mut c: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                c.len() == i,
                1 <= n <= 100000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] c[j] == 10000000i32,
            decreases n - i,
        {
            c.push(10000000i32);
            i += 1;
        }
        (c, k)
    } else if mutation_kind == 3 && k < 1000000000000i64 {
        // nudge k up
        (candies, k + 1)
    } else if mutation_kind == 4 && k > 1i64 {
        // nudge k down
        (candies, k - 1)
    } else if mutation_kind == 5 {
        // set k to 1
        (candies, 1i64)
    } else if mutation_kind == 6 {
        // set k to max
        (candies, 1000000000000i64)
    } else if mutation_kind == 7 {
        // set first candy to max value
        let mut c = candies;
        c.set(0, 10000000i32);
        (c, k)
    } else if mutation_kind == 8 {
        // set first candy to 1
        let mut c = candies;
        c.set(0, 1i32);
        (c, k)
    } else if mutation_kind == 9 && candies.len() < 100000 {
        // grow: push one element (value 1)
        let mut c = candies;
        c.push(1i32);
        (c, k)
    } else if mutation_kind == 10 && candies.len() > 1 {
        // shrink: pop last element
        let mut c = candies;
        c.pop();
        (c, k)
    } else if mutation_kind == 11 {
        // nudge first candy up if possible
        let mut c = candies;
        if c[0] < 10000000 {
            c.set(0, c[0] + 1);
        }
        (c, k)
    } else if mutation_kind == 12 {
        // nudge first candy down if possible
        let mut c = candies;
        if c[0] > 1 {
            c.set(0, c[0] - 1);
        }
        (c, k)
    } else if mutation_kind == 13 && candies.len() >= 2 {
        // swap first two elements
        let mut c = candies;
        let tmp = c[0];
        c.set(0, c[1]);
        c.set(1, tmp);
        (c, k)
    } else if mutation_kind == 14 && k <= 500000000000i64 {
        // double k
        (candies, k * 2)
    } else if mutation_kind == 15 {
        // halve k (at least 1)
        let new_k = k / 2;
        if new_k >= 1 {
            (candies, new_k)
        } else {
            (candies, 1i64)
        }
    } else {
        // fallback: identity
        (candies, k)
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

fn mutate(candies: Vec<i32>, k: i64, mutation_kind: u8) -> (Vec<i32>, i64) {
    generate_test_case(candies, k, mutation_kind)
}

fn random_candies(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut candies = Vec::with_capacity(len);
    for _ in 0..len {
        candies.push(rng.gen_range_i64(1, 10000000) as i32);
    }
    candies
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2226);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |candies: Vec<i32>, k: i64, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}_{}", candies, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::maximum_candies(candies.clone(), k);
        writeln!(out, "{}", json!({"input": {"candies": candies, "k": k}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    emit(vec![5, 8, 6], 3, &mut seen, &mut out, &mut count);
    emit(vec![2, 5], 11, &mut seen, &mut out, &mut count);

    // Seed inputs: interesting cases
    let seed_inputs: Vec<(Vec<i32>, i64)> = vec![
        (vec![1], 1),
        (vec![10000000], 1),
        (vec![1], 1000000000000),
        (vec![10000000], 1000000000000),
        (vec![1, 1, 1], 3),
        (vec![1, 1, 1], 4),
        (vec![10000000, 10000000, 10000000], 3),
        (vec![1, 2, 3, 4, 5], 5),
        (vec![1, 2, 3, 4, 5], 15),
        (vec![10000000; 10], 10),
        (vec![10000000; 10], 100),
        (vec![1; 100], 100),
    ];

    let mutation_kinds: Vec<u8> = (0..=15).collect();

    // Apply mutations to seed inputs
    for (c, kv) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (rc, rk) = mutate(c.clone(), *kv, mk);
            emit(rc, rk, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes and k values
    while count < target {
        // Size classes for array length
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 100000),  // max
        };
        let candies = random_candies(&mut rng, n);

        // k value classes
        let k: i64 = match rng.gen_range_usize(0, 4) {
            0 => 1,                                            // min k
            1 => rng.gen_range_i64(1, n as i64),               // k <= n
            2 => rng.gen_range_i64(1, 1000000),                // moderate k
            3 => rng.gen_range_i64(1, 1000000000000),          // large k
            _ => 1000000000000,                                // max k
        };

        let mk = rng.gen_range_usize(0, 15) as u8;
        let (rc, rk) = mutate(candies, k, mk);
        emit(rc, rk, &mut seen, &mut out, &mut count);
    }
}
