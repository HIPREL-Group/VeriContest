use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fruits: Vec<i32>,
    baskets: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= fruits.len() <= 100,
        fruits.len() == baskets.len(),
        forall |i: int| 0 <= i < fruits.len() ==> 1 <= #[trigger] fruits[i] <= 1000,
        forall |i: int| 0 <= i < baskets.len() ==> 1 <= #[trigger] baskets[i] <= 1000,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (fruits, baskets)
    } else if mutation_kind == 1 {
        // set last fruit to 1000 (max, harder to place)
        let mut f = fruits;
        let last = f.len() - 1;
        f.set(last, 1000);
        (f, baskets)
    } else if mutation_kind == 2 {
        // set last basket to 1 (min capacity)
        let mut b = baskets;
        let last = b.len() - 1;
        b.set(last, 1);
        (fruits, b)
    } else if mutation_kind == 3 {
        // set first fruit to 1 (min fruit, easy to place)
        let mut f = fruits;
        f.set(0, 1);
        (f, baskets)
    } else if mutation_kind == 4 {
        // set first basket to 1000 (max capacity)
        let mut b = baskets;
        b.set(0, 1000);
        (fruits, b)
    } else if mutation_kind == 5 {
        // nudge first fruit up
        let val = fruits[0];
        let mut f = fruits;
        if val < 1000 {
            f.set(0, val + 1);
        }
        (f, baskets)
    } else if mutation_kind == 6 {
        // nudge first fruit down
        let val = fruits[0];
        let mut f = fruits;
        if val > 1 {
            f.set(0, val - 1);
        }
        (f, baskets)
    } else if mutation_kind == 7 {
        // nudge first basket up
        let val = baskets[0];
        let mut b = baskets;
        if val < 1000 {
            b.set(0, val + 1);
        }
        (fruits, b)
    } else if mutation_kind == 8 {
        // nudge first basket down
        let val = baskets[0];
        let mut b = baskets;
        if val > 1 {
            b.set(0, val - 1);
        }
        (fruits, b)
    } else if mutation_kind == 9 {
        // swap first fruit and basket values
        let f0 = fruits[0];
        let b0 = baskets[0];
        let mut f = fruits;
        let mut b = baskets;
        f.set(0, b0);
        b.set(0, f0);
        (f, b)
    } else {
        // fallback: identity
        (fruits, baskets)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(fruits: Vec<i32>, baskets: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(fruits, baskets, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3477);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |fruits: Vec<i32>, baskets: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}|{:?}", fruits, baskets);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::num_of_unplaced_fruits(fruits.clone(), baskets.clone());
        writeln!(out, "{}", json!({
            "input": {"fruits": fruits, "baskets": baskets},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![4, 2, 5], vec![3, 5, 4]),
        (vec![3, 6, 1], vec![6, 4, 7]),
    ];
    for (f, b) in &examples {
        emit(f.clone(), b.clone(), &mut seen, &mut out, &mut total);
    }

    // Seed inputs with mutations
    let seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![1000], vec![1000]),
        (vec![1000], vec![1]),
        (vec![1], vec![1000]),
        (vec![500, 500], vec![500, 500]),
        (vec![1, 1, 1], vec![1000, 1000, 1000]),
        (vec![1000, 1000, 1000], vec![1, 1, 1]),
        (vec![1, 2, 3, 4, 5], vec![5, 4, 3, 2, 1]),
        (vec![10, 20, 30], vec![30, 20, 10]),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for (f, b) in &seeds {
        for &mk in &mutation_kinds {
            let (rf, rb) = mutate(f.clone(), b.clone(), mk);
            emit(rf, rb, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs across size classes with mutations
    while total < count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 100),     // large
            _ => rng.gen_range_usize(1, 100),      // any
        };
        let fruits = random_array(&mut rng, n);
        let baskets = random_array(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let (rf, rb) = mutate(fruits, baskets, mk);
        emit(rf, rb, &mut seen, &mut out, &mut total);
    }
}
