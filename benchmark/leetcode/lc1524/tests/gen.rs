use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 100_000,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set last element to 1 (min boundary)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1);
        a
    } else if mutation_kind == 2 {
        // set last element to 100 (max boundary)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 100);
        a
    } else if mutation_kind == 3 {
        // set all elements to 1 (all even sums)
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> a[j] == 1,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 1);
            i += 1;
        }
        a
    } else if mutation_kind == 4 {
        // set all elements to 2 (all even)
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> a[j] == 2,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 2);
            i += 1;
        }
        a
    } else if mutation_kind == 5 && arr.len() < 100_000 {
        // grow by one element
        let mut a = arr;
        a.push(50);
        a
    } else if mutation_kind == 6 && arr.len() > 1 {
        // shrink by one element
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 7 {
        // nudge first element: if < 100, increment by 1
        let mut a = arr;
        if a[0] < 100 {
            a.set(0, a[0] + 1);
        }
        a
    } else if mutation_kind == 8 {
        // nudge first element down: if > 1, decrement by 1
        let mut a = arr;
        if a[0] > 1 {
            a.set(0, a[0] - 1);
        }
        a
    } else if mutation_kind == 9 {
        // set first element to 50 (mid-range)
        let mut a = arr;
        a.set(0, 50);
        a
    } else {
        arr // fallback
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

fn mutate(arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(arr, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 100) as i32);
    }
    arr
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
    let mut emitted = 0usize;

    let mut emit = |arr: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let output = Solution::num_of_subarrays(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    emit(vec![1, 3, 5], &mut out, &mut emitted);
    emit(vec![2, 4, 6], &mut out, &mut emitted);
    emit(vec![1, 2, 3, 4, 5, 6, 7], &mut out, &mut emitted);

    // Seed arrays for mutation
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![100],
        vec![1, 2],
        vec![2, 1],
        vec![1, 1, 1],
        vec![2, 2, 2],
        vec![1, 2, 3, 4, 5],
        vec![50, 50, 50],
        vec![99, 100, 1, 2],
        vec![1, 100, 1, 100],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut out, &mut emitted);
        }
    }

    // Size classes with random mutations
    for i in 0..30 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let arr = random_arr(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut out, &mut emitted);
    }

    // Fill remaining with random arrays, identity mutation
    while emitted < count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let arr = random_arr(&mut rng, len);
        emit(mutate(arr, 0), &mut out, &mut emitted);
    }
}
