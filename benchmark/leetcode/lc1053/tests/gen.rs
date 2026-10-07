use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 10_000,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 10_000,
    ensures
        1 <= result@.len() <= 10_000,
        forall|i: int| 0 <= i < result@.len() ==> 1 <= #[trigger] result@[i] <= 10_000,
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
        // set last element to 10000 (max boundary)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 10_000);
        a
    } else if mutation_kind == 3 && arr.len() >= 2 {
        // swap first and last elements
        let mut a = arr;
        let last = a.len() - 1;
        let v0 = a[0];
        let vl = a[last];
        a.set(0, vl);
        a.set(last, v0);
        a
    } else if mutation_kind == 4 && arr.len() < 10_000 {
        // grow: push element 1
        let mut a = arr;
        a.push(1);
        a
    } else if mutation_kind == 5 && arr.len() > 1 {
        // shrink: pop last element
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 6 {
        // nudge last element up (if < 10000)
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] < 10_000 {
            a.set(last, a[last] + 1);
        }
        a
    } else if mutation_kind == 7 {
        // nudge last element down (if > 1)
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] > 1 {
            a.set(last, a[last] - 1);
        }
        a
    } else if mutation_kind == 8 {
        // set all elements to 1
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> a[j] == 1i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 1);
            i += 1;
        }
        a
    } else if mutation_kind == 9 {
        // set all elements to 10000
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> a[j] == 10_000i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 10_000);
            i += 1;
        }
        a
    } else if mutation_kind == 10 {
        // set first element to 1
        let mut a = arr;
        a.set(0, 1);
        a
    } else if mutation_kind == 11 {
        // set first element to 10000
        let mut a = arr;
        a.set(0, 10_000);
        a
    } else {
        // fallback: identity
        arr
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

fn mutate(arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(arr, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 10_000) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1053);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let result = Solution::prev_perm_opt1(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": result})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 2, 1],
        vec![1, 1, 5],
        vec![1, 9, 4, 6, 7],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut out, &mut count);
    }

    // Curated seeds for diversity
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 2],
        vec![2, 1],
        vec![1, 1],
        vec![10000],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 1, 1, 1],
        vec![10000, 10000, 10000],
        vec![1, 10000],
        vec![10000, 1],
        vec![5, 5, 5, 5, 5],
        vec![3, 1, 2],
        vec![2, 3, 1],
        vec![1, 3, 2],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply mutations to curated seeds
    for seed in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed.clone(), mk);
            emit(result, &mut out, &mut count);
        }
    }

    // Random arrays with diverse sizes and random mutations
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 10000), // max
        };
        let arr = random_arr(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut out, &mut count);
    }
}
