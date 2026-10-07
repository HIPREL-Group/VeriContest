use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= arr.len() <= 1000,
        forall|i: int| 0 <= i < arr.len() ==> -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> -1_000_000 <= #[trigger] result[i] <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 0);
        a
    } else if mutation_kind == 2 {
        // set last element to 1_000_000 (max boundary)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1_000_000);
        a
    } else if mutation_kind == 3 {
        // set last element to -1_000_000 (min boundary)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, -1_000_000);
        a
    } else if mutation_kind == 4 {
        // set all elements to 0 (all same — trivial AP)
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                2 <= a.len() <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == 0int,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        a
    } else if mutation_kind == 5 && arr.len() < 1000 {
        // grow by one element (push 0)
        let mut a = arr;
        a.push(0);
        a
    } else if mutation_kind == 6 && arr.len() > 2 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 7 {
        // nudge last element: if < 1_000_000, increment by 1
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] < 1_000_000 {
            a.set(last, a[last] + 1);
        }
        a
    } else if mutation_kind == 8 {
        // nudge last element down: if > -1_000_000, decrement by 1
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] > -1_000_000 {
            a.set(last, a[last] - 1);
        }
        a
    } else if mutation_kind == 9 && arr.len() >= 2 {
        // swap first two elements
        let mut a = arr;
        let tmp = a[0];
        a.set(0, a[1]);
        a.set(1, tmp);
        a
    } else if mutation_kind == 10 {
        // negate last element
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, -a[last]);
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
    let mut a = Vec::with_capacity(len);
    for _ in 0..len {
        a.push(rng.gen_range_i64(-1_000_000, 1_000_000) as i32);
    }
    a
}

fn make_ap(start: i32, step: i32, len: usize) -> Vec<i32> {
    let mut a = Vec::with_capacity(len);
    let mut v = start as i64;
    for _ in 0..len {
        a.push(v as i32);
        v += step as i64;
    }
    a
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

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", arr);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::can_make_arithmetic_progression(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let seeds: Vec<Vec<i32>> = vec![
        vec![3, 5, 1],                          // example 1 (true)
        vec![1, 2, 4],                          // example 2 (false)
        vec![1, 2],                              // minimal, AP
        vec![5, 5],                              // minimal, all same
        vec![1, 1, 1, 1],                        // all same, AP
        vec![1, 3, 5, 7, 9],                    // sorted AP
        vec![9, 7, 5, 3, 1],                    // reverse sorted AP
        vec![1, 5, 3],                           // shuffled AP
        vec![1, 2, 3, 5],                        // not AP
        vec![-5, -3, -1, 1, 3],                  // negative to positive AP
        vec![1_000_000, -1_000_000],             // boundary values
        vec![0, 0, 0, 0, 0],                    // all zeros
        vec![-1_000_000, 0, 1_000_000],          // boundary AP
        make_ap(0, 1, 10),                       // consecutive 0..9
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    for i in 0..60 {
        let len = match i % 5 {
            0 => rng.gen_range_usize(2, 5),        // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };
        // Mix random arrays and arithmetic progressions
        let s = if i % 3 == 0 {
            let start = rng.gen_range_i64(-500_000, 500_000) as i32;
            let max_step = if len > 1 { (2_000_000i64 / (len as i64 - 1)).min(1000) } else { 1000 };
            let step = rng.gen_range_i64(-max_step, max_step) as i32;
            make_ap(start, step, len)
        } else {
            random_arr(&mut rng, len)
        };
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(2, 1000);
        let s = random_arr(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
