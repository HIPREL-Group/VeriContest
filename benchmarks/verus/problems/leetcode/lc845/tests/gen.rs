use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 10_000,
        forall|k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|k: int| 0 <= k < result.len() ==> 0 <= #[trigger] result[k] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut a = arr;
        a.set(0, 0);
        a
    } else if mutation_kind == 2 {
        // set first element to 10000 (max boundary)
        let mut a = arr;
        a.set(0, 10_000);
        a
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 0);
        a
    } else if mutation_kind == 4 {
        // set last element to 10000
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 10_000);
        a
    } else if mutation_kind == 5 {
        // nudge first element up
        let mut a = arr;
        if a[0] < 10_000 {
            a.set(0, a[0] + 1);
        }
        a
    } else if mutation_kind == 6 {
        // nudge first element down
        let mut a = arr;
        if a[0] > 0 {
            a.set(0, a[0] - 1);
        }
        a
    } else if mutation_kind == 7 && arr.len() < 10_000 {
        // grow by one element (push 0)
        let mut a = arr;
        a.push(0);
        a
    } else if mutation_kind == 8 && arr.len() > 1 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 9 {
        // set all elements to the same value (flat — no mountain)
        let val = arr[0];
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 10_000,
                0 <= val <= 10_000,
                forall|j: int| 0 <= j < i ==> a[j] == val,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, val);
            i += 1;
        }
        a
    } else if mutation_kind == 10 && arr.len() >= 2 {
        // swap first two elements
        let mut a = arr;
        let tmp = a[0];
        a.set(0, a[1]);
        a.set(1, tmp);
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

fn mutate(arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(arr, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 10_000) as i32);
    }
    arr
}

/// Build a mountain array: ascending to peak then descending.
fn mountain_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    assert!(len >= 3);
    let peak_idx = rng.gen_range_usize(1, len - 2);
    let mut arr = Vec::with_capacity(len);
    // ascending part [0..peak_idx]
    let mut val: i32 = rng.gen_range_i64(0, 5_000) as i32;
    arr.push(val);
    for _ in 1..=peak_idx {
        let step = rng.gen_range_i64(1, 100) as i32;
        val = std::cmp::min(val + step, 10_000);
        arr.push(val);
    }
    // descending part [peak_idx+1..len-1]
    for _ in (peak_idx + 1)..len {
        let step = rng.gen_range_i64(1, 100) as i32;
        val = std::cmp::max(val - step, 0);
        arr.push(val);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(845);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?}", arr);
        if !seen.insert(key) { return; }
        let output = Solution::longest_mountain(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 1, 4, 7, 3, 2, 5],
        vec![2, 2, 2],
    ];
    for ex in examples {
        emit(mutate(ex, 0), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds covering edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],                              // single element
        vec![0, 1],                           // two elements, no mountain
        vec![0, 1, 0],                        // minimal mountain
        vec![0, 10000, 0],                    // peak at max value
        vec![5, 5, 5, 5],                     // flat, no mountain
        vec![0, 1, 2, 3],                     // strictly ascending, no mountain
        vec![3, 2, 1, 0],                     // strictly descending, no mountain
        vec![0, 1, 2, 1, 0],                  // full mountain
        vec![0, 1, 2, 3, 2, 1, 0],            // larger mountain
        vec![0, 1, 0, 1, 0],                  // two small mountains
        vec![1, 3, 1, 3, 1, 3, 1],            // multiple mountains
        vec![0, 1, 2, 2, 1, 0],              // plateau at peak (not a mountain)
        vec![0, 0, 1, 0, 0],                 // mountain with flat edges
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Generate mountain arrays with mutations
    for _ in 0..20 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => 3,
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 2000),
        };
        let arr = mountain_arr(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut count);
    }

    // Random arrays with diverse sizes and mutations
    for _ in 0..40 {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // max
        };
        let arr = random_arr(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < target_count {
        let len = rng.gen_range_usize(1, 10_000);
        let arr = random_arr(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut count);
    }
}
