use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: &mut Vec<i32>, mutation_kind: u8)
    requires
        1 <= old(arr).len() <= 10_000,
        forall|i: int| 0 <= i < old(arr).len() ==> 0 <= #[trigger] old(arr)[i] <= 9,
    ensures
        1 <= old(arr).len() <= 10_000,
        forall|i: int| 0 <= i < old(arr).len() ==> 0 <= #[trigger] old(arr)[i] <= 9,
        1 <= arr.len() <= 10_000,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 9,
{
    if mutation_kind == 0 {
        // identity — no change
    } else if mutation_kind == 1 {
        // set last element to 0 (force zero duplication near end)
        let last = arr.len() - 1;
        arr.set(last, 0);
    } else if mutation_kind == 2 {
        // set all elements to 0 (maximum duplication)
        let ghost old_arr = arr@;
        let n = arr.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                arr.len() == n,
                1 <= n <= 10_000,
                forall|j: int| 0 <= j < i ==> arr[j] == 0,
                forall|j: int| i <= j < n as int ==> arr[j] == old_arr[j],
            decreases n - i,
        {
            arr.set(i, 0);
            i += 1;
        }
    } else if mutation_kind == 3 && arr.len() < 10_000 {
        // grow by one element (push a 0)
        arr.push(0);
    } else if mutation_kind == 4 && arr.len() > 1 {
        // shrink by one element (pop)
        arr.pop();
    } else if mutation_kind == 5 {
        // set last element to 9 (non-zero, no duplication at end)
        let last = arr.len() - 1;
        arr.set(last, 9);
    } else if mutation_kind == 6 {
        // nudge last element up: if < 9, increment
        let last = arr.len() - 1;
        if arr[last] < 9 {
            let v = arr[last];
            arr.set(last, v + 1);
        }
    } else if mutation_kind == 7 {
        // nudge last element down: if > 0, decrement
        let last = arr.len() - 1;
        if arr[last] > 0 {
            let v = arr[last];
            arr.set(last, v - 1);
        }
    } else if mutation_kind == 8 {
        // set all elements to 9
        let ghost old_arr = arr@;
        let n = arr.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                arr.len() == n,
                1 <= n <= 10_000,
                forall|j: int| 0 <= j < i ==> arr[j] == 9,
                forall|j: int| i <= j < n as int ==> arr[j] == old_arr[j],
            decreases n - i,
        {
            arr.set(i, 9);
            i += 1;
        }
    } else {
        // fallback — no change
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

fn mutate(mut arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(&mut arr, mutation_kind);
    arr
}

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 9) as i32);
    }
    arr
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
        let mut arr_clone = arr.clone();
        Solution::duplicate_zeros(&mut arr_clone);
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": arr_clone})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 0, 2, 3, 0, 4, 5, 0],  // Example 1
        vec![1, 2, 3],                   // Example 2
        vec![0],                         // single zero
        vec![9],                         // single non-zero
        vec![0, 0, 0, 0],               // all zeros
        vec![1, 2, 3, 4, 5],            // no zeros
        vec![0, 1, 0, 1, 0],            // alternating
        vec![1, 0, 0, 0, 1],            // consecutive zeros
        vec![0, 0, 0, 0, 0, 0, 0, 0, 0, 0], // 10 zeros
        vec![9, 9, 9, 9, 9, 9, 9, 9, 9, 9], // 10 nines
        vec![5, 0, 5, 0, 5],            // mixed
        vec![0, 9],                      // two elements
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

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
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // max
        };
        let s = random_arr(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let s = random_arr(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
