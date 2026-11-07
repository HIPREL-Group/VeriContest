use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, k: usize, mutation_kind: u8) -> (result: (Vec<i32>, usize))
    requires
        1 <= values.len() <= 150_000,
        1 <= k <= values.len(),
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values@[i] <= 100,
    ensures
        result.0.len() <= 150_000,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0@[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (values, k)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = values;
        v.set(0, 1);
        (v, k)
    } else if mutation_kind == 2 {
        // set first element to 100 (max boundary)
        let mut v = values;
        v.set(0, 100);
        (v, k)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let len = values.len();
        let mut v = values;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == len,
                1 <= len <= 150_000,
                forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == 1i32,
                forall|j: int| i <= j < len ==> 1 <= #[trigger] v@[j] <= 100,
            decreases len - i,
        {
            v.set(i, 1);
            i += 1;
        }
        (v, k)
    } else if mutation_kind == 4 {
        // set all elements to 100
        let len = values.len();
        let mut v = values;
        let mut i: usize = 0;
        while i < len
            invariant
                0 <= i <= len,
                v.len() == len,
                1 <= len <= 150_000,
                forall|j: int| 0 <= j < i ==> #[trigger] v@[j] == 100i32,
                forall|j: int| i <= j < len ==> 1 <= #[trigger] v@[j] <= 100,
            decreases len - i,
        {
            v.set(i, 100);
            i += 1;
        }
        (v, k)
    } else if mutation_kind == 5 && values.len() < 150_000 {
        // grow by one element (push 50)
        let mut v = values;
        v.push(50);
        (v, k)
    } else if mutation_kind == 6 && values.len() > 1 && k < values.len() {
        // shrink by one element (pop), only if k still valid
        let mut v = values;
        v.pop();
        (v, k)
    } else if mutation_kind == 7 {
        // set last element to 1
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 1);
        (v, k)
    } else if mutation_kind == 8 {
        // set last element to 100
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 100);
        (v, k)
    } else if mutation_kind == 9 && values.len() >= 2 {
        // swap first two elements
        let mut v = values;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        (v, k)
    } else if mutation_kind == 10 && k > 1 {
        // shrink window: k - 1
        (values, k - 1)
    } else if mutation_kind == 11 && k < values.len() {
        // grow window: k + 1
        (values, k + 1)
    } else if mutation_kind == 12 {
        // window = 1 (minimum)
        (values, 1)
    } else if mutation_kind == 13 {
        // window = n (maximum, whole array)
        let n = values.len();
        (values, n)
    } else {
        // fallback: identity
        (values, k)
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

fn random_heights(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 100) as i32);
    }
    arr
}

fn mutate(values: Vec<i32>, k: usize, mutation_kind: u8) -> (Vec<i32>, usize) {
    generate_test_case(values, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(363);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |heights: Vec<i32>, k: usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", heights, k);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::min_sum_window_start(heights.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"heights": heights, "k": k},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example from description.md
    {
        let ex_heights = vec![1, 2, 6, 1, 1, 7, 1];
        let ex_k = 3usize;
        let (h, k) = mutate(ex_heights, ex_k, 0);
        emit(h, k, &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds
    let seeds: Vec<(Vec<i32>, usize)> = vec![
        (vec![1], 1),                               // single element
        (vec![1, 2], 1),                             // two elements, k=1
        (vec![1, 2], 2),                             // two elements, k=n
        (vec![100, 100, 100], 2),                    // all max values
        (vec![1, 1, 1, 1, 1], 3),                    // all min values
        (vec![1, 100, 1, 100, 1], 2),                // alternating
        (vec![100, 1, 1, 1, 100], 3),                // valley shape
        (vec![1, 1, 1, 100, 100], 2),                // ascending groups
        (vec![50, 50, 50, 50], 4),                   // k = n
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];

    // Apply every mutation to every seed
    for (h, k) in &seeds {
        for &mk in &mutation_kinds {
            let (rh, rk) = mutate(h.clone(), *k, mk);
            emit(rh, rk, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with various size classes and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),        // tiny
        (6, 20),       // small
        (21, 100),     // medium
        (101, 500),    // large
        (501, 1000),   // big
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            let n = rng.gen_range_usize(*lo, *hi);
            let arr = random_heights(&mut rng, n);
            let k = rng.gen_range_usize(1, n);
            let mk = rng.gen_range_usize(0, 13) as u8;
            let (rh, rk) = mutate(arr, k, mk);
            emit(rh, rk, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random arrays
    while count < target_count {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let arr = random_heights(&mut rng, n);
        let k = rng.gen_range_usize(1, n);
        let mk = rng.gen_range_usize(0, 13) as u8;
        let (rh, rk) = mutate(arr, k, mk);
        emit(rh, rk, &mut seen, &mut out, &mut count);
    }
}
