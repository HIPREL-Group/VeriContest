use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` for special_array from seed elements,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 0 (no element >= any x >= 1)
///   2 — set all elements to 1000 (max boundary)
///   3 — nudge first element up: if < 1000, increment by 1
///   4 — nudge first element down: if > 0, decrement by 1
///   5 — set last element to 0 (min boundary element)
///   6 — set last element to 1000 (max boundary element)
///   7 — swap first and last elements
pub fn generate_test_case(
    elems: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= elems.len() <= 100,
        forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1000,
    ensures
        1 <= result.len() <= 100,
        forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
{
    let n = elems.len();

    if mutation_kind == 1 {
        // set all elements to 0
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == 0i32,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            out.push(0);
            k = k + 1;
        }
        out
    } else if mutation_kind == 2 {
        // set all elements to 1000
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == 1000i32,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            out.push(1000);
            k = k + 1;
        }
        out
    } else if mutation_kind == 3 {
        // nudge first element up
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            if k == 0 && elems[0] < 1000 {
                out.push(elems[0] + 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 4 {
        // nudge first element down
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            if k == 0 && elems[0] > 0 {
                out.push(elems[0] - 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 5 {
        // set last element to 0
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(0);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 6 {
        // set last element to 1000
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(1000);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 7 && n > 1 {
        // swap first and last elements
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                n > 1,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            if k == 0 {
                out.push(elems[n - 1]);
            } else if k == n - 1 {
                out.push(elems[0]);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else {
        // identity (mutation_kind == 0 or fallback)
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 100,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 1000,
                forall |j: int| 0 <= j < k ==> 0 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            out.push(elems[k]);
            k = k + 1;
        }
        out
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn mutate(elems: &Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(elems, mutation_kind)
}

fn random_elems(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1608);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::special_array(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Hand-crafted seeds from the problem examples and edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![3, 5],                     // example 1: output 2
        vec![0, 0],                     // example 2: output -1
        vec![0, 4, 3, 0, 4],           // example 3: output 3
        vec![1],                        // single element
        vec![0],                        // single zero
        vec![1000],                     // single max
        vec![1, 1, 1],                 // all ones
        vec![0, 0, 0, 0, 0],          // all zeros
        vec![100, 100, 100, 100, 100], // all same large
        vec![1, 2, 3, 4, 5],          // increasing
        vec![5, 4, 3, 2, 1],          // decreasing
        vec![2, 2],                    // special: x=2, count(>=2)=2
        vec![3, 3, 3],                // special: x=3, count(>=3)=3
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10], // range 0..10
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with varied sizes and random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),     // tiny
        (4, 10),    // small
        (11, 30),   // medium
        (31, 60),   // large
        (61, 100),  // max
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            let len = rng.gen_range_usize(*lo, *hi);
            let s = random_elems(&mut rng, len);
            let mk = rng.gen_range_usize(0, 7) as u8;
            let result = mutate(&s, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Boundary-heavy random cases: values near 0 and 1000
    for _ in 0..20 {
        let len = rng.gen_range_usize(1, 100);
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            let val = match rng.gen_range_usize(0, 4) {
                0 => 0,
                1 => 1000,
                2 => rng.gen_range_i64(0, 5) as i32,
                3 => rng.gen_range_i64(995, 1000) as i32,
                _ => rng.gen_range_i64(0, 1000) as i32,
            };
            v.push(val);
        }
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(&v, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 100);
        let s = random_elems(&mut rng, len);
        emit(mutate(&s, 0), &mut seen, &mut out, &mut count);
    }
}
