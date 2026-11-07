use vstd::prelude::*;

verus! {

/// Constructs valid `(Vec<i32>, i32)` inputs for get_averages from seed
/// elements and k, applying mutation_kind to diversify.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 0
///   2 — set all elements to 100_000 (max boundary)
///   3 — nudge first element up: if < 100_000, increment by 1
///   4 — nudge first element down: if > 0, decrement by 1
///   5 — set last element to 0 (min boundary element)
///   6 — set last element to 100_000 (max boundary element)
///   7 — swap first and last elements
///   8 — set k to 0
///   9 — set k to min(100_000, nums.len() - 1) so window covers entire array
pub fn generate_test_case(
    elems: &Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= elems.len() <= 100_000,
        0 <= k <= 100_000,
        forall|i: int| 0 <= i < elems.len() ==> 0 <= #[trigger] elems[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100_000,
{
    let n = elems.len();

    if mutation_kind == 1 {
        // set all elements to 0
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < j ==> #[trigger] out[idx] == 0i32,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            out.push(0);
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 2 {
        // set all elements to 100_000
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < j ==> #[trigger] out[idx] == 100_000i32,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            out.push(100_000);
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 3 {
        // nudge first element up
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            if j == 0 && elems[0] < 100_000 {
                out.push(elems[0] + 1);
            } else {
                out.push(elems[j]);
            }
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 4 {
        // nudge first element down
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            if j == 0 && elems[0] > 0 {
                out.push(elems[0] - 1);
            } else {
                out.push(elems[j]);
            }
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 5 {
        // set last element to 0
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            if j == n - 1 {
                out.push(0);
            } else {
                out.push(elems[j]);
            }
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 6 {
        // set last element to 100_000
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            if j == n - 1 {
                out.push(100_000);
            } else {
                out.push(elems[j]);
            }
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 7 && n >= 2 {
        // swap first and last elements
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                n >= 2,
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            if j == 0 {
                out.push(elems[n - 1]);
            } else if j == n - 1 {
                out.push(elems[0]);
            } else {
                out.push(elems[j]);
            }
            j = j + 1;
        }
        (out, k)
    } else if mutation_kind == 8 {
        // set k to 0
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            out.push(elems[j]);
            j = j + 1;
        }
        (out, 0i32)
    } else if mutation_kind == 9 {
        // set k so window covers as much as possible
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            out.push(elems[j]);
            j = j + 1;
        }
        // k = (n - 1) / 2 so the window spans the entire array (or close)
        let new_k = ((n - 1) / 2) as i32;
        (out, new_k)
    } else {
        // identity (mutation_kind == 0 or fallback)
        let mut out: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == elems.len(),
                1 <= n <= 100_000,
                out.len() == j,
                forall|idx: int| 0 <= idx < elems.len() ==> 0 <= #[trigger] elems[idx] <= 100_000,
                forall|idx: int| 0 <= idx < j ==> 0 <= #[trigger] out[idx] <= 100_000,
            decreases n - j,
        {
            out.push(elems[j]);
            j = j + 1;
        }
        (out, k)
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

fn mutate(elems: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(&elems, k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_elems(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 100_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2090);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}|{}", nums, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::get_averages(nums.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "k": k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // ---- Example inputs from description.md ----
    {
        let (nums, k) = mutate(vec![7, 4, 3, 9, 1, 8, 5, 2, 6], 3, 0);
        emit(nums, k, &mut seen, &mut out, &mut count);
    }
    {
        let (nums, k) = mutate(vec![100000], 0, 0);
        emit(nums, k, &mut seen, &mut out, &mut count);
    }
    {
        let (nums, k) = mutate(vec![8], 100000, 0);
        emit(nums, k, &mut seen, &mut out, &mut count);
    }

    // ---- Structured seeds × all mutations ----
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![0], 0),
        (vec![100000], 0),
        (vec![1, 2, 3, 4, 5], 2),
        (vec![1, 2, 3, 4, 5], 0),
        (vec![1, 2, 3, 4, 5, 6, 7], 3),
        (vec![0, 0, 0, 0, 0], 1),
        (vec![100000, 100000, 100000], 1),
        (vec![50000; 10], 4),
        (vec![1; 20], 9),
        (vec![99999, 1, 50000, 25000, 75000], 2),
        (vec![0, 100000, 0, 100000, 0, 100000, 0], 3),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    for (seed_elems, seed_k) in &seeds {
        for &mk in &mutation_kinds {
            let (nums, k) = mutate(seed_elems.clone(), *seed_k, mk);
            emit(nums, k, &mut seen, &mut out, &mut count);
        }
    }

    // ---- Random inputs across size classes ----
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // very large
        };
        let k_val = match count % 4 {
            0 => 0i32,
            1 => rng.gen_range_i64(0, (n as i64).min(100_000)) as i32,
            2 => rng.gen_range_i64(0, 100_000) as i32,  // may exceed n, giving all -1
            _ => ((n as i32 - 1) / 2).max(0),           // window fits exactly
        };
        let elems = random_elems(&mut rng, n);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (nums, k) = mutate(elems, k_val, mk);
        emit(nums, k, &mut seen, &mut out, &mut count);
    }
}
