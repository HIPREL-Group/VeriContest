use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` for find_max_k from seed elements,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 1 (all positive, no negatives)
///   2 — set all elements to -1 (all negative, no positives)
///   3 — negate all elements
///   4 — nudge first element toward zero (skip zero)
///   5 — set last element to 1000 (max boundary)
///   6 — set last element to -1000 (min boundary)
///   7 — swap first and last elements
pub fn generate_test_case(
    elems: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= elems.len() <= 1000,
        forall |i: int| 0 <= i < elems.len() ==> -1000 <= #[trigger] elems[i] <= 1000,
        forall |i: int| 0 <= i < elems.len() ==> elems[i] != 0,
    ensures
        1 <= result.len() <= 1000,
        forall |i: int| 0 <= i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
        forall |i: int| 0 <= i < result.len() ==> result[i] != 0,
{
    let n = elems.len();

    if mutation_kind == 1 {
        // set all elements to 1
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == 1i32,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
            decreases n - k,
        {
            out.push(1);
            k = k + 1;
        }
        out
    } else if mutation_kind == 2 {
        // set all elements to -1
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall |j: int| 0 <= j < k ==> #[trigger] out[j] == -1i32,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
            decreases n - k,
        {
            out.push(-1);
            k = k + 1;
        }
        out
    } else if mutation_kind == 3 {
        // negate all elements
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> -1000 <= #[trigger] elems[i] <= 1000,
                forall |i: int| 0 <= i < elems.len() ==> elems[i] != 0,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
            decreases n - k,
        {
            out.push(-elems[k]);
            k = k + 1;
        }
        out
    } else if mutation_kind == 4 {
        // nudge first element toward zero (skip zero)
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> -1000 <= #[trigger] elems[i] <= 1000,
                forall |i: int| 0 <= i < elems.len() ==> elems[i] != 0,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
            decreases n - k,
        {
            if k == 0 {
                let v = elems[0];
                if v > 1 {
                    out.push(v - 1);
                } else if v < -1 {
                    out.push(v + 1);
                } else {
                    // v is 1 or -1; can't nudge toward zero without hitting zero
                    out.push(v);
                }
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 5 {
        // set last element to 1000
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> -1000 <= #[trigger] elems[i] <= 1000,
                forall |i: int| 0 <= i < elems.len() ==> elems[i] != 0,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
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
    } else if mutation_kind == 6 {
        // set last element to -1000
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> -1000 <= #[trigger] elems[i] <= 1000,
                forall |i: int| 0 <= i < elems.len() ==> elems[i] != 0,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(-1000);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 7 && n >= 2 {
        // swap first and last elements
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                n >= 2,
                1 <= n <= 1000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> -1000 <= #[trigger] elems[i] <= 1000,
                forall |i: int| 0 <= i < elems.len() ==> elems[i] != 0,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
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
                1 <= n <= 1000,
                out.len() == k,
                forall |i: int| 0 <= i < elems.len() ==> -1000 <= #[trigger] elems[i] <= 1000,
                forall |i: int| 0 <= i < elems.len() ==> elems[i] != 0,
                forall |j: int| 0 <= j < k ==> -1000 <= #[trigger] out[j] <= 1000,
                forall |j: int| 0 <= j < k ==> out[j] != 0,
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

/// Generate a random non-zero i32 in [-1000, 1000]
fn rand_nonzero(rng: &mut Rng) -> i32 {
    loop {
        let v = rng.gen_range_i64(-1000, 1000) as i32;
        if v != 0 {
            return v;
        }
    }
}

/// Generate a random Vec of non-zero i32 values in [-1000, 1000]
fn rand_elems(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(rand_nonzero(rng));
    }
    v
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![-1, 2, -3, 3],
        vec![-1, 10, 6, 7, -7, 1],
        vec![-10, 8, 6, 7, -2, -3],
    ];

    for nums in &examples {
        if count >= goal { break; }
        if seen.insert(nums.clone()) {
            let output = Solution::find_max_k(nums.clone());
            writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Interesting seed arrays for boundary/edge coverage
    let fixed_seeds: Vec<Vec<i32>> = vec![
        vec![1],                         // single positive
        vec![-1],                        // single negative
        vec![1, -1],                     // matching pair
        vec![1000, -1000],               // max matching pair
        vec![1, 2, 3, -1, -2, -3],      // multiple matching pairs
        vec![1, 2, 3, 4, 5],            // all positive, no matches
        vec![-1, -2, -3, -4, -5],       // all negative, no matches
        vec![999, -999, 1000, -1000],   // large matching pairs
        vec![1, -2, 3, -4, 5, -6],     // alternating, no matches
        vec![500, -500],                // medium pair
    ];

    for elems in &fixed_seeds {
        for mk in 0..=8u8 {
            if count >= goal { break; }
            let nums = generate_test_case(elems, mk);
            if seen.insert(nums.clone()) {
                let output = Solution::find_max_k(nums.clone());
                writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
                count += 1;
            }
        }
        if count >= goal { break; }
    }

    // Random test cases with diverse sizes
    while count < goal {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };

        let elems = rand_elems(&mut rng, n);
        let mk = rng.gen_u8() % 9;
        let nums = generate_test_case(&elems, mk);
        if seen.insert(nums.clone()) {
            let output = Solution::find_max_k(nums.clone());
            writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
