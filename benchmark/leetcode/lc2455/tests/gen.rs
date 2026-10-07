use vstd::prelude::*;

verus! {

/// Constructs a valid `Vec<i32>` for average_value from seed elements,
/// applying mutation_kind to diversify the generated inputs.
///
/// Mutations:
///   0 — identity (copy seed elements as-is)
///   1 — set all elements to 1 (min boundary)
///   2 — set all elements to 1000 (max boundary)
///   3 — nudge first element up: if < 1000, increment by 1
///   4 — nudge first element down: if > 1, decrement by 1
///   5 — set last element to 1 (min boundary element)
///   6 — set last element to 1000 (max boundary element)
///   7 — swap first and last elements
///   8 — set all elements to 6 (smallest value divisible by 6)
///   9 — set all elements to 12 (another value divisible by 6)
pub fn generate_test_case(
    elems: &Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= elems.len() <= 1000,
        forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
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
                forall|j: int| 0 <= j < k ==> #[trigger] out[j] == 1i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            out.push(1);
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
                1 <= n <= 1000,
                out.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] out[j] == 1000i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
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
                1 <= n <= 1000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
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
                1 <= n <= 1000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            if k == 0 && elems[0] > 1 {
                out.push(elems[0] - 1);
            } else {
                out.push(elems[k]);
            }
            k = k + 1;
        }
        out
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            if k == n - 1 {
                out.push(1);
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
                1 <= n <= 1000,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
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
                1 <= n <= 1000,
                n > 1,
                out.len() == k,
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
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
    } else if mutation_kind == 8 {
        // set all elements to 6 (divisible by 6)
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] out[j] == 6i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            out.push(6);
            k = k + 1;
        }
        out
    } else if mutation_kind == 9 {
        // set all elements to 12 (another value divisible by 6)
        let mut out: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                n == elems.len(),
                1 <= n <= 1000,
                out.len() == k,
                forall|j: int| 0 <= j < k ==> #[trigger] out[j] == 12i32,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
            decreases n - k,
        {
            out.push(12);
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
                forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 1000,
                forall|j: int| 0 <= j < k ==> 1 <= #[trigger] out[j] <= 1000,
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

struct Solution;
include!("../code.rs");

fn random_elems(rng: &mut Rng, len: usize) -> Vec<i32> {
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2455);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 3, 6, 10, 12, 15],
        vec![1, 2, 4, 7, 10],
    ];

    for nums in &examples {
        if count >= goal { break; }
        let key = format!("{:?}", nums);
        if seen.insert(key) {
            let output = Solution::average_value(nums.clone());
            writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
            count += 1;
        }
    }

    // Generate diverse test cases
    while count < goal {
        // Size classes for array lengths
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 1000),   // max
        };

        let elems = random_elems(&mut rng, n);
        let mk = rng.gen_u8() % 11;
        let nums = generate_test_case(&elems, mk);
        let key = format!("{:?}", nums);
        if seen.insert(key) {
            let output = Solution::average_value(nums.clone());
            writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
            count += 1;
        }
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
