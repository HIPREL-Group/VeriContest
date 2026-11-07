use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 100000,
        1 <= nums2.len() <= 100000,
        forall|i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000000,
        forall|i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000000,
    ensures
        1 <= result.0.len() <= 100000,
        1 <= result.1.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000000,
{
    if mutation_kind == 0 {
        // identity
        (nums1, nums2)
    } else if mutation_kind == 1 && nums1.len() > 1 {
        // shrink nums1 by one
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2)
    } else if mutation_kind == 2 && nums2.len() > 1 {
        // shrink nums2 by one
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2)
    } else if mutation_kind == 3 {
        // set first element of nums1 to 0
        let mut n1 = nums1;
        n1.set(0, 0);
        (n1, nums2)
    } else if mutation_kind == 4 {
        // set first element of nums2 to 0
        let mut n2 = nums2;
        n2.set(0, 0);
        (nums1, n2)
    } else if mutation_kind == 5 && nums1.len() < 100000 {
        // grow nums1 by pushing 0
        let mut n1 = nums1;
        n1.push(0);
        (n1, nums2)
    } else if mutation_kind == 6 && nums2.len() < 100000 {
        // grow nums2 by pushing 0
        let mut n2 = nums2;
        n2.push(0);
        (nums1, n2)
    } else if mutation_kind == 7 {
        // set all elements of nums1 to 0
        let mut n1 = nums1;
        let mut i: usize = 0;
        while i < n1.len()
            invariant
                0 <= i <= n1.len(),
                n1.len() == nums1.len(),
                1 <= n1.len() <= 100000,
                forall|j: int| 0 <= j < i ==> n1[j] == 0,
                forall|j: int| i <= j < n1.len() ==> n1[j] == nums1[j],
            decreases n1.len() - i,
        {
            n1.set(i, 0);
            i += 1;
        }
        (n1, nums2)
    } else if mutation_kind == 8 {
        // set first element of nums1 to 1000000 (max boundary)
        let mut n1 = nums1;
        n1.set(0, 1000000);
        (n1, nums2)
    } else if mutation_kind == 9 {
        // set first element of nums2 to 1000000 (max boundary)
        let mut n2 = nums2;
        n2.set(0, 1000000);
        (nums1, n2)
    } else {
        // fallback: identity
        (nums1, nums2)
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

fn mutate(nums1: Vec<i32>, nums2: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(nums1, nums2, mutation_kind)
}

fn random_array(rng: &mut Rng, len: usize, max_val: i64, zero_frac: f64) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        let r: f64 = (rng.next_u64() % 1000) as f64 / 1000.0;
        if r < zero_frac {
            arr.push(0);
        } else {
            arr.push(rng.gen_range_i64(0, max_val) as i32);
        }
    }
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![3, 2, 0, 1, 0], vec![6, 5, 0]),
        (vec![2, 0, 2, 0], vec![1, 4]),
    ];
    for (n1, n2) in &examples {
        let result = Solution::min_sum(n1.clone(), n2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": n1, "nums2": n2},
            "output": result
        })).unwrap();
    }

    let mut generated = examples.len();

    while generated < count {
        // Size classes
        let n1_len: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let n2_len: usize = match (generated + 2) % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        // Vary zero fraction for diversity
        let zero_frac: f64 = match generated % 4 {
            0 => 0.0,   // no zeros
            1 => 0.5,   // half zeros
            2 => 1.0,   // all zeros
            _ => 0.2,   // some zeros
        };

        // Vary max values for diversity
        let max_val: i64 = if generated % 10 == 0 {
            1   // very small values
        } else if generated % 10 == 1 {
            1000000  // max boundary
        } else {
            rng.gen_range_i64(1, 1000000)
        };

        let nums1 = random_array(&mut rng, n1_len, max_val, zero_frac);
        let nums2 = random_array(&mut rng, n2_len, max_val, zero_frac);

        let mk = (generated % 10) as u8;
        let (n1, n2) = mutate(nums1, nums2, mk);

        let result = Solution::min_sum(n1.clone(), n2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": n1, "nums2": n2},
            "output": result
        })).unwrap();

        generated += 1;
    }
}
