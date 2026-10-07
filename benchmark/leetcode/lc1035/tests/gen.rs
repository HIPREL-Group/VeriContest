use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 500,
        1 <= nums2.len() <= 500,
        forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 2000,
        forall|i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 2000,
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1.len() <= 500,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 2000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 2000,
{
    if mutation_kind == 0 {
        // identity
        (nums1, nums2)
    } else if mutation_kind == 1 {
        // set first element of nums1 to 1 (min boundary)
        let mut n1 = nums1;
        n1.set(0, 1);
        (n1, nums2)
    } else if mutation_kind == 2 {
        // set first element of nums1 to 2000 (max boundary)
        let mut n1 = nums1;
        n1.set(0, 2000);
        (n1, nums2)
    } else if mutation_kind == 3 {
        // swap arrays
        (nums2, nums1)
    } else if mutation_kind == 4 && nums1.len() > 1 {
        // shrink nums1
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2)
    } else if mutation_kind == 5 && nums2.len() > 1 {
        // shrink nums2
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2)
    } else if mutation_kind == 6 && nums1.len() < 500 {
        // grow nums1
        let mut n1 = nums1;
        n1.push(1);
        (n1, nums2)
    } else if mutation_kind == 7 && nums2.len() < 500 {
        // grow nums2
        let mut n2 = nums2;
        n2.push(1);
        (nums1, n2)
    } else if mutation_kind == 8 {
        // set last element of nums1 to match first element of nums2
        let mut n1 = nums1;
        let last = n1.len() - 1;
        let val = nums2[0];
        n1.set(last, val);
        (n1, nums2)
    } else if mutation_kind == 9 {
        // set first element of nums2 to 1 (min boundary)
        let mut n2 = nums2;
        n2.set(0, 1);
        (nums1, n2)
    } else if mutation_kind == 10 {
        // set first element of nums2 to 2000 (max boundary)
        let mut n2 = nums2;
        n2.set(0, 2000);
        (nums1, n2)
    } else {
        // fallback
        (nums1, nums2)
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

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 2000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1035);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n1: Vec<i32>, n2: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}|{:?}", n1, n2);
        if *count >= goal || !seen.insert(key) {
            return;
        }
        let output = Solution::max_uncrossed_lines(n1.clone(), n2.clone());
        writeln!(out, "{}", json!({"input": {"nums1": n1, "nums2": n2}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1,4,2], vec![1,2,4]),
        (vec![2,5,1,2,5], vec![10,5,2,1,5,2]),
        (vec![1,3,7,1,7,5], vec![1,9,2,5,1]),
    ];
    for (n1, n2) in &examples {
        for mk in 0..=10u8 {
            let (r1, r2) = generate_test_case(n1.clone(), n2.clone(), mk);
            emit(r1, r2, &mut seen, &mut out, &mut count);
        }
    }

    // Seed arrays with interesting patterns
    let seed_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),                         // single matching
        (vec![1], vec![2]),                         // single non-matching
        (vec![1, 2, 3], vec![1, 2, 3]),             // identical
        (vec![1, 2, 3], vec![3, 2, 1]),             // reversed
        (vec![2000], vec![2000]),                    // max boundary value
        (vec![1, 1, 1], vec![1, 1, 1]),             // all same
        (vec![1, 2], vec![3, 4]),                    // no overlap
        (vec![1, 2, 3, 4, 5], vec![5, 4, 3, 2, 1]), // reversed longer
    ];
    for (n1, n2) in &seed_pairs {
        for mk in 0..=10u8 {
            let (r1, r2) = generate_test_case(n1.clone(), n2.clone(), mk);
            emit(r1, r2, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with varying sizes
    while count < goal {
        let size_class = count % 5;
        let len1 = match size_class {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 500),   // max
        };
        let len2 = match (count / 5) % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 500),
        };
        let n1 = random_array(&mut rng, len1);
        let n2 = random_array(&mut rng, len2);
        let mk = (rng.next_u64() % 12) as u8;
        let (r1, r2) = generate_test_case(n1, n2, mk);
        emit(r1, r2, &mut seen, &mut out, &mut count);
    }
}
