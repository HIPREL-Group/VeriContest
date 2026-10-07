use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= nums1.len() <= 50,
        1 <= nums2.len() <= 50,
        forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 50,
        forall|j: int| 0 <= j < nums2.len() ==> 1 <= #[trigger] nums2[j] <= 50,
        1 <= k <= 50,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1.len() <= 50,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 50,
        forall|j: int| 0 <= j < result.1.len() ==> 1 <= #[trigger] result.1[j] <= 50,
        1 <= result.2 <= 50,
{
    if mutation_kind == 0 {
        // identity
        (nums1, nums2, k)
    } else if mutation_kind == 1 {
        // set last element of nums1 to 1
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 1);
        (n1, nums2, k)
    } else if mutation_kind == 2 {
        // set last element of nums1 to 50
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 50);
        (n1, nums2, k)
    } else if mutation_kind == 3 {
        // set last element of nums2 to 1
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 1);
        (nums1, n2, k)
    } else if mutation_kind == 4 {
        // set last element of nums2 to 50
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 50);
        (nums1, n2, k)
    } else if mutation_kind == 5 {
        // set k to 1
        (nums1, nums2, 1)
    } else if mutation_kind == 6 {
        // set k to 50
        (nums1, nums2, 50)
    } else if mutation_kind == 7 && nums1.len() < 50 {
        // grow nums1 by pushing 1
        let mut n1 = nums1;
        n1.push(1);
        (n1, nums2, k)
    } else if mutation_kind == 8 && nums1.len() > 1 {
        // shrink nums1
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2, k)
    } else if mutation_kind == 9 && nums2.len() < 50 {
        // grow nums2 by pushing 1
        let mut n2 = nums2;
        n2.push(1);
        (nums1, n2, k)
    } else if mutation_kind == 10 && nums2.len() > 1 {
        // shrink nums2
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2, k)
    } else if mutation_kind == 11 && nums1.len() >= 2 {
        // swap first and last of nums1
        let mut n1 = nums1;
        let last = n1.len() - 1;
        let first_val = n1[0];
        let last_val = n1[last];
        n1.set(0, last_val);
        n1.set(last, first_val);
        (n1, nums2, k)
    } else if mutation_kind == 12 && nums2.len() >= 2 {
        // swap first and last of nums2
        let mut n2 = nums2;
        let last = n2.len() - 1;
        let first_val = n2[0];
        let last_val = n2[last];
        n2.set(0, last_val);
        n2.set(last, first_val);
        (nums1, n2, k)
    } else {
        // fallback: identity
        (nums1, nums2, k)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 50) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let num_mutations: u8 = 13;

    let mut emit = |nums1: Vec<i32>, nums2: Vec<i32>, k: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}|{:?}|{}", nums1, nums2, k);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::number_of_pairs(nums1.clone(), nums2.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2, "k": k},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![1, 3, 4], vec![1, 3, 4], 1),
        (vec![1, 2, 4, 12], vec![2, 4], 3),
    ];
    for (n1, n2, k) in examples {
        emit(n1, n2, k, &mut seen, &mut out, &mut count);
    }

    // Seed pool: interesting arrays
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],
        vec![50],
        vec![1, 2, 3],
        vec![48, 49, 50],
        vec![1, 1, 1, 1, 1],
        vec![50, 50, 50, 50, 50],
        vec![6, 12, 24, 48],
        vec![2, 4, 8, 16, 32],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
    ];
    let seed_ks: Vec<i32> = vec![1, 2, 5, 10, 25, 50];

    // Cross-product of seed arrays × seed arrays × k values × mutations
    for n1 in &seed_arrays {
        for n2 in &seed_arrays {
            for &k in &seed_ks {
                for mk in 0..num_mutations {
                    if count >= count_target { break; }
                    let (r1, r2, rk) = generate_test_case(n1.clone(), n2.clone(), k, mk);
                    emit(r1, r2, rk, &mut seen, &mut out, &mut count);
                }
            }
        }
    }

    // Random inputs with random mutations
    while count < count_target {
        let len1 = match count % 5 {
            0 => rng.gen_range_usize(1, 3),    // tiny
            1 => rng.gen_range_usize(1, 10),   // small
            2 => rng.gen_range_usize(10, 25),  // medium
            3 => rng.gen_range_usize(25, 40),  // large
            _ => rng.gen_range_usize(40, 50),  // max
        };
        let len2 = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 25),
            3 => rng.gen_range_usize(25, 40),
            _ => rng.gen_range_usize(40, 50),
        };
        let n1 = random_vec(&mut rng, len1);
        let n2 = random_vec(&mut rng, len2);
        let k = if count % 5 == 0 {
            *[1i32, 50, 25, 1, 50].get(count % 5).unwrap()
        } else {
            rng.gen_range_i64(1, 50) as i32
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (r1, r2, rk) = generate_test_case(n1, n2, k, mk);
        emit(r1, r2, rk, &mut seen, &mut out, &mut count);
    }
}
