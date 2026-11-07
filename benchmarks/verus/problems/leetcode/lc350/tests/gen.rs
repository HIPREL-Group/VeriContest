use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elems1: &Vec<i32>,
    elems2: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= elems1.len() <= 1000,
        1 <= elems2.len() <= 1000,
        forall|i: int| 0 <= i < elems1.len() ==> 0 <= #[trigger] elems1[i] <= 1000,
        forall|i: int| 0 <= i < elems2.len() ==> 0 <= #[trigger] elems2[i] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
{
    let mut nums1: Vec<i32> = Vec::new();
    let mut nums2: Vec<i32> = Vec::new();

    // Copy elems1 into nums1
    let mut i: usize = 0;
    while i < elems1.len()
        invariant
            0 <= i <= elems1.len(),
            nums1.len() == i,
            forall|k: int| 0 <= k < nums1.len() ==> 0 <= #[trigger] nums1[k] <= 1000,
            forall|k: int| 0 <= k < nums1.len() ==> nums1[k] == elems1[k],
            forall|k: int| 0 <= k < elems1.len() ==> 0 <= #[trigger] elems1[k] <= 1000,
        decreases elems1.len() - i,
    {
        nums1.push(elems1[i]);
        i = i + 1;
    }

    // Copy elems2 into nums2
    let mut j: usize = 0;
    while j < elems2.len()
        invariant
            0 <= j <= elems2.len(),
            nums2.len() == j,
            forall|k: int| 0 <= k < nums2.len() ==> 0 <= #[trigger] nums2[k] <= 1000,
            forall|k: int| 0 <= k < nums2.len() ==> nums2[k] == elems2[k],
            forall|k: int| 0 <= k < elems2.len() ==> 0 <= #[trigger] elems2[k] <= 1000,
        decreases elems2.len() - j,
    {
        nums2.push(elems2[j]);
        j = j + 1;
    }

    if mutation_kind == 1 && nums1.len() < 1000 {
        // Grow nums1: push element 0
        nums1.push(0i32);
    } else if mutation_kind == 2 && nums2.len() < 1000 {
        // Grow nums2: push element 0
        nums2.push(0i32);
    } else if mutation_kind == 3 && nums1.len() > 1 {
        // Shrink nums1
        let old_len = nums1.len();
        let _ = nums1.pop();
        proof {
            assert(nums1.len() == old_len - 1);
            assert forall|k: int| 0 <= k < nums1.len() implies 0 <= #[trigger] nums1[k] <= 1000 by {};
        }
    } else if mutation_kind == 4 && nums2.len() > 1 {
        // Shrink nums2
        let old_len = nums2.len();
        let _ = nums2.pop();
        proof {
            assert(nums2.len() == old_len - 1);
            assert forall|k: int| 0 <= k < nums2.len() implies 0 <= #[trigger] nums2[k] <= 1000 by {};
        }
    } else if mutation_kind == 5 {
        // Set first element of nums1 to 0
        nums1.set(0, 0i32);
        proof {
            assert forall|k: int| 0 <= k < nums1.len() implies 0 <= #[trigger] nums1[k] <= 1000 by {};
        }
    } else if mutation_kind == 6 {
        // Set first element of nums2 to 1000
        nums2.set(0, 1000i32);
        proof {
            assert forall|k: int| 0 <= k < nums2.len() implies 0 <= #[trigger] nums2[k] <= 1000 by {};
        }
    } else if mutation_kind == 7 {
        // Set first element of nums1 to 1000 and first of nums2 to 1000 (match)
        nums1.set(0, 1000i32);
        nums2.set(0, 1000i32);
        proof {
            assert forall|k: int| 0 <= k < nums1.len() implies 0 <= #[trigger] nums1[k] <= 1000 by {};
            assert forall|k: int| 0 <= k < nums2.len() implies 0 <= #[trigger] nums2[k] <= 1000 by {};
        }
    } else if mutation_kind == 8 && nums1.len() >= 2 {
        // Swap first two elements of nums1
        let a = nums1[0];
        let b = nums1[1];
        nums1.set(0, b);
        nums1.set(1, a);
        proof {
            assert forall|k: int| 0 <= k < nums1.len() implies 0 <= #[trigger] nums1[k] <= 1000 by {};
        }
    }
    // mutation_kind == 0 or fallback: identity (no mutation)

    (nums1, nums2)
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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_array(rng: &mut Rng, len: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut arr = Vec::new();
    for _ in 0..len {
        arr.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count_goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($e1:expr, $e2:expr, $mk:expr) => {
            if count < count_goal {
                let e1_val: Vec<i32> = $e1;
                let e2_val: Vec<i32> = $e2;
                let mk_val: u8 = $mk;
                let (nums1_out, nums2_out) = generate_test_case(&e1_val, &e2_val, mk_val);
                let result = Solution::intersect(nums1_out.clone(), nums2_out.clone());
                let line = json!({
                    "input": {"nums1": nums1_out, "nums2": nums2_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    emit!(vec![1, 2, 2, 1], vec![2, 2], 0);
    emit!(vec![4, 9, 5], vec![9, 4, 9, 8, 4], 0);

    // ---- Edge cases: single element arrays ----
    emit!(vec![0], vec![0], 0);
    emit!(vec![1000], vec![1000], 0);
    emit!(vec![0], vec![1000], 0);
    emit!(vec![5], vec![5], 0);

    // ---- No intersection ----
    emit!(vec![1, 2, 3], vec![4, 5, 6], 0);

    // ---- Full intersection (identical arrays) ----
    emit!(vec![1, 2, 3], vec![1, 2, 3], 0);

    // ---- Duplicate-heavy ----
    emit!(vec![1, 1, 1, 1], vec![1, 1], 0);
    emit!(vec![3, 3, 3], vec![3, 3, 3, 3], 0);

    // ---- All mutations on a small example ----
    for mk in 0u8..=8 {
        emit!(vec![1, 2, 3, 4, 5], vec![3, 4, 5, 6, 7], mk);
    }

    // ---- Boundary values with mutations ----
    for mk in 0u8..=8 {
        emit!(vec![0, 0, 1000, 1000], vec![0, 500, 1000], mk);
    }

    // ---- Random tiny arrays (1-5 elements), all mutations ----
    for _ in 0..4 {
        let n1 = rng.gen_range_usize(1, 5);
        let n2 = rng.gen_range_usize(1, 5);
        let e1 = random_array(&mut rng, n1, 0, 1000);
        let e2 = random_array(&mut rng, n2, 0, 1000);
        for mk in 0u8..=8 {
            emit!(e1.clone(), e2.clone(), mk);
        }
    }

    // ---- Random small arrays (5-20 elements), random mutations ----
    for _ in 0..8 {
        let n1 = rng.gen_range_usize(5, 20);
        let n2 = rng.gen_range_usize(5, 20);
        let e1 = random_array(&mut rng, n1, 0, 1000);
        let e2 = random_array(&mut rng, n2, 0, 1000);
        let mk = (rng.next_u64() % 9) as u8;
        emit!(e1.clone(), e2.clone(), mk);
        emit!(e1.clone(), e2.clone(), 0);
    }

    // ---- Random medium arrays (50-200 elements), random mutations ----
    for _ in 0..6 {
        let n1 = rng.gen_range_usize(50, 200);
        let n2 = rng.gen_range_usize(50, 200);
        let e1 = random_array(&mut rng, n1, 0, 1000);
        let e2 = random_array(&mut rng, n2, 0, 1000);
        let mk = (rng.next_u64() % 9) as u8;
        emit!(e1.clone(), e2.clone(), mk);
    }

    // ---- Random large arrays (500-1000 elements), random mutations ----
    for _ in 0..4 {
        let n1 = rng.gen_range_usize(500, 1000);
        let n2 = rng.gen_range_usize(500, 1000);
        let e1 = random_array(&mut rng, n1, 0, 1000);
        let e2 = random_array(&mut rng, n2, 0, 1000);
        let mk = (rng.next_u64() % 9) as u8;
        emit!(e1.clone(), e2.clone(), mk);
    }

    // ---- Max size arrays ----
    emit!(random_array(&mut rng, 1000, 0, 1000), random_array(&mut rng, 1000, 0, 1000), 0);

    // ---- Narrow value range (high overlap) ----
    for _ in 0..4 {
        let n1 = rng.gen_range_usize(10, 100);
        let n2 = rng.gen_range_usize(10, 100);
        let e1 = random_array(&mut rng, n1, 0, 5);
        let e2 = random_array(&mut rng, n2, 0, 5);
        let mk = (rng.next_u64() % 9) as u8;
        emit!(e1.clone(), e2.clone(), mk);
    }

    // ---- Fill remaining with random ----
    while count < count_goal {
        let n1 = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let n2 = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 500),
            _ => rng.gen_range_usize(500, 1000),
        };
        let e1 = random_array(&mut rng, n1, 0, 1000);
        let e2 = random_array(&mut rng, n2, 0, 1000);
        let mk = (rng.next_u64() % 9) as u8;
        emit!(e1, e2, mk);
    }

    eprintln!("Generated {} test cases", count);
}
