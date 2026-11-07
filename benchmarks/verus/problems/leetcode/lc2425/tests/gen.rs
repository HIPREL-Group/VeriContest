use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 100_000,
        1 <= nums2.len() <= 100_000,
        forall|i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1_000_000_000,
        forall|j: int| 0 <= j < nums2.len() ==> 0 <= #[trigger] nums2[j] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|j: int| 0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        (nums1, nums2)
    } else if mutation_kind == 1 {
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 0);
        (n1, nums2)
    } else if mutation_kind == 2 {
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 0);
        (nums1, n2)
    } else if mutation_kind == 3 {
        let mut n1 = nums1;
        let ghost orig_len = n1.len();
        let mut i: usize = 0;
        while i < n1.len()
            invariant
                0 <= i <= n1.len(),
                n1.len() == orig_len,
                1 <= n1.len() <= 100_000,
                forall|k: int| 0 <= k < i ==> n1[k] == 0i32,
                forall|k: int| i <= k < n1.len() ==> n1[k] == nums1[k],
            decreases n1.len() - i,
        {
            n1.set(i, 0);
            i += 1;
        }
        (n1, nums2)
    } else if mutation_kind == 4 {
        let mut n2 = nums2;
        let ghost orig_len = n2.len();
        let mut j: usize = 0;
        while j < n2.len()
            invariant
                0 <= j <= n2.len(),
                n2.len() == orig_len,
                1 <= n2.len() <= 100_000,
                forall|k: int| 0 <= k < j ==> n2[k] == 0i32,
                forall|k: int| j <= k < n2.len() ==> n2[k] == nums2[k],
            decreases n2.len() - j,
        {
            n2.set(j, 0);
            j += 1;
        }
        (nums1, n2)
    } else if mutation_kind == 5 && nums1.len() < 100_000 {
        let mut n1 = nums1;
        n1.push(0);
        (n1, nums2)
    } else if mutation_kind == 6 && nums2.len() < 100_000 {
        let mut n2 = nums2;
        n2.push(0);
        (nums1, n2)
    } else if mutation_kind == 7 && nums1.len() > 1 {
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2)
    } else if mutation_kind == 8 && nums2.len() > 1 {
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2)
    } else if mutation_kind == 9 {
        let mut n1 = nums1;
        n1.set(0, 1_000_000_000);
        (n1, nums2)
    } else if mutation_kind == 10 {
        let mut n2 = nums2;
        n2.set(0, 1_000_000_000);
        (nums1, n2)
    } else if mutation_kind == 11 {
        let mut n1 = nums1;
        let last = n1.len() - 1;
        if n1[last] < 1_000_000_000 {
            n1.set(last, n1[last] + 1);
        }
        (n1, nums2)
    } else if mutation_kind == 12 {
        let mut n2 = nums2;
        let last = n2.len() - 1;
        if n2[last] > 0 {
            n2.set(last, n2[last] - 1);
        }
        (nums1, n2)
    } else {
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

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(lo, hi) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2425);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |n1: Vec<i32>, n2: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}|{:?}", n1, n2);
        if !seen.insert(key) { return; }
        let output = Solution::xor_all_nums(n1.clone(), n2.clone());
        writeln!(out, "{}", json!({"input": {"nums1": n1, "nums2": n2}, "output": output})).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    for (n1, n2) in vec![
        (vec![2, 1, 3], vec![10, 2, 5, 0]),
        (vec![1, 2], vec![3, 4]),
    ] {
        emit(n1, n2, &mut seen, &mut out, &mut total);
    }

    // Seed arrays for mutation
    let seed_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![0], vec![0]),
        (vec![1_000_000_000], vec![1_000_000_000]),
        (vec![0, 0, 0], vec![0, 0, 0]),
        (vec![1], vec![1]),
        (vec![999_999_999], vec![1]),
        (vec![123, 456, 789], vec![321, 654]),
        (vec![0, 1_000_000_000], vec![500_000_000]),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];

    for (n1, n2) in &seed_pairs {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let (r1, r2) = mutate(n1.clone(), n2.clone(), mk);
            emit(r1, r2, &mut seen, &mut out, &mut total);
        }
    }

    // Random arrays with diverse sizes and random mutations
    while total < count {
        let len1: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10_000),
        };
        let len2: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10_000),
        };
        let (lo, hi) = if rng.gen_range_usize(0, 4) == 0 {
            (0i64, 1i64)
        } else {
            (0i64, 1_000_000_000i64)
        };
        let n1 = random_array(&mut rng, len1, lo, hi);
        let n2 = random_array(&mut rng, len2, lo, hi);
        let mk = rng.gen_range_usize(0, 13) as u8;
        let (r1, r2) = mutate(n1, n2, mk);
        emit(r1, r2, &mut seen, &mut out, &mut total);
    }
}
