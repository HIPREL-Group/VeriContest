use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    nums3: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 100,
        1 <= nums2.len() <= 100,
        1 <= nums3.len() <= 100,
        forall|i: int| 0 <= i < nums1.len() ==> 1 <= #[trigger] nums1[i] <= 100,
        forall|i: int| 0 <= i < nums2.len() ==> 1 <= #[trigger] nums2[i] <= 100,
        forall|i: int| 0 <= i < nums3.len() ==> 1 <= #[trigger] nums3[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.1.len() <= 100,
        1 <= result.2.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (nums1, nums2, nums3)
    } else if mutation_kind == 1 {
        // copy first element of nums1 into nums2 (forces overlap)
        let mut n2 = nums2;
        let v = nums1[0];
        n2.set(0, v);
        (nums1, n2, nums3)
    } else if mutation_kind == 2 {
        // copy first element of nums1 into nums3 (forces overlap)
        let mut n3 = nums3;
        let v = nums1[0];
        n3.set(0, v);
        (nums1, nums2, n3)
    } else if mutation_kind == 3 {
        // copy first element of nums2 into nums3 (forces overlap)
        let mut n3 = nums3;
        let v = nums2[0];
        n3.set(0, v);
        (nums1, nums2, n3)
    } else if mutation_kind == 4 {
        // copy first element of nums1 into both nums2 and nums3 (triple overlap)
        let mut n2 = nums2;
        let mut n3 = nums3;
        let v = nums1[0];
        n2.set(0, v);
        n3.set(0, v);
        (nums1, n2, n3)
    } else if mutation_kind == 5 {
        // set all elements of nums1 to 1
        let mut n1 = nums1;
        let mut i: usize = 0;
        while i < n1.len()
            invariant
                0 <= i <= n1.len(),
                n1.len() == nums1.len(),
                1 <= n1.len() <= 100,
                forall|j: int| 0 <= j < i ==> n1[j] == 1i32,
                forall|j: int| i <= j < n1.len() ==> n1[j] == nums1[j],
            decreases n1.len() - i,
        {
            n1.set(i, 1);
            i += 1;
        }
        (n1, nums2, nums3)
    } else if mutation_kind == 6 {
        // set all elements of all arrays to 100 (boundary)
        let mut n1 = nums1;
        let mut i: usize = 0;
        while i < n1.len()
            invariant
                0 <= i <= n1.len(),
                n1.len() == nums1.len(),
                1 <= n1.len() <= 100,
                forall|j: int| 0 <= j < i ==> n1[j] == 100i32,
                forall|j: int| i <= j < n1.len() ==> n1[j] == nums1[j],
            decreases n1.len() - i,
        {
            n1.set(i, 100);
            i += 1;
        }
        let mut n2 = nums2;
        let mut i2: usize = 0;
        while i2 < n2.len()
            invariant
                0 <= i2 <= n2.len(),
                n2.len() == nums2.len(),
                1 <= n2.len() <= 100,
                forall|j: int| 0 <= j < i2 ==> n2[j] == 100i32,
                forall|j: int| i2 <= j < n2.len() ==> n2[j] == nums2[j],
            decreases n2.len() - i2,
        {
            n2.set(i2, 100);
            i2 += 1;
        }
        let mut n3 = nums3;
        let mut i3: usize = 0;
        while i3 < n3.len()
            invariant
                0 <= i3 <= n3.len(),
                n3.len() == nums3.len(),
                1 <= n3.len() <= 100,
                forall|j: int| 0 <= j < i3 ==> n3[j] == 100i32,
                forall|j: int| i3 <= j < n3.len() ==> n3[j] == nums3[j],
            decreases n3.len() - i3,
        {
            n3.set(i3, 100);
            i3 += 1;
        }
        (n1, n2, n3)
    } else if mutation_kind == 7 {
        // nudge first element of nums1: if < 100, increment
        let mut n1 = nums1;
        if n1[0] < 100 {
            n1.set(0, n1[0] + 1);
        }
        (n1, nums2, nums3)
    } else if mutation_kind == 8 && nums1.len() < 100 {
        // grow nums1 by appending element from nums2 (forces overlap)
        let mut n1 = nums1;
        let v = nums2[0];
        n1.push(v);
        (n1, nums2, nums3)
    } else if mutation_kind == 9 && nums1.len() > 1 {
        // shrink nums1
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2, nums3)
    } else {
        // fallback: identity
        (nums1, nums2, nums3)
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

fn mutate(
    nums1: Vec<i32>, nums2: Vec<i32>, nums3: Vec<i32>, mutation_kind: u8,
) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    generate_test_case(nums1, nums2, nums3, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 100) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2032);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n1: Vec<i32>, n2: Vec<i32>, n3: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}|{:?}|{:?}", n1, n2, n3);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::two_out_of_three(n1.clone(), n2.clone(), n3.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": n1, "nums2": n2, "nums3": n3},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<(Vec<i32>, Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 1, 3, 2], vec![2, 3], vec![3]),
        (vec![3, 1], vec![2, 3], vec![1, 2]),
        (vec![1, 2, 2], vec![4, 3, 3], vec![5]),
    ];
    for (n1, n2, n3) in examples {
        emit(n1, n2, n3, &mut seen, &mut out, &mut count);
    }

    // Seed arrays for mutation
    let seeds: Vec<(Vec<i32>, Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1], vec![1]),
        (vec![100], vec![100], vec![100]),
        (vec![1], vec![2], vec![3]),
        (vec![50, 50], vec![50, 51], vec![51, 52]),
        (vec![1, 2, 3, 4, 5], vec![5, 6, 7, 8, 9], vec![9, 10, 1, 2, 3]),
        (vec![1, 1, 1], vec![2, 2, 2], vec![3, 3, 3]),
        (vec![99, 100], vec![1, 2], vec![100, 1]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for (n1, n2, n3) in &seeds {
        for &mk in &mutation_kinds {
            let (r1, r2, r3) = mutate(n1.clone(), n2.clone(), n3.clone(), mk);
            emit(r1, r2, r3, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations
    for _ in 0..200 {
        if count >= target { break; }
        let len1 = rng.gen_range_usize(1, 100);
        let len2 = rng.gen_range_usize(1, 100);
        let len3 = rng.gen_range_usize(1, 100);
        let n1 = random_array(&mut rng, len1);
        let n2 = random_array(&mut rng, len2);
        let n3 = random_array(&mut rng, len3);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (r1, r2, r3) = mutate(n1, n2, n3, mk);
        emit(r1, r2, r3, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity mutations
    while count < target {
        let len1 = rng.gen_range_usize(1, 100);
        let len2 = rng.gen_range_usize(1, 100);
        let len3 = rng.gen_range_usize(1, 100);
        let n1 = random_array(&mut rng, len1);
        let n2 = random_array(&mut rng, len2);
        let n3 = random_array(&mut rng, len3);
        let (r1, r2, r3) = mutate(n1, n2, n3, 0);
        emit(r1, r2, r3, &mut seen, &mut out, &mut count);
    }
}
