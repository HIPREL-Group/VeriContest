use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 100 { 100usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 100 { 100 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1.len() <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100,
{
    (bounded_values(&nums1), bounded_values(&nums2))
}


pub fn generate_candidate(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        nums1.len() <= 2147483647usize,
        nums2.len() <= 2147483647usize,
    ensures
        result.0.len() <= 2147483647usize,
        result.1.len() <= 2147483647usize,
{
    if mutation_kind == 0 {
        // identity
        (nums1, nums2)
    } else if mutation_kind == 1 {
        // swap the two arrays
        (nums2, nums1)
    } else if mutation_kind == 2 && nums1.len() < 2147483647 {
        // push element to nums1
        let mut n1 = nums1;
        n1.push(1);
        (n1, nums2)
    } else if mutation_kind == 3 && nums2.len() < 2147483647 {
        // push element to nums2
        let mut n2 = nums2;
        n2.push(1);
        (nums1, n2)
    } else if mutation_kind == 4 && nums1.len() > 0 {
        // pop from nums1
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2)
    } else if mutation_kind == 5 && nums2.len() > 0 {
        // pop from nums2
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2)
    } else if mutation_kind == 6 && nums1.len() > 0 {
        // set first element of nums1 to 0
        let mut n1 = nums1;
        n1.set(0, 0);
        (n1, nums2)
    } else if mutation_kind == 7 && nums2.len() > 0 {
        // set first element of nums2 to 0
        let mut n2 = nums2;
        n2.set(0, 0);
        (nums1, n2)
    } else if mutation_kind == 8 && nums1.len() > 0 && nums2.len() < 2147483647 {
        // copy first element of nums1 into nums2 (increase overlap)
        let val = nums1[0];
        let mut n2 = nums2;
        n2.push(val);
        (nums1, n2)
    } else if mutation_kind == 9 && nums1.len() > 0 {
        // nudge first element of nums1 up
        let mut n1 = nums1;
        if n1[0] < i32::MAX {
            n1.set(0, n1[0] + 1);
        }
        (n1, nums2)
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

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo, hi) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2956);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums1: Vec<i32>, nums2: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        let (nums1, nums2) = generate_test_case(nums1, nums2);
        if *emitted >= count { return; }
        let key = format!("{:?}|{:?}", nums1, nums2);
        if !seen.insert(key) { return; }
        let output = Solution::find_intersection_values(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![2, 3, 2], vec![1, 2]),
        (vec![4, 3, 2, 3, 1], vec![2, 2, 5, 2, 3, 6]),
        (vec![3, 4, 2, 3], vec![1, 5]),
    ];
    for (n1, n2) in examples {
        emit(n1, n2, &mut seen, &mut out, &mut emitted);
    }

    // Seed arrays with mutations
    let seed_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![1], vec![2]),
        (vec![100], vec![100]),
        (vec![1, 2, 3], vec![3, 2, 1]),
        (vec![1, 1, 1], vec![1, 1, 1]),
        (vec![1, 2, 3, 4, 5], vec![6, 7, 8, 9, 10]),
    ];
    for (n1, n2) in &seed_pairs {
        for mk in 0..10u8 {
            let (r1, r2) = generate_candidate(n1.clone(), n2.clone(), mk);
            emit(r1, r2, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes and mutations
    while emitted < count {
        let size_class = emitted % 5;
        let n1_len = match size_class {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let n2_len = match size_class {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        // Mix value ranges: sometimes small (1-10), sometimes full (1-100), sometimes with overlap
        let (lo, hi) = if emitted % 4 == 0 { (1, 5) } else if emitted % 4 == 1 { (1, 10) } else { (1, 100) };
        let nums1 = random_array(&mut rng, n1_len, lo, hi);
        let nums2 = random_array(&mut rng, n2_len, lo, hi);

        let mk = rng.gen_range_usize(0, 9) as u8;
        let (r1, r2) = generate_candidate(nums1, nums2, mk);
        emit(r1, r2, &mut seen, &mut out, &mut emitted);
    }
}
