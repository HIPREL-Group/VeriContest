use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 1000,
        1 <= nums2.len() <= 1000,
        forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 100,
        forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 100,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        (result.0.len() + 1) * (result.1.len() + 1) <= usize::MAX,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 100,
{
    let r = if mutation_kind == 0u8 {
        // identity
        (nums1, nums2)
    } else if mutation_kind == 1u8 {
        // set last element of nums1 to 0
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 0);
        (n1, nums2)
    } else if mutation_kind == 2u8 {
        // set last element of nums1 to 100 (boundary)
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 100);
        (n1, nums2)
    } else if mutation_kind == 3u8 {
        // set last element of nums2 to 0
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 0);
        (nums1, n2)
    } else if mutation_kind == 4u8 {
        // set last element of nums2 to 100 (boundary)
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 100);
        (nums1, n2)
    } else if mutation_kind == 5u8 && nums1.len() > 1 {
        // shrink nums1 by one element
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2)
    } else if mutation_kind == 6u8 && nums2.len() > 1 {
        // shrink nums2 by one element
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2)
    } else if mutation_kind == 7u8 && nums1.len() < 1000 {
        // grow nums1 by one element (push 0)
        let mut n1 = nums1;
        n1.push(0);
        (n1, nums2)
    } else if mutation_kind == 8u8 && nums2.len() < 1000 {
        // grow nums2 by one element (push 0)
        let mut n2 = nums2;
        n2.push(0);
        (nums1, n2)
    } else if mutation_kind == 9u8 {
        // set first element of nums1 = first element of nums2
        let mut n1 = nums1;
        let v = nums2[0];
        n1.set(0, v);
        (n1, nums2)
    } else if mutation_kind == 10u8 {
        // set all elements of nums1 to 0
        let mut n1 = nums1;
        let mut i: usize = 0;
        while i < n1.len()
            invariant
                0 <= i <= n1.len(),
                n1.len() == nums1.len(),
                1 <= n1.len() <= 1000,
                forall |j: int| 0 <= j < i ==> n1[j] == 0,
                forall |j: int| i <= j < n1.len() ==> n1[j] == nums1[j],
            decreases n1.len() - i,
        {
            n1.set(i, 0);
            i += 1;
        }
        (n1, nums2)
    } else if mutation_kind == 11u8 {
        // set all elements of nums2 to 0
        let mut n2 = nums2;
        let mut i: usize = 0;
        while i < n2.len()
            invariant
                0 <= i <= n2.len(),
                n2.len() == nums2.len(),
                1 <= n2.len() <= 1000,
                forall |j: int| 0 <= j < i ==> n2[j] == 0,
                forall |j: int| i <= j < n2.len() ==> n2[j] == nums2[j],
            decreases n2.len() - i,
        {
            n2.set(i, 0);
            i += 1;
        }
        (nums1, n2)
    } else {
        // fallback: identity
        (nums1, nums2)
    };

    proof {
        assert(r.0.len() + 1 <= 1001int);
        assert(r.1.len() + 1 <= 1001int);
        assert((r.0.len() + 1) * (r.1.len() + 1) <= 1001int * 1001int) by (nonlinear_arith)
            requires r.0.len() + 1 <= 1001int, r.1.len() + 1 <= 1001int,
                     r.0.len() + 1 >= 0int, r.1.len() + 1 >= 0int;
    }

    r
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

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 100) as i32);
    }
    arr
}

fn mutate(nums1: Vec<i32>, nums2: Vec<i32>, mk: u8) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(nums1, nums2, mk)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(718);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums1: Vec<i32>, nums2: Vec<i32>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}|{:?}", nums1, nums2);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_length(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1,2,3,2,1], vec![3,2,1,4,7]),
        (vec![0,0,0,0,0], vec![0,0,0,0,0]),
    ];
    for (n1, n2) in &examples {
        emit(n1.clone(), n2.clone(), &mut seen, &mut out, &mut emitted);
    }

    // Seed arrays with diverse characteristics
    let seed_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![0], vec![0]),
        (vec![100], vec![100]),
        (vec![0], vec![100]),
        (vec![1, 2, 3], vec![1, 2, 3]),
        (vec![50, 50, 50], vec![50, 50, 50]),
        (vec![0, 0, 0], vec![100, 100, 100]),
        (vec![1, 2, 3, 4, 5], vec![6, 7, 8, 9, 10]),
        (vec![1, 1, 1, 1], vec![1, 1, 1, 1]),
        (vec![99, 100], vec![99, 100]),
        (vec![0, 1, 0, 1], vec![1, 0, 1, 0]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed pair
    for (n1, n2) in &seed_pairs {
        for &mk in &mutation_kinds {
            let (r1, r2) = mutate(n1.clone(), n2.clone(), mk);
            emit(r1, r2, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse size classes
    while emitted < count {
        let len1: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 500),     // large
            _ => rng.gen_range_usize(501, 1000),    // max
        };
        let len2: usize = match (emitted + 2) % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let n1 = random_array(&mut rng, len1);
        let n2 = random_array(&mut rng, len2);
        let mk = rng.gen_range_usize(0, 11) as u8;
        let (r1, r2) = mutate(n1, n2, mk);
        emit(r1, r2, &mut seen, &mut out, &mut emitted);
    }
}
