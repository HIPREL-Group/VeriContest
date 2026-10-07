use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    mutation_kind: u8,
) -> (res: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 1000,
        1 <= nums2.len() <= 1000,
        forall|i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
        forall|i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
    ensures
        1 <= res.0.len() <= 1000,
        1 <= res.1.len() <= 1000,
        forall|i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 1000,
        forall|i: int| 0 <= i < res.1.len() ==> 0 <= #[trigger] res.1[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (nums1, nums2)
    } else if mutation_kind == 1 {
        // copy nums1[0] into nums2[0] to force intersection
        let mut n2 = nums2;
        let v = nums1[0];
        n2.set(0, v);
        (nums1, n2)
    } else if mutation_kind == 2 {
        // copy nums2[0] into nums1[0] to force intersection
        let mut n1 = nums1;
        let v = nums2[0];
        n1.set(0, v);
        (n1, nums2)
    } else if mutation_kind == 3 {
        // set nums1[last] to 0 (boundary)
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 0);
        (n1, nums2)
    } else if mutation_kind == 4 {
        // set nums1[last] to 1000 (boundary)
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 1000);
        (n1, nums2)
    } else if mutation_kind == 5 {
        // set nums2[last] to 0 (boundary)
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 0);
        (nums1, n2)
    } else if mutation_kind == 6 {
        // set nums2[last] to 1000 (boundary)
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 1000);
        (nums1, n2)
    } else if mutation_kind == 7 && nums1.len() >= 2 {
        // add duplicate in nums1: copy first element to last position
        let mut n1 = nums1;
        let v = n1[0];
        let last = n1.len() - 1;
        n1.set(last, v);
        (n1, nums2)
    } else if mutation_kind == 8 {
        // nudge nums1[last] up by 1 if < 1000
        let mut n1 = nums1;
        let last = n1.len() - 1;
        if n1[last] < 1000 {
            n1.set(last, n1[last] + 1);
        }
        (n1, nums2)
    } else if mutation_kind == 9 {
        // nudge nums2[last] down by 1 if > 0
        let mut n2 = nums2;
        let last = n2.len() - 1;
        if n2[last] > 0 {
            n2.set(last, n2[last] - 1);
        }
        (nums1, n2)
    } else if mutation_kind == 10 {
        // set all of nums1 to same value as nums1[0]
        let v = nums1[0];
        let ghost orig_len = nums1.len();
        let mut n1 = nums1;
        let mut i: usize = 0;
        while i < n1.len()
            invariant
                0 <= i <= n1.len(),
                n1.len() == orig_len,
                1 <= n1.len() <= 1000,
                0 <= v <= 1000,
                forall|j: int| 0 <= j < i ==> n1[j] == v,
                forall|j: int| i <= j < n1.len() ==> 0 <= #[trigger] n1[j] <= 1000,
            decreases n1.len() - i,
        {
            n1.set(i, v);
            i += 1;
        }
        (n1, nums2)
    } else if mutation_kind == 11 {
        // set all of nums2 to same value as nums2[0]
        let v = nums2[0];
        let ghost orig_len = nums2.len();
        let mut n2 = nums2;
        let mut i: usize = 0;
        while i < n2.len()
            invariant
                0 <= i <= n2.len(),
                n2.len() == orig_len,
                1 <= n2.len() <= 1000,
                0 <= v <= 1000,
                forall|j: int| 0 <= j < i ==> n2[j] == v,
                forall|j: int| i <= j < n2.len() ==> 0 <= #[trigger] n2[j] <= 1000,
            decreases n2.len() - i,
        {
            n2.set(i, v);
            i += 1;
        }
        (nums1, n2)
    } else if mutation_kind == 12 && nums1.len() < 1000 {
        // grow nums1 by pushing 0
        let mut n1 = nums1;
        n1.push(0);
        (n1, nums2)
    } else if mutation_kind == 13 && nums2.len() < 1000 {
        // grow nums2 by pushing 0
        let mut n2 = nums2;
        n2.push(0);
        (nums1, n2)
    } else if mutation_kind == 14 && nums1.len() > 1 {
        // shrink nums1 by popping
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2)
    } else if mutation_kind == 15 && nums2.len() > 1 {
        // shrink nums2 by popping
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2)
    } else {
        // fallback: identity
        (nums1, nums2)
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
}

struct Solution;
include!("../code.rs");

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 1000) as i32);
    }
    arr
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

    let mut emit = |n1: Vec<i32>, n2: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}|{:?}", n1, n2);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::intersection(n1.clone(), n2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": n1, "nums2": n2},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 2, 2, 1], vec![2, 2]),
        (vec![4, 9, 5], vec![9, 4, 9, 8, 4]),
    ];
    for (n1, n2) in &examples {
        emit(n1.clone(), n2.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed arrays with interesting patterns
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1000],
        vec![0, 1000],
        vec![500],
        vec![1, 2, 3],
        vec![0, 0, 0],
        vec![1000, 1000, 1000],
        vec![1, 1, 2, 2, 3, 3],
        vec![0, 500, 1000],
    ];

    let num_mutations: u8 = 16;

    // Apply every mutation to seed pairs
    for s1 in &seed_arrays {
        for s2 in &seed_arrays {
            for mk in 0..num_mutations {
                if count >= count_target { break; }
                let (r1, r2) = generate_test_case(s1.clone(), s2.clone(), mk);
                emit(r1, r2, &mut seen, &mut out, &mut count);
            }
            if count >= count_target { break; }
        }
        if count >= count_target { break; }
    }

    // Random arrays with varied sizes and random mutations
    while count < count_target {
        let len1 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 1000),  // max
        };
        let len2 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let n1 = random_array(&mut rng, len1);
        let n2 = random_array(&mut rng, len2);
        let mk = rng.gen_range_usize(0, (num_mutations - 1) as usize) as u8;
        let (r1, r2) = generate_test_case(n1, n2, mk);
        emit(r1, r2, &mut seen, &mut out, &mut count);
    }
}
