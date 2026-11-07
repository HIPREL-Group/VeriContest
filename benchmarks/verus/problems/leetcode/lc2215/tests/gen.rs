use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw1: Vec<i32>,
    raw2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= raw1.len() <= 1000,
        1 <= raw2.len() <= 1000,
        forall|i: int| 0 <= i < raw1.len() ==> -1000 <= #[trigger] raw1[i] <= 1000,
        forall|j: int| 0 <= j < raw2.len() ==> -1000 <= #[trigger] raw2[j] <= 1000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
        forall|j: int| 0 <= j < result.1.len() ==> -1000 <= #[trigger] result.1[j] <= 1000,
{
    if mutation_kind == 0 {
        // Identity
        (raw1, raw2)
    } else if mutation_kind == 1 && raw1.len() < 1000 {
        // Grow nums1
        let mut nums1 = raw1;
        nums1.push(0i32);
        (nums1, raw2)
    } else if mutation_kind == 2 && raw2.len() < 1000 {
        // Grow nums2
        let mut nums2 = raw2;
        nums2.push(0i32);
        (raw1, nums2)
    } else if mutation_kind == 3 && raw1.len() > 1 {
        // Shrink nums1
        let mut nums1 = raw1;
        nums1.pop();
        (nums1, raw2)
    } else if mutation_kind == 4 && raw2.len() > 1 {
        // Shrink nums2
        let mut nums2 = raw2;
        nums2.pop();
        (raw1, nums2)
    } else if mutation_kind == 5 {
        // Set first element of nums1 to 0
        let mut nums1 = raw1;
        nums1.set(0, 0i32);
        (nums1, raw2)
    } else if mutation_kind == 6 {
        // Set first element of nums2 to 0
        let mut nums2 = raw2;
        nums2.set(0, 0i32);
        (raw1, nums2)
    } else if mutation_kind == 7 {
        // Set first element of nums1 to -1000
        let mut nums1 = raw1;
        nums1.set(0, -1000i32);
        (nums1, raw2)
    } else if mutation_kind == 8 {
        // Set first element of nums1 to 1000
        let mut nums1 = raw1;
        nums1.set(0, 1000i32);
        (nums1, raw2)
    } else if mutation_kind == 9 {
        // Copy nums1 into nums2 (all shared)
        let mut nums2 = Vec::new();
        let mut k: usize = 0;
        while k < raw1.len()
            invariant
                0 <= k <= raw1.len(),
                nums2.len() == k,
                forall|j: int| 0 <= j < k as int ==> #[trigger] nums2[j] == raw1[j],
                forall|j: int| 0 <= j < k as int ==> -1000 <= #[trigger] nums2[j] <= 1000,
                1 <= raw1.len() <= 1000,
                forall|i: int| 0 <= i < raw1.len() ==> -1000 <= #[trigger] raw1[i] <= 1000,
            decreases raw1.len() - k,
        {
            nums2.push(raw1[k]);
            k += 1;
        }
        (raw1, nums2)
    } else {
        // Fallback: identity
        (raw1, raw2)
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
    let mut v = Vec::new();
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    v
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let mut case_idx: usize = 0;

    // Example 1
    {
        let nums1 = vec![1, 2, 3];
        let nums2 = vec![2, 4, 6];
        let result = Solution::find_difference(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": result
        })).unwrap();
        case_idx += 1;
    }

    // Example 2
    {
        let nums1 = vec![1, 2, 3, 3];
        let nums2 = vec![1, 1, 2, 2];
        let result = Solution::find_difference(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": result
        })).unwrap();
        case_idx += 1;
    }

    while case_idx < count {
        let n1: usize = match case_idx % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let n2: usize = match (case_idx + 2) % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };

        let raw1 = random_array(&mut rng, n1);
        let raw2 = random_array(&mut rng, n2);

        let mutation_kind = (case_idx % 10) as u8;
        let (nums1, nums2) = generate_test_case(raw1, raw2, mutation_kind);

        let result = Solution::find_difference(nums1.clone(), nums2.clone());

        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": result
        })).unwrap();

        case_idx += 1;
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
