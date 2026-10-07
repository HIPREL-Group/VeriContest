use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elements: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= elements.len() <= 100_000,
        forall|i: int| 0 <= i < elements.len() ==> -10_000 <= #[trigger] elements@[i] <= 10_000,
        1 <= k <= elements.len(),
    ensures
        result.0.len() <= 100_000,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> -10_000 <= #[trigger] result.0@[i] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        (elements, k)
    } else if mutation_kind == 1 {
        // set all elements to 0
        let n = elements.len();
        let mut nums = elements;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == n,
                1 <= n <= 100_000,
                forall|j: int| 0 <= j < i as int ==> nums@[j] == 0i32,
                forall|j: int| i as int <= j < nums.len() as int
                    ==> -10_000 <= #[trigger] nums@[j] <= 10_000,
            decreases nums.len() - i,
        {
            nums.set(i, 0);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 2 {
        // set all elements to -10_000 (lower boundary)
        let n = elements.len();
        let mut nums = elements;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == n,
                1 <= n <= 100_000,
                forall|j: int| 0 <= j < i as int ==> nums@[j] == -10_000i32,
                forall|j: int| i as int <= j < nums.len() as int
                    ==> -10_000 <= #[trigger] nums@[j] <= 10_000,
            decreases nums.len() - i,
        {
            nums.set(i, -10_000);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 3 {
        // set all elements to 10_000 (upper boundary)
        let n = elements.len();
        let mut nums = elements;
        let mut i: usize = 0;
        while i < nums.len()
            invariant
                0 <= i <= nums.len(),
                nums.len() == n,
                1 <= n <= 100_000,
                forall|j: int| 0 <= j < i as int ==> nums@[j] == 10_000i32,
                forall|j: int| i as int <= j < nums.len() as int
                    ==> -10_000 <= #[trigger] nums@[j] <= 10_000,
            decreases nums.len() - i,
        {
            nums.set(i, 10_000);
            i += 1;
        }
        (nums, k)
    } else if mutation_kind == 4 {
        // k = 1 (minimal window)
        (elements, 1)
    } else if mutation_kind == 5 {
        // k = len (full array window)
        let full_k = elements.len() as i32;
        (elements, full_k)
    } else if mutation_kind == 6 {
        // nudge first element up
        let mut nums = elements;
        if nums[0] < 10_000 {
            nums.set(0, nums[0] + 1);
        }
        (nums, k)
    } else if mutation_kind == 7 {
        // nudge last element down
        let mut nums = elements;
        let last = nums.len() - 1;
        if nums[last] > -10_000 {
            nums.set(last, nums[last] - 1);
        }
        (nums, k)
    } else if mutation_kind == 8 {
        // swap first and last elements
        let mut nums = elements;
        let last = nums.len() - 1;
        let first_val = nums[0];
        let last_val = nums[last];
        nums.set(0, last_val);
        nums.set(last, first_val);
        (nums, k)
    } else {
        // fallback: identity
        (elements, k)
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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_elements(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut elems = Vec::with_capacity(len);
    for _ in 0..len {
        elems.push(rng.gen_range_i64(-10_000, 10_000) as i32);
    }
    elems
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(643);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!())
        .parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($nums:expr, $k:expr) => {
            if count < goal {
                let nums_val: Vec<i32> = $nums;
                let k_val: i32 = $k;
                let output = Solution::find_max_average(nums_val.clone(), k_val);
                let line = json!({
                    "input": {"nums": nums_val, "k": k_val},
                    "output": output
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    emit!(vec![1, 12, -5, -6, 50, 3], 4);
    emit!(vec![5], 1);

    // ---- Boundary seeds with all mutations ----
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![0], 1),
        (vec![10_000], 1),
        (vec![-10_000], 1),
        (vec![0, 0, 0], 2),
        (vec![10_000, -10_000, 10_000, -10_000], 2),
        (vec![1, 2, 3, 4, 5], 3),
        (vec![-1, -2, -3, -4, -5], 3),
        (vec![10_000; 10], 5),
        (vec![-10_000; 10], 5),
        (vec![0; 20], 10),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    for (elems, k_val) in &seeds {
        for &mk in &mutation_kinds {
            let (nums, k_out) = generate_test_case(elems.clone(), *k_val, mk);
            emit!(nums, k_out);
        }
    }

    // ---- Random test cases with diverse sizes ----
    while count < goal {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // very large
        };

        let elements = random_elements(&mut rng, n);
        let k = rng.gen_range_i64(1, n as i64) as i32;
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];

        let (nums, k_out) = generate_test_case(elements, k, mk);
        emit!(nums, k_out);
    }
}
