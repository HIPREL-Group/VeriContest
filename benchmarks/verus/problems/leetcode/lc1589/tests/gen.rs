use vstd::prelude::*;

verus! {

/// Constructs valid `(nums, requests)` inputs for max_sum_range_query from
/// parallel construction arrays, applying mutation_kind for diversity.
pub fn generate_test_case(
    raw_nums: &Vec<i32>,
    starts: &Vec<i32>,
    ends: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= raw_nums.len() <= 100_000,
        forall |i: int| 0 <= i < raw_nums.len() ==> 0 <= #[trigger] raw_nums[i] <= 100_000,
        1 <= starts.len() <= 100_000,
        starts.len() == ends.len(),
        forall |i: int| 0 <= i < starts.len() ==>
            0 <= #[trigger] starts[i] <= ends[i] && (ends[i] as int) < raw_nums.len() as int,
    ensures
        1 <= result.0@.len() <= 100_000,
        forall |i: int| 0 <= i < result.0@.len() ==>
            0 <= #[trigger] result.0@[i] <= 100_000,
        1 <= result.1@.len() <= 100_000,
        forall |i: int| 0 <= i < result.1@.len() ==> (
            (#[trigger] result.1@[i])@.len() == 2
                && 0 <= result.1@[i]@[0]
                && result.1@[i]@[0] <= result.1@[i]@[1]
                && (result.1@[i]@[1] as int) < result.0@.len() as int
        ),
{
    // Build nums with mutations
    let mut nums: Vec<i32> = Vec::new();
    let mut ni: usize = 0;
    while ni < raw_nums.len()
        invariant
            0 <= ni <= raw_nums.len(),
            nums.len() == ni,
            1 <= raw_nums.len() <= 100_000,
            forall |i: int| 0 <= i < raw_nums.len() ==> 0 <= #[trigger] raw_nums[i] <= 100_000,
            forall |j: int| 0 <= j < ni ==> 0 <= #[trigger] nums[j] <= 100_000,
        decreases raw_nums.len() - ni,
    {
        // Mutation 0: normal
        // Mutation 1: all zeros
        // Mutation 2: all max (100_000)
        // Mutation 3: set to 1
        // Mutation 4: halve values
        let val: i32 = if mutation_kind == 1 {
            0i32
        } else if mutation_kind == 2 {
            100_000i32
        } else if mutation_kind == 3 {
            1i32
        } else if mutation_kind == 4 {
            raw_nums[ni] / 2
        } else {
            raw_nums[ni]
        };
        assert(0 <= val <= 100_000);
        nums.push(val);
        ni = ni + 1;
    }

    // Build requests with mutations
    let n = raw_nums.len();
    let mut requests: Vec<Vec<i32>> = Vec::new();
    let mut ri: usize = 0;
    while ri < starts.len()
        invariant
            0 <= ri <= starts.len(),
            1 <= starts.len() <= 100_000,
            starts.len() == ends.len(),
            n == raw_nums.len(),
            1 <= n <= 100_000,
            nums.len() == n,
            requests.len() == ri,
            forall |i: int| 0 <= i < starts.len() ==>
                0 <= #[trigger] starts[i] <= ends[i] && (ends[i] as int) < n as int,
            forall |j: int| 0 <= j < ri ==> (
                (#[trigger] requests[j])@.len() == 2
                    && 0 <= requests[j]@[0]
                    && requests[j]@[0] <= requests[j]@[1]
                    && (requests[j]@[1] as int) < n as int
            ),
        decreases starts.len() - ri,
    {
        // Mutation 5: single-element range (end = start)
        // Mutation 6: full range (start = 0, end = n-1)
        // Mutation 7: start at 0
        let s_orig = starts[ri];
        let e_orig = ends[ri];

        let start_val: i32;
        let end_val: i32;
        if mutation_kind == 5 {
            start_val = s_orig;
            end_val = s_orig;
            assert(0 <= start_val <= end_val);
            assert((end_val as int) < n as int);
        } else if mutation_kind == 6 {
            start_val = 0i32;
            end_val = (n - 1) as i32;
            assert(0 <= start_val <= end_val);
            assert((end_val as int) < n as int);
        } else if mutation_kind == 7 {
            start_val = 0i32;
            end_val = e_orig;
            assert(0 <= start_val <= end_val);
            assert((end_val as int) < n as int);
        } else {
            start_val = s_orig;
            end_val = e_orig;
            assert(0 <= start_val <= end_val);
            assert((end_val as int) < n as int);
        }

        let mut req: Vec<i32> = Vec::new();
        req.push(start_val);
        req.push(end_val);

        assert(req@.len() == 2);
        assert(req@[0] == start_val);
        assert(req@[1] == end_val);

        requests.push(req);
        ri = ri + 1;
    }

    (nums, requests)
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

fn random_inputs(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>, Vec<i32>) {
    let mut nums = Vec::with_capacity(n);
    for _ in 0..n {
        nums.push(rng.gen_range_i64(0, 100_000) as i32);
    }
    let m = match rng.gen_range_usize(0, 4) {
        0 => rng.gen_range_usize(1, 3),
        1 => rng.gen_range_usize(1, 10),
        2 => rng.gen_range_usize(11, 100),
        3 => rng.gen_range_usize(101, 500),
        _ => rng.gen_range_usize(501, 2000),
    };
    let mut starts = Vec::with_capacity(m);
    let mut ends = Vec::with_capacity(m);
    for _ in 0..m {
        let s = rng.gen_range_i64(0, (n - 1) as i64) as i32;
        let e = rng.gen_range_i64(s as i64, (n - 1) as i64) as i32;
        starts.push(s);
        ends.push(e);
    }
    (nums, starts, ends)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1589);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums_vec: Vec<i32>, requests_vec: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{:?},{:?}", nums_vec, requests_vec);
        if !seen.insert(key) { return; }
        let result = Solution::max_sum_range_query(nums_vec.clone(), requests_vec.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums_vec, "requests": requests_vec},
            "output": result
        })).unwrap();
        *count += 1;
    };

    // Example 1: nums = [1,2,3,4,5], requests = [[1,3],[0,1]]
    {
        let raw_nums = vec![1, 2, 3, 4, 5];
        let starts = vec![1, 0];
        let ends = vec![3, 1];
        for mk in 0u8..=7 {
            let (n, r) = generate_test_case(&raw_nums, &starts, &ends, mk);
            emit(n, r, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: nums = [1,2,3,4,5,6], requests = [[0,1]]
    {
        let raw_nums = vec![1, 2, 3, 4, 5, 6];
        let starts = vec![0];
        let ends = vec![1];
        for mk in 0u8..=7 {
            let (n, r) = generate_test_case(&raw_nums, &starts, &ends, mk);
            emit(n, r, &mut seen, &mut out, &mut count);
        }
    }

    // Example 3: nums = [1,2,3,4,5,10], requests = [[0,2],[1,3],[1,1]]
    {
        let raw_nums = vec![1, 2, 3, 4, 5, 10];
        let starts = vec![0, 1, 1];
        let ends = vec![2, 3, 1];
        for mk in 0u8..=7 {
            let (n, r) = generate_test_case(&raw_nums, &starts, &ends, mk);
            emit(n, r, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single element, single request
    {
        let raw_nums = vec![0];
        let starts = vec![0];
        let ends = vec![0];
        for mk in 0u8..=7 {
            let (n, r) = generate_test_case(&raw_nums, &starts, &ends, mk);
            emit(n, r, &mut seen, &mut out, &mut count);
        }
    }

    // Edge case: single element max value
    {
        let raw_nums = vec![100_000];
        let starts = vec![0];
        let ends = vec![0];
        for mk in 0u8..=7 {
            let (n, r) = generate_test_case(&raw_nums, &starts, &ends, mk);
            emit(n, r, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 20),         // small
            2 => rng.gen_range_usize(21, 200),       // medium
            3 => rng.gen_range_usize(201, 1000),     // large
            _ => rng.gen_range_usize(1001, 5000),    // big
        };

        let (raw_nums, starts, ends) = random_inputs(&mut rng, n);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (nums_out, reqs_out) = generate_test_case(&raw_nums, &starts, &ends, mk);
        emit(nums_out, reqs_out, &mut seen, &mut out, &mut count);
    }
}
