use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums_vals: &Vec<i32>,
    q_indices: &Vec<i32>,
    q_ks: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= q_indices.len() <= nums_vals.len() <= 50,
        q_indices.len() == q_ks.len(),
        forall|i: int| 0 <= i < nums_vals.len() ==> 1 <= #[trigger] nums_vals[i] <= 100_000,
        forall|i: int| 0 <= i < q_indices.len() ==> 0 <= #[trigger] q_indices[i] < nums_vals.len(),
        forall|i: int| 0 <= i < q_ks.len() ==> 0 <= #[trigger] q_ks[i] <= nums_vals.len() - 1,
    ensures
        1 <= result.1.len() <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i].len() == 2,
        forall |i: int| 0 <= i < result.1.len() && result.1[i].len() == 2 ==> 0 <= #[trigger] result.1[i][0] < result.0.len(),
        forall |i: int| 0 <= i < result.1.len() && result.1[i].len() == 2 ==> 0 <= #[trigger] result.1[i][1] <= result.0.len() - 1,
{
    let n = nums_vals.len();
    let m = q_indices.len();

    // Build nums from construction params with optional mutations
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            0 <= k <= n,
            n == nums_vals.len(),
            n <= 50,
            nums.len() == k,
            forall|j: int| 0 <= j < nums_vals.len() ==> 1 <= #[trigger] nums_vals[j] <= 100_000,
            forall|j: int| 0 <= j < k as int ==> 1 <= #[trigger] nums[j] <= 100_000,
        decreases n - k,
    {
        if mutation_kind == 1 {
            nums.push(1i32);
        } else if mutation_kind == 2 && nums_vals[k] <= 99_999 {
            nums.push(nums_vals[k] + 1);
        } else {
            nums.push(nums_vals[k]);
        }
        k += 1;
    }

    // Build queries from q_indices and q_ks
    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < m
        invariant
            0 <= i <= m,
            m == q_indices.len(),
            m == q_ks.len(),
            m <= n,
            n == nums.len(),
            n <= 50,
            queries.len() == i as int,
            forall|j: int| 0 <= j < q_indices.len() ==> 0 <= #[trigger] q_indices[j] < n as int,
            forall|j: int| 0 <= j < q_ks.len() ==> 0 <= #[trigger] q_ks[j] <= n as int - 1,
            forall|j: int| 0 <= j < i as int ==> #[trigger] queries[j].len() == 2,
            forall|j: int| 0 <= j < i as int && queries[j].len() == 2
                ==> 0 <= #[trigger] queries[j][0] < nums.len(),
            forall|j: int| 0 <= j < i as int && queries[j].len() == 2
                ==> 0 <= #[trigger] queries[j][1] <= nums.len() as int - 1,
        decreases m - i,
    {
        let idx: i32 = if mutation_kind == 3 {
            0i32
        } else {
            q_indices[i]
        };
        let kv: i32 = if mutation_kind == 4 {
            0i32
        } else {
            q_ks[i]
        };

        let mut q: Vec<i32> = Vec::new();
        q.push(idx);
        q.push(kv);
        assert(q.len() == 2);
        queries.push(q);
        i += 1;
    }

    (nums, queries)
}

} // verus!

// ---------------------------------------------------------------------------
// Unverified runtime: PRNG, sampling, JSONL output
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    (0..len).map(|_| rng.gen_range_i64(1, 100_000) as i32).collect()
}

fn random_query_params(rng: &mut Rng, n: usize, m: usize) -> (Vec<i32>, Vec<i32>) {
    let indices: Vec<i32> = (0..m).map(|_| rng.gen_range_usize(0, n - 1) as i32).collect();
    let ks: Vec<i32> = (0..m).map(|_| rng.gen_range_usize(0, n - 1) as i32).collect();
    (indices, ks)
}

fn main() {
    use std::io::Write;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3080);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, queries: Vec<Vec<i32>>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let result = Solution::unmarked_sum_array(nums.clone(), queries.clone());
        let q_json: Vec<serde_json::Value> = queries.iter().map(|q| json!([q[0], q[1]])).collect();
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "queries": q_json},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Example 1: nums = [1,2,2,1,2,3,1], queries = [[1,2],[3,3],[4,2]]
    {
        let nums = vec![1,2,2,1,2,3,1];
        let q_idx = vec![1,3,4];
        let q_ks = vec![2,3,2];
        let (out_nums, out_queries) = generate_test_case(&nums, &q_idx, &q_ks, 0);
        emit(out_nums, out_queries, &mut out, &mut emitted);
    }

    // Example 2: nums = [1,4,2,3], queries = [[0,1]]
    {
        let nums = vec![1,4,2,3];
        let q_idx = vec![0];
        let q_ks = vec![1];
        let (out_nums, out_queries) = generate_test_case(&nums, &q_idx, &q_ks, 0);
        emit(out_nums, out_queries, &mut out, &mut emitted);
    }

    // Apply mutations to example 1
    for mk in 1u8..=4 {
        let nums = vec![1,2,2,1,2,3,1];
        let q_idx = vec![1,3,4];
        let q_ks = vec![2,3,2];
        let (out_nums, out_queries) = generate_test_case(&nums, &q_idx, &q_ks, mk);
        emit(out_nums, out_queries, &mut out, &mut emitted);
    }

    // Random test cases with diverse size classes (max 50 for nums, 20 for queries)
    let mut _attempts = 0usize;
    while emitted < count {
        _attempts += 1;
        if _attempts > 10000 { break; }
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 20),
            3 => rng.gen_range_usize(21, 35),
            _ => rng.gen_range_usize(36, 50),
        };
        let m: usize = rng.gen_range_usize(1, n.min(20));

        let nums = random_nums(&mut rng, n);
        let (q_idx, q_ks) = random_query_params(&mut rng, n, m);

        let mk: u8 = if emitted % 5 == 0 {
            rng.gen_range_usize(1, 4) as u8
        } else {
            0
        };

        let (out_nums, out_queries) = generate_test_case(&nums, &q_idx, &q_ks, mk);
        emit(out_nums, out_queries, &mut out, &mut emitted);
    }
}
