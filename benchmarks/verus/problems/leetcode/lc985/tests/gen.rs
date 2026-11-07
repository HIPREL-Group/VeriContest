use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    queries: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= nums.len() <= 10_000,
        forall |i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000,
        1 <= queries.len() <= 10_000,
        forall |i: int| 0 <= i < queries.len() ==>
            queries[i].len() == 2
            && -10_000 <= queries[i][0] <= 10_000
            && 0 <= queries[i][1] < nums.len(),
    ensures
        1 <= result.0.len() <= 10_000,
        forall |i: int| 0 <= i < result.0.len() ==> -10_000 <= #[trigger] result.0[i] <= 10_000,
        1 <= result.1.len() <= 10_000,
        forall |i: int| 0 <= i < result.1.len() ==>
            result.1[i].len() == 2
            && -10_000 <= result.1[i][0] <= 10_000
            && 0 <= result.1[i][1] < result.0.len(),
{
    if mutation_kind == 0 {
        // identity
        (nums, queries)
    } else if mutation_kind == 1 && nums[0] < 10_000 {
        // nudge first num up
        let mut n = nums;
        n.set(0, n[0] + 1);
        (n, queries)
    } else if mutation_kind == 2 && nums[0] > -10_000 {
        // nudge first num down
        let mut n = nums;
        n.set(0, n[0] - 1);
        (n, queries)
    } else if mutation_kind == 3 {
        // set all nums to 0 (all even)
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                n.len() == nums.len(),
                1 <= n.len() <= 10_000,
                0 <= i <= n.len(),
                forall |j: int| 0 <= j < i ==> #[trigger] n[j] == 0i32,
                forall |j: int| i <= j < n.len() as int ==> #[trigger] n[j] == nums[j],
                1 <= queries.len() <= 10_000,
                forall |k: int| 0 <= k < queries.len() ==>
                    queries[k].len() == 2
                    && -10_000 <= queries[k][0] <= 10_000
                    && 0 <= queries[k][1] < nums.len(),
            decreases n.len() - i,
        {
            n.set(i, 0);
            i += 1;
        }
        (n, queries)
    } else if mutation_kind == 4 {
        // set all nums to 1 (all odd, even sum always 0)
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                n.len() == nums.len(),
                1 <= n.len() <= 10_000,
                0 <= i <= n.len(),
                forall |j: int| 0 <= j < i ==> #[trigger] n[j] == 1i32,
                forall |j: int| i <= j < n.len() as int ==> #[trigger] n[j] == nums[j],
                1 <= queries.len() <= 10_000,
                forall |k: int| 0 <= k < queries.len() ==>
                    queries[k].len() == 2
                    && -10_000 <= queries[k][0] <= 10_000
                    && 0 <= queries[k][1] < nums.len(),
            decreases n.len() - i,
        {
            n.set(i, 1);
            i += 1;
        }
        (n, queries)
    } else if mutation_kind == 5 {
        // set first num to max boundary
        let mut n = nums;
        n.set(0, 10_000);
        (n, queries)
    } else if mutation_kind == 6 {
        // set first num to min boundary
        let mut n = nums;
        n.set(0, -10_000);
        (n, queries)
    } else if mutation_kind == 7 && nums[0] > i32::MIN {
        // negate first num
        let neg = -nums[0];
        if neg >= -10_000 && neg <= 10_000 {
            let mut n = nums;
            n.set(0, neg);
            (n, queries)
        } else {
            (nums, queries)
        }
    } else {
        // fallback: identity
        (nums, queries)
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

fn mutate(nums: Vec<i32>, queries: Vec<Vec<i32>>, mutation_kind: u8) -> (Vec<i32>, Vec<Vec<i32>>) {
    generate_test_case(nums, queries, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-10_000, 10_000) as i32);
    }
    nums
}

fn random_queries(rng: &mut Rng, count: usize, nums_len: usize) -> Vec<Vec<i32>> {
    let mut queries = Vec::with_capacity(count);
    for _ in 0..count {
        let val = rng.gen_range_i64(-10_000, 10_000) as i32;
        let idx = rng.gen_range_usize(0, nums_len - 1) as i32;
        queries.push(vec![val, idx]);
    }
    queries
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(985);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, queries: Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        let key = format!("{:?}{:?}", nums, queries);
        if *total >= count || !seen.insert(key) {
            return;
        }
        let output = Solution::sum_even_after_queries(nums.clone(), queries.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "queries": queries},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let example_nums_1 = vec![1, 2, 3, 4];
    let example_queries_1 = vec![vec![1, 0], vec![-3, 1], vec![-4, 0], vec![2, 3]];
    emit(example_nums_1, example_queries_1, &mut seen, &mut out, &mut total);

    let example_nums_2 = vec![1];
    let example_queries_2 = vec![vec![4, 0]];
    emit(example_nums_2, example_queries_2, &mut seen, &mut out, &mut total);

    // Seed inputs for mutation
    let seed_inputs: Vec<(Vec<i32>, Vec<Vec<i32>>)> = vec![
        (vec![0, 0, 0, 0], vec![vec![1, 0], vec![2, 1], vec![-1, 2]]),
        (vec![2, 4, 6, 8], vec![vec![1, 0], vec![-2, 3]]),
        (vec![1, 3, 5, 7], vec![vec![1, 0], vec![2, 2]]),
        (vec![-10_000, 10_000], vec![vec![10_000, 0], vec![-10_000, 1]]),
        (vec![0], vec![vec![0, 0]]),
        (vec![2], vec![vec![-2, 0], vec![4, 0]]),
        (vec![1, 2], vec![vec![1, 0], vec![-1, 1], vec![2, 0]]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for (nums, queries) in &seed_inputs {
        for &mk in &mutation_kinds {
            let (n, q) = mutate(nums.clone(), queries.clone(), mk);
            emit(n, q, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs with random mutations across size classes
    while total < count {
        let n_len = match total % 5 {
            0 => rng.gen_range_usize(1, 5),      // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 10_000), // max
        };
        let q_len = match total % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10_000),
        };

        let nums = random_nums(&mut rng, n_len);
        let queries = random_queries(&mut rng, q_len, n_len);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let (n, q) = mutate(nums, queries, mk);
        emit(n, q, &mut seen, &mut out, &mut total);
    }
}
