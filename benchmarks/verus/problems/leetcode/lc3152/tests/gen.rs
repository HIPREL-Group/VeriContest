use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    queries: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (ret: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100_000,
        1 <= queries.len() <= 100_000,
        forall|i: int| 0 <= i < queries.len() ==>
            queries[i].len() == 2
            && 0 <= queries[i][0] <= queries[i][1] < nums.len(),
    ensures
        1 <= ret.0.len() <= 100_000,
        forall|i: int| 0 <= i < ret.0.len() ==> 1 <= #[trigger] ret.0[i] <= 100_000,
        1 <= ret.1.len() <= 100_000,
        forall|i: int| 0 <= i < ret.1.len() ==>
            ret.1[i].len() == 2
            && 0 <= ret.1[i][0] <= ret.1[i][1] < ret.0.len(),
{
    if mutation_kind == 0 {
        // identity
        (nums, queries)
    } else if mutation_kind == 1 && nums[0] < 100_000 {
        // nudge first element up
        let mut n = nums;
        n.set(0, n[0] + 1);
        (n, queries)
    } else if mutation_kind == 2 && nums[0] > 1 {
        // nudge first element down
        let mut n = nums;
        n.set(0, n[0] - 1);
        (n, queries)
    } else if mutation_kind == 3 {
        // set first element to boundary value 1
        let mut n = nums;
        n.set(0, 1);
        (n, queries)
    } else if mutation_kind == 4 {
        // set first element to boundary value 100_000
        let mut n = nums;
        n.set(0, 100_000);
        (n, queries)
    } else if mutation_kind == 5 && nums.len() >= 2 {
        // swap first two elements
        let mut n = nums;
        let a = n[0];
        let b = n[1];
        n.set(0, b);
        n.set(1, a);
        (n, queries)
    } else if mutation_kind == 6 {
        // set all elements to alternating parities: 1, 2, 1, 2, ...
        let mut n = nums;
        let ghost old_len = n.len();
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == old_len,
                1 <= n.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> (
                    if j % 2 == 0 { #[trigger] n[j] == 1i32 } else { #[trigger] n[j] == 2i32 }
                ),
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] n[j] <= 100_000,
                forall|j: int| i <= j < n.len() ==> #[trigger] n[j] == nums[j],
            decreases n.len() - i,
        {
            if i % 2 == 0 {
                n.set(i, 1);
            } else {
                n.set(i, 2);
            }
            i += 1;
        }
        (n, queries)
    } else if mutation_kind == 7 {
        // set all elements to 1 (same parity — no pair is special)
        let mut n = nums;
        let ghost old_len = n.len();
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == old_len,
                1 <= n.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> #[trigger] n[j] == 1i32,
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] n[j] <= 100_000,
                forall|j: int| i <= j < n.len() ==> #[trigger] n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, 1);
            i += 1;
        }
        (n, queries)
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    nums
}

fn random_queries(rng: &mut Rng, num_queries: usize, nums_len: usize) -> Vec<Vec<i32>> {
    let mut queries = Vec::with_capacity(num_queries);
    for _ in 0..num_queries {
        let a = rng.gen_range_usize(0, nums_len - 1) as i32;
        let b = rng.gen_range_usize(a as usize, nums_len - 1) as i32;
        queries.push(vec![a, b]);
    }
    queries
}

fn mutate(nums: Vec<i32>, queries: Vec<Vec<i32>>, mutation_kind: u8) -> (Vec<i32>, Vec<Vec<i32>>) {
    generate_test_case(nums, queries, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3152);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, queries: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}|{:?}", nums, queries);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_array_special(nums.clone(), queries.clone());
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "queries": queries},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    {
        let (n, q) = mutate(vec![3, 4, 1, 2, 6], vec![vec![0, 4]], 0);
        emit(n, q, &mut seen, &mut out, &mut total);
    }
    {
        let (n, q) = mutate(vec![4, 3, 1, 6], vec![vec![0, 2], vec![2, 3]], 0);
        emit(n, q, &mut seen, &mut out, &mut total);
    }

    // Seed inputs with various mutations
    let seed_inputs: Vec<(Vec<i32>, Vec<Vec<i32>>)> = vec![
        (vec![1], vec![vec![0, 0]]),
        (vec![1, 2], vec![vec![0, 1]]),
        (vec![1, 1], vec![vec![0, 1]]),
        (vec![2, 2], vec![vec![0, 1]]),
        (vec![1, 2, 3], vec![vec![0, 2], vec![0, 1], vec![1, 2]]),
        (vec![1, 2, 1, 2, 1], vec![vec![0, 4], vec![0, 0], vec![4, 4]]),
        (vec![2, 2, 2, 2], vec![vec![0, 3], vec![1, 2]]),
        (vec![100_000, 1, 100_000], vec![vec![0, 2]]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    for (nums, queries) in &seed_inputs {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let (n, q) = mutate(nums.clone(), queries.clone(), mk);
            emit(n, q, &mut seen, &mut out, &mut total);
        }
    }

    // Random inputs across diverse size classes
    while total < count {
        let nums_len = match total % 5 {
            0 => rng.gen_range_usize(1, 3),         // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 10_000),  // very large
        };
        let num_queries = match total % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(1, 50),
            3 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 500),
        };
        let nums = random_nums(&mut rng, nums_len);
        let queries = random_queries(&mut rng, num_queries, nums_len);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let (n, q) = mutate(nums, queries, mk);
        emit(n, q, &mut seen, &mut out, &mut total);
    }
}
