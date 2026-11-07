use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    queries: Vec<i32>,
    x: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= nums.len() <= 100000,
        1 <= queries.len() <= 100000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000,
        forall|i: int| 0 <= i < queries.len() ==> 1 <= #[trigger] queries[i] <= 100000,
        1 <= x <= 10000,
    ensures
        1 <= result.0.len() <= 100000,
        1 <= result.1.len() <= 100000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100000,
        1 <= result.2 <= 10000,
{
    if mutation_kind == 0 {
        // identity
        (nums, queries, x)
    } else if mutation_kind == 1 {
        // set first element of nums to x (guarantees at least one occurrence)
        let mut n = nums;
        n.set(0, x);
        (n, queries, x)
    } else if mutation_kind == 2 {
        // set all elements of nums to x (every position is an occurrence)
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 100000,
                1 <= x <= 10000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] n[j] == x,
                forall|j: int| i as int <= j < n.len() ==> #[trigger] n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, x);
            i += 1;
        }
        (n, queries, x)
    } else if mutation_kind == 3 {
        // set all elements of nums to a value != x (x never appears)
        let alt: i32 = if x == 1 { 2i32 } else { 1i32 };
        let mut n = nums;
        let mut i: usize = 0;
        while i < n.len()
            invariant
                0 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 100000,
                1 <= alt <= 10000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] n[j] == alt,
                forall|j: int| i as int <= j < n.len() ==> #[trigger] n[j] == nums[j],
            decreases n.len() - i,
        {
            n.set(i, alt);
            i += 1;
        }
        (n, queries, x)
    } else if mutation_kind == 4 && nums.len() < 100000 {
        // grow nums by pushing x at the end
        let mut n = nums;
        n.push(x);
        (n, queries, x)
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink nums by popping last element
        let mut n = nums;
        n.pop();
        (n, queries, x)
    } else if mutation_kind == 6 {
        // set first query to 1 (ask for first occurrence)
        let mut q = queries;
        q.set(0, 1i32);
        (nums, q, x)
    } else if mutation_kind == 7 {
        // set first query to 100000 (large k, likely -1 result)
        let mut q = queries;
        q.set(0, 100000i32);
        (nums, q, x)
    } else if mutation_kind == 8 && x < 10000 {
        // nudge x up
        (nums, queries, x + 1)
    } else if mutation_kind == 9 && x > 1 {
        // nudge x down
        (nums, queries, x - 1)
    } else {
        // fallback: identity
        (nums, queries, x)
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
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 10000) as i32);
    }
    v
}

fn random_queries(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100000) as i32);
    }
    v
}

fn mutate(nums: Vec<i32>, queries: Vec<i32>, x: i32, mk: u8) -> (Vec<i32>, Vec<i32>, i32) {
    generate_test_case(nums, queries, x, mk)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3159);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, queries: Vec<i32>, x: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}|{:?}|{}", nums, queries, x);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::occurrences_of_element(nums.clone(), queries.clone(), x);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "queries": queries, "x": x},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    emit(vec![1,3,1,7], vec![1,3,2,4], 1, &mut seen, &mut out, &mut count);
    emit(vec![1,2,3], vec![10], 5, &mut seen, &mut out, &mut count);

    // Seed inputs for mutation
    let seed_cases: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![1,3,1,7], vec![1,3,2,4], 1),
        (vec![1,2,3], vec![10], 5),
        (vec![1], vec![1], 1),
        (vec![10000], vec![1], 10000),
        (vec![5,5,5,5,5], vec![1,2,3,4,5], 5),
        (vec![1,2,3,4,5], vec![1,2,3,4,5], 3),
        (vec![1,1,1,1], vec![1,2,3,4,5], 1),
        (vec![2,4,6,8], vec![1], 3),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for (nums, queries, x) in &seed_cases {
        for &mk in &mutation_kinds {
            if count >= target { break; }
            let (rn, rq, rx) = mutate(nums.clone(), queries.clone(), *x, mk);
            emit(rn, rq, rx, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes
    while count < target {
        // Size class for nums
        let n_len: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10000),  // big
        };

        // Size class for queries
        let q_len: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        let nums = random_nums(&mut rng, n_len);
        let queries = random_queries(&mut rng, q_len);

        // Mix boundary x values ~20% of the time
        let x: i32 = if rng.gen_range_usize(0, 4) == 0 {
            *[1i32, 10000, 5000, 1, 9999].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            rng.gen_range_i64(1, 10000) as i32
        };

        let mk = rng.gen_range_usize(0, 9) as u8;
        let (rn, rq, rx) = mutate(nums, queries, x, mk);
        emit(rn, rq, rx, &mut seen, &mut out, &mut count);
    }
}
