use vstd::prelude::*;

verus! {

pub open spec fn seq_sum(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        seq_sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1] as int
    }
}

pub open spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn min_elements_spec(diff: int, limit: int) -> int {
    (diff + limit - 1) / limit
}

proof fn seq_sum_all_same(s: Seq<i32>, v: i32)
    requires
        forall |i: int| 0 <= i < s.len() ==> s[i] == v,
    ensures
        seq_sum(s) == s.len() * (v as int),
    decreases s.len(),
{
    if s.len() > 0 {
        let n = s.len();
        let prefix = s.subrange(0, n - 1);
        assert forall |i: int| 0 <= i < prefix.len() implies prefix[i] == v by {
            assert(prefix[i] == s[i]);
        }
        seq_sum_all_same(prefix, v);
        assert(prefix.len() == n - 1);
        assert(seq_sum(prefix) == (n - 1) * (v as int));
        assert(s[n - 1] == v);
        assert(seq_sum(s) == seq_sum(prefix) + s[n - 1] as int);
        assert(seq_sum(s) == (n - 1) * (v as int) + v as int);
        assert((n - 1) * (v as int) + v as int == n * (v as int)) by (nonlinear_arith)
            requires n == s.len(), v == v as int
        ;
    }
}

pub fn generate_test_case(
    n: usize,
    limit: i32,
    goal: i32,
    fill_value: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= n <= 100_000,
        1 <= limit <= 1_000_000,
        -limit <= fill_value <= limit,
        -1_000_000_000 <= goal <= 1_000_000_000,
        min_elements_spec(abs_int(n as int * fill_value as int - goal as int), limit as int) <= i32::MAX as int,
    ensures
        1 <= result.0@.len() <= 100_000,
        1 <= result.1 <= 1_000_000,
        forall |i: int| 0 <= i < result.0@.len() ==> -result.1 <= (#[trigger] result.0@[i]) && result.0@[i] <= result.1,
        -1_000_000_000 <= result.2 <= 1_000_000_000,
        min_elements_spec(abs_int(seq_sum(result.0@) - result.2 as int), result.1 as int) <= i32::MAX as int,
{
    if mutation_kind == 1 {
        // Zero-fill mutation: all elements are 0, goal unchanged.
        // sum = 0, diff = |goal|, result = ceil(|goal| / limit).
        // |goal| <= 1e9, limit >= 1 => result <= 1e9 < i32::MAX.
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100_000,
                nums.len() == i,
                forall |j: int| 0 <= j < i ==> nums@[j] == 0i32,
                1 <= limit <= 1_000_000,
            decreases n - i,
        {
            nums.push(0i32);
            i = i + 1;
        }
        proof {
            seq_sum_all_same(nums@, 0i32);
            assert(seq_sum(nums@) == 0);
            assert(abs_int(0 - goal as int) == abs_int(goal as int));
            let diff = abs_int(goal as int);
            assert(diff <= 1_000_000_000);
            assert(diff + limit as int - 1 <= 1_000_999_999);
            assert(1_000_999_999 <= i32::MAX as int);
        }
        (nums, limit, goal)
    } else if mutation_kind == 2 {
        // Single-element mutation: array of length 1 with fill_value.
        // sum = fill_value, |fill_value| <= limit <= 1e6.
        // diff = |fill_value - goal| <= 1e6 + 1e9 < i32::MAX.
        let mut nums: Vec<i32> = Vec::new();
        nums.push(fill_value);
        proof {
            let s = nums@;
            assert(s.len() == 1);
            assert(s[0] == fill_value);
            assert(seq_sum(s) == seq_sum(s.subrange(0, 0)) + s[0] as int);
            assert(s.subrange(0, 0).len() == 0);
            assert(seq_sum(s.subrange(0, 0)) == 0);
            assert(seq_sum(s) == fill_value as int);
            let diff = abs_int(fill_value as int - goal as int);
            assert(-1_000_000 <= fill_value as int <= 1_000_000);
            assert(-1_000_000_000 <= goal as int <= 1_000_000_000);
            assert(diff <= 1_001_000_000int);
            assert(diff + limit as int - 1 <= 1_001_999_999);
            assert(1_001_999_999 < i32::MAX as int);
        }
        (nums, limit, goal)
    } else if mutation_kind == 3 {
        // Zero-fill, zero-goal mutation: diff = 0, result = 0.
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100_000,
                nums.len() == i,
                forall |j: int| 0 <= j < i ==> nums@[j] == 0i32,
                1 <= limit <= 1_000_000,
            decreases n - i,
        {
            nums.push(0i32);
            i = i + 1;
        }
        proof {
            seq_sum_all_same(nums@, 0i32);
            assert(seq_sum(nums@) == 0);
            assert(abs_int(0int) == 0);
            assert(min_elements_spec(0, limit as int) == (0 + limit as int - 1) / limit as int);
            assert(0 <= limit as int - 1 < limit as int);
        }
        (nums, limit, 0i32)
    } else {
        // Identity mutation (mutation_kind == 0 or fallback):
        // Build array of n copies of fill_value.
        let mut nums: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 100_000,
                nums.len() == i,
                forall |j: int| 0 <= j < i ==> nums@[j] == fill_value,
                1 <= limit <= 1_000_000,
                -limit <= fill_value <= limit,
            decreases n - i,
        {
            nums.push(fill_value);
            i = i + 1;
        }
        proof {
            seq_sum_all_same(nums@, fill_value);
            assert(seq_sum(nums@) == n as int * fill_value as int);
        }
        (nums, limit, goal)
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

fn check_overflow(sum: i64, goal: i64, limit: i64) -> bool {
    let diff = (sum - goal).abs();
    let result = (diff + limit - 1) / limit;
    result <= i32::MAX as i64
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |nums: Vec<i32>, limit: i32, goal: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    total: &mut usize| {
        if *total >= count {
            return;
        }
        let key = format!("{:?}|{}|{}", nums, limit, goal);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::min_elements(nums.clone(), limit, goal);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "limit": limit, "goal": goal},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    emit(vec![1, -1, 1], 3, -4, &mut seen, &mut out, &mut total);
    emit(vec![1, -10, 9, 1], 100, 0, &mut seen, &mut out, &mut total);

    // Seed configurations: (n, limit, goal, fill_value)
    let configs: Vec<(usize, i32, i32, i32)> = vec![
        (1, 1, 0, 0),
        (1, 1, 1, 0),
        (1, 1, -1, 0),
        (1, 1_000_000, 1_000_000_000, 0),
        (1, 1_000_000, -1_000_000_000, 0),
        (1, 1, 1_000_000_000, 0),
        (1, 1, -1_000_000_000, 0),
        (5, 3, -4, 0),
        (4, 100, 0, 1),
        (10, 10, 50, 5),
        (10, 10, -50, -5),
        (3, 1, 0, 1),
        (3, 1, 0, -1),
        (100, 1000, 500, 5),
        (1000, 100, 0, 0),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3];

    for &(n, limit, goal, fill) in &configs {
        for &mk in &mutation_kinds {
            let sum = n as i64 * fill as i64;
            if !check_overflow(sum, goal as i64, limit as i64) {
                continue;
            }
            let (nums, rl, rg) = generate_test_case(n, limit, goal, fill, mk);
            emit(nums, rl, rg, &mut seen, &mut out, &mut total);
        }
    }

    // Diverse random generation
    while total < count {
        // Size classes for array length
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };

        // Limit: mix boundary and random values
        let limit: i32 = if total % 10 == 0 {
            1
        } else if total % 10 == 1 {
            1_000_000
        } else {
            rng.gen_range_i64(1, 1_000_000) as i32
        };

        // Goal: mix boundary and random values
        let goal: i32 = if total % 7 == 0 {
            0
        } else if total % 7 == 1 {
            1_000_000_000
        } else if total % 7 == 2 {
            -1_000_000_000
        } else {
            rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32
        };

        // Fill value: bounded by limit, with boundary values mixed in
        let fill_value: i32 = if total % 5 == 0 {
            0
        } else if total % 5 == 1 {
            limit
        } else if total % 5 == 2 {
            -limit
        } else if total % 5 == 3 {
            1i32.min(limit)
        } else {
            rng.gen_range_i64(-limit as i64, limit as i64) as i32
        };

        let sum = n as i64 * fill_value as i64;
        if !check_overflow(sum, goal as i64, limit as i64) {
            continue;
        }

        let mk = rng.gen_range_usize(0, 3) as u8;
        let (nums, rl, rg) = generate_test_case(n, limit, goal, fill_value, mk);
        emit(nums, rl, rg, &mut seen, &mut out, &mut total);
    }
}
