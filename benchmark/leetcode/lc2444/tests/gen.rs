use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: Vec<i32>,
    min_k: i32,
    max_k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        2 <= values.len() <= 100_000,
        1 <= min_k <= 1_000_000,
        1 <= max_k <= 1_000_000,
        forall|i: int| 0 <= i && i < values.len() ==> 1 <= #[trigger] values[i] && values[i] <= 1_000_000,
    ensures
        2 <= result.0.len() && result.0.len() <= 100_000,
        1 <= result.1 && result.1 <= 1_000_000,
        1 <= result.2 && result.2 <= 1_000_000,
        forall|i: int| 0 <= i && i < result.0.len() ==> 1 <= #[trigger] result.0[i] && result.0[i] <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        (values, min_k, max_k)
    } else if mutation_kind == 1 {
        // set first element to min_k
        let mut v = values;
        v.set(0, min_k);
        (v, min_k, max_k)
    } else if mutation_kind == 2 {
        // set last element to max_k
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, max_k);
        (v, min_k, max_k)
    } else if mutation_kind == 3 {
        // set first element to min_k and last to max_k
        let mut v = values;
        v.set(0, min_k);
        let last = v.len() - 1;
        v.set(last, max_k);
        (v, min_k, max_k)
    } else if mutation_kind == 4 {
        // set all elements to min_k
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                2 <= v.len() <= 100_000,
                forall|j: int| 0 <= j && j < i ==> v[j] == min_k,
                forall|j: int| i <= j && j < v.len() ==> v[j] == values[j],
                1 <= min_k <= 1_000_000,
            decreases v.len() - i,
        {
            v.set(i, min_k);
            i += 1;
        }
        (v, min_k, max_k)
    } else if mutation_kind == 5 {
        // set all elements to max_k
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                2 <= v.len() <= 100_000,
                forall|j: int| 0 <= j && j < i ==> v[j] == max_k,
                forall|j: int| i <= j && j < v.len() ==> v[j] == values[j],
                1 <= max_k <= 1_000_000,
            decreases v.len() - i,
        {
            v.set(i, max_k);
            i += 1;
        }
        (v, min_k, max_k)
    } else if mutation_kind == 6 && min_k == max_k {
        // when min_k == max_k, set all to that value (all subarrays are fixed-bound)
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                2 <= v.len() <= 100_000,
                forall|j: int| 0 <= j && j < i ==> v[j] == min_k,
                forall|j: int| i <= j && j < v.len() ==> v[j] == values[j],
                1 <= min_k <= 1_000_000,
            decreases v.len() - i,
        {
            v.set(i, min_k);
            i += 1;
        }
        (v, min_k, max_k)
    } else if mutation_kind == 7 && max_k < 1_000_000 {
        // nudge max_k up by 1
        (values, min_k, (max_k + 1) as i32)
    } else if mutation_kind == 8 && min_k > 1 {
        // nudge min_k down by 1
        (values, (min_k - 1) as i32, max_k)
    } else if mutation_kind == 9 {
        // swap min_k and max_k
        (values, max_k, min_k)
    } else if mutation_kind == 10 && values.len() > 2 {
        // shrink: remove last element
        let mut v = values;
        v.pop();
        (v, min_k, max_k)
    } else if mutation_kind == 11 && values.len() < 100_000 {
        // grow: push min_k
        let mut v = values;
        v.push(min_k);
        (v, min_k, max_k)
    } else {
        // fallback: identity
        (values, min_k, max_k)
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

fn mutate(values: Vec<i32>, min_k: i32, max_k: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(values, min_k, max_k, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_values(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2444);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, min_k: i32, max_k: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= count_target { return; }
        let key = format!("{:?},{},{}", nums, min_k, max_k);
        if !seen.insert(key) { return; }
        let output = Solution::count_subarrays(nums.clone(), min_k, max_k);
        writeln!(out, "{}", json!({
            "input": {"nums": nums, "minK": min_k, "maxK": max_k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example test cases from description
    {
        let (nums, mk, xk) = mutate(vec![1,3,5,2,7,5], 1, 5, 0);
        emit(nums, mk, xk, &mut seen, &mut out, &mut count);
    }
    {
        let (nums, mk, xk) = mutate(vec![1,1,1,1], 1, 1, 0);
        emit(nums, mk, xk, &mut seen, &mut out, &mut count);
    }

    // Structured seeds with all mutations
    let seeds: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1, 1_000_000], 1, 1_000_000),
        (vec![5, 5], 5, 5),
        (vec![1, 2, 3, 4, 5], 1, 5),
        (vec![3, 1, 5, 2, 4], 1, 5),
        (vec![1, 1, 1, 1, 1], 1, 1),
        (vec![500_000, 500_000, 500_000], 500_000, 500_000),
        (vec![1, 1_000_000, 500_000], 1, 1_000_000),
        (vec![2, 3, 2, 3, 2], 2, 3),
        (vec![10, 20, 30, 10, 20, 30], 10, 30),
        (vec![1, 2, 1, 2, 1, 2], 1, 2),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    for (s_vals, s_min, s_max) in &seeds {
        for &mk in &mutation_kinds {
            if count >= count_target { break; }
            let (nums, min_k, max_k) = mutate(s_vals.clone(), *s_min, *s_max, mk);
            emit(nums, min_k, max_k, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes
    while count < count_target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10_000),
        };

        let min_k = rng.gen_range_i64(1, 1_000_000) as i32;
        let max_k = rng.gen_range_i64(min_k as i64, 1_000_000) as i32;

        // Generate values mostly in [min_k, max_k] range with some out-of-range
        let vals = random_values(&mut rng, n, 1, 1_000_000);

        let mk = rng.gen_range_usize(0, 11) as u8;
        let (nums, mk_out, xk_out) = mutate(vals, min_k, max_k, mk);
        emit(nums, mk_out, xk_out, &mut seen, &mut out, &mut count);
    }
}
