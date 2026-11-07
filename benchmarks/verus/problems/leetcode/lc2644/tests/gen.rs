use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    divisors: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums.len() <= 1000,
        1 <= divisors.len() <= 1000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < divisors.len() ==> 1 <= #[trigger] divisors[i] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        (nums, divisors)
    } else if mutation_kind == 1 {
        // set first element of nums to 1 (min boundary)
        let mut n = nums;
        n.set(0, 1);
        (n, divisors)
    } else if mutation_kind == 2 {
        // set first element of nums to max boundary
        let mut n = nums;
        n.set(0, 1_000_000_000);
        (n, divisors)
    } else if mutation_kind == 3 {
        // set first element of divisors to 1 (divides everything)
        let mut d = divisors;
        d.set(0, 1);
        (nums, d)
    } else if mutation_kind == 4 {
        // set first element of divisors to max boundary
        let mut d = divisors;
        d.set(0, 1_000_000_000);
        (nums, d)
    } else if mutation_kind == 5 {
        // set all nums to the same value as nums[0]
        let val = nums[0];
        let mut n = nums;
        let mut i: usize = 1;
        while i < n.len()
            invariant
                1 <= i <= n.len(),
                n.len() == nums.len(),
                1 <= n.len() <= 1000,
                1 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> n[j] == val,
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] n[j] <= 1_000_000_000,
                forall|j: int| i <= j < n.len() ==> n[j] == nums[j],
                forall|j: int| i <= j < n.len() ==> 1 <= #[trigger] n[j] <= 1_000_000_000,
            decreases n.len() - i,
        {
            n.set(i, val);
            i = i + 1;
        }
        (n, divisors)
    } else if mutation_kind == 6 {
        // set all divisors to the same value as divisors[0]
        let val = divisors[0];
        let mut d = divisors;
        let mut i: usize = 1;
        while i < d.len()
            invariant
                1 <= i <= d.len(),
                d.len() == divisors.len(),
                1 <= d.len() <= 1000,
                1 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] d[j] <= 1_000_000_000,
                forall|j: int| i <= j < d.len() ==> d[j] == divisors[j],
                forall|j: int| i <= j < d.len() ==> 1 <= #[trigger] d[j] <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, val);
            i = i + 1;
        }
        (nums, d)
    } else if mutation_kind == 7 && nums.len() < 1000 {
        // grow nums by pushing nums[0]
        let val = nums[0];
        let mut n = nums;
        n.push(val);
        (n, divisors)
    } else if mutation_kind == 8 && nums.len() > 1 {
        // shrink nums by popping last element
        let mut n = nums;
        n.pop();
        (n, divisors)
    } else if mutation_kind == 9 && divisors.len() < 1000 {
        // grow divisors by pushing divisors[0]
        let val = divisors[0];
        let mut d = divisors;
        d.push(val);
        (nums, d)
    } else if mutation_kind == 10 && divisors.len() > 1 {
        // shrink divisors by popping last element
        let mut d = divisors;
        d.pop();
        (nums, d)
    } else if mutation_kind == 11 && nums.len() >= 2 {
        // swap first two elements of nums
        let mut n = nums;
        let a = n[0];
        let b = n[1];
        n.set(0, b);
        n.set(1, a);
        proof {
            assert(1 <= n[0] <= 1_000_000_000);
            assert(1 <= n[1] <= 1_000_000_000);
            assert forall|i: int| 0 <= i < n.len()
                implies 1 <= #[trigger] n[i] <= 1_000_000_000
            by {
                if i == 0 {
                    assert(n[0] == b);
                } else if i == 1 {
                    assert(n[1] == a);
                } else {
                    assert(n[i] == nums[i]);
                }
            };
        }
        (n, divisors)
    } else if mutation_kind == 12 {
        // nudge last element of nums up (if possible)
        let mut n = nums;
        let last = n.len() - 1;
        if n[last] < 1_000_000_000 {
            n.set(last, n[last] + 1);
        }
        (n, divisors)
    } else if mutation_kind == 13 {
        // nudge last element of nums down (if possible)
        let mut n = nums;
        let last = n.len() - 1;
        if n[last] > 1 {
            n.set(last, n[last] - 1);
        }
        (n, divisors)
    } else if mutation_kind == 14 {
        // set last divisor = first num (guarantees at least one divisibility)
        let val = nums[0];
        let mut d = divisors;
        let last = d.len() - 1;
        d.set(last, val);
        (nums, d)
    } else {
        // fallback: identity
        (nums, divisors)
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

fn random_array(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(lo, hi) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2644);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, divisors: Vec<i32>, mk: u8,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count { return; }
        let (n, d) = generate_test_case(nums, divisors, mk);
        let result = Solution::max_div_score(n.clone(), d.clone());
        let line = json!({
            "input": {"nums": n, "divisors": d},
            "output": result
        }).to_string();
        if seen.insert(line.clone()) {
            writeln!(out, "{}", line).unwrap();
            *count += 1;
        }
    };

    // ---- Example inputs from description.md ----
    emit(vec![2, 9, 15, 50], vec![5, 3, 7, 2], 0,
         &mut seen, &mut out, &mut count);
    emit(vec![4, 7, 9, 3, 9], vec![5, 2, 3], 0,
         &mut seen, &mut out, &mut count);
    emit(vec![20, 14, 21, 10], vec![10, 16, 20], 0,
         &mut seen, &mut out, &mut count);

    // ---- Boundary seeds with all mutations ----
    let boundary_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),
        (vec![1_000_000_000], vec![1_000_000_000]),
        (vec![1], vec![1_000_000_000]),
        (vec![1_000_000_000], vec![1]),
        (vec![1, 2, 3], vec![1]),
        (vec![6, 12, 18], vec![6, 3, 2]),
        (vec![7, 11, 13], vec![7, 11, 13]),
        (vec![100, 200, 300, 400, 500], vec![100, 50, 25, 10, 5, 2, 1]),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14];

    for (nums, divs) in &boundary_seeds {
        for &mk in &mutation_kinds {
            emit(nums.clone(), divs.clone(), mk,
                 &mut seen, &mut out, &mut count);
        }
    }

    // ---- Random test cases with varied sizes ----
    while count < target_count {
        // Pick size class for nums
        let n_len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),      // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 1000),  // max
        };
        // Pick size class for divisors
        let d_len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };

        // Value range: mix small and large values
        let (lo, hi): (i64, i64) = match rng.gen_range_usize(0, 3) {
            0 => (1, 20),                  // small values (more divisibility)
            1 => (1, 1000),                // medium values
            2 => (1, 1_000_000),           // large values
            _ => (1, 1_000_000_000),       // full range
        };

        let nums = random_array(&mut rng, n_len, lo, hi);
        let divs = random_array(&mut rng, d_len, lo, hi);
        let mk = rng.gen_range_usize(0, 14) as u8;

        emit(nums, divs, mk, &mut seen, &mut out, &mut count);
    }
}
