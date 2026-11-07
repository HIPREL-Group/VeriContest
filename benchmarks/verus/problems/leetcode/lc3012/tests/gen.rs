use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum value — important for this problem)
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1);
        v
    } else if mutation_kind == 2 {
        // set first element to 1
        let mut v = nums;
        v.set(0, 1);
        v
    } else if mutation_kind == 3 {
        // set all elements to same value as first element (all-divisible case)
        let mut v = nums;
        let val = v[0];
        let mut i: usize = 1;
        while i < v.len()
            invariant
                1 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100_000,
                1 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> v[j] == val,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] v[j] <= 1_000_000_000,
                forall|j: int| i <= j < v.len() ==> 1 <= #[trigger] v[j] <= 1_000_000_000,
            decreases v.len() - i,
        {
            v.set(i, val);
            i += 1;
        }
        v
    } else if mutation_kind == 4 && nums.len() < 100_000 {
        // grow by pushing element 1
        let mut v = nums;
        v.push(1);
        v
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by popping last element
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 6 {
        // set last element to max boundary
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, 1_000_000_000);
        v
    } else if mutation_kind == 7 {
        // nudge last element up (if below max)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] < 1_000_000_000 {
            v.set(last, v[last] + 1);
        }
        v
    } else if mutation_kind == 8 {
        // nudge last element down (if above min)
        let mut v = nums;
        let last = v.len() - 1;
        if v[last] > 1 {
            v.set(last, v[last] - 1);
        }
        v
    } else if mutation_kind == 9 {
        // set all elements to 1 (all-minimum case)
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> v[j] == 1i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] v[j] <= 1_000_000_000,
                forall|j: int| i <= j < v.len() ==> 1 <= #[trigger] v[j] <= 1_000_000_000,
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        v
    } else {
        // fallback: identity
        nums
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

fn make_array(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
}

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let num_mutations: u8 = 10;
    let mut generated: usize = 0;

    // Example inputs from description.md — routed through generate_test_case (identity mutation)
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 4, 3, 1],
        vec![5, 5, 5, 10, 5],
        vec![2, 3, 4],
    ];

    for ex in &examples {
        if generated >= count { break; }
        let nums = mutate(ex.clone(), 0);
        let result = Solution::minimum_array_length(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    // Structured test cases: diverse sizes × all mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),        // tiny
        (1, 10),       // small
        (11, 100),     // medium
        (101, 1000),   // large
        (1001, 10000), // big
    ];

    for (lo, hi) in &size_classes {
        for mk in 0..num_mutations {
            if generated >= count { break; }
            let n = rng.gen_range_usize(*lo, *hi);
            let base = make_array(&mut rng, n);
            let nums = mutate(base, mk);
            let result = Solution::minimum_array_length(nums.clone());
            writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
            generated += 1;
        }
    }

    // Fill remaining with random cases
    let mut _attempts: usize = 0;
    while generated < count {
        _attempts += 1;
        if _attempts > 10000 { break; }
        let n = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let base = make_array(&mut rng, n);
        let nums = mutate(base, mk);
        let result = Solution::minimum_array_length(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": result})).unwrap();
        generated += 1;
    }

    eprintln!("Generated {} test cases to {:?}", generated, out_path);
}
