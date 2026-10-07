use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
    ensures
        2 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        // set last element to 100 (maximum boundary)
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 100);
        d
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 100
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                2 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 100i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 100);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow by one element (push 50)
        let mut d = nums;
        d.push(50);
        d
    } else if mutation_kind == 6 && nums.len() > 2 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 && nums.len() >= 2 {
        // swap first two elements
        let mut d = nums;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else if mutation_kind == 8 {
        // nudge last element up (if < 100)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 100 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 9 {
        // nudge last element down (if > 1)
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::count_partitions(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![10, 10, 3, 7, 6],  // output: 4
        vec![1, 2, 2],          // output: 0
        vec![2, 4, 6, 8],       // output: 3
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed pool: interesting arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![100, 100],
        vec![1, 100],
        vec![50, 50],
        vec![1, 2, 3, 4, 5],
        vec![99, 99, 99],
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1],
        vec![2, 2],
        vec![1, 2],
        vec![3, 3, 3],
        vec![50, 51],
        vec![100, 1, 100, 1],
    ];

    let mutation_kinds: Vec<u8> = (0..=10).collect();

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            if count >= goal { break; }
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < goal {
        let len = match count % 5 {
            0 => rng.gen_range_usize(2, 5),     // tiny
            1 => rng.gen_range_usize(2, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let seed_arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = generate_test_case(seed_arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
