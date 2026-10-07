use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 10_000,
        forall|i: int| 0 <= i < nums.len() ==> i32::MIN <= #[trigger] nums[i] <= i32::MAX,
    ensures
        1 <= result.len() <= 10_000,
        forall|i: int| 0 <= i < result.len() ==> i32::MIN <= #[trigger] result[i] <= i32::MAX,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // set first element to i32::MIN
        let mut v = nums;
        v.set(0, i32::MIN);
        v
    } else if mutation_kind == 2 {
        // set first element to i32::MAX
        let mut v = nums;
        v.set(0, i32::MAX);
        v
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut v = nums;
        v.set(0, 0);
        v
    } else if mutation_kind == 4 && nums.len() < 10_000 {
        // grow by one element (push 0)
        let mut v = nums;
        v.push(0);
        v
    } else if mutation_kind == 5 && nums.len() > 1 {
        // shrink by one element (pop)
        let mut v = nums;
        v.pop();
        v
    } else if mutation_kind == 6 {
        // set last element to i32::MIN
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, i32::MIN);
        v
    } else if mutation_kind == 7 {
        // set last element to i32::MAX
        let mut v = nums;
        let last = v.len() - 1;
        v.set(last, i32::MAX);
        v
    } else if mutation_kind == 8 {
        // set all elements to 0
        let mut v = nums;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == nums.len(),
                1 <= v.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> v[j] == 0i32,
                forall|j: int| i <= j < v.len() ==> v[j] == nums[j],
            decreases v.len() - i,
        {
            v.set(i, 0);
            i += 1;
        }
        v
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first two elements
        let mut v = nums;
        let a = v[0];
        let b = v[1];
        v.set(0, b);
        v.set(1, a);
        v
    } else if mutation_kind == 10 {
        // set first element to 1
        let mut v = nums;
        v.set(0, 1);
        v
    } else if mutation_kind == 11 {
        // set first element to -1
        let mut v = nums;
        v.set(0, -1i32);
        v
    } else {
        // fallback: identity
        nums
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(i32::MIN as i64, i32::MAX as i64) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(414);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::third_max(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![3, 2, 1],
        vec![1, 2],
        vec![2, 2, 3, 1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Curated seeds covering interesting cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1, 1],
        vec![1, 2, 3],
        vec![3, 2, 1],
        vec![1, 1, 1],
        vec![1, 2, 2, 3],
        vec![i32::MIN, i32::MAX, 0],
        vec![i32::MIN, i32::MIN, i32::MIN],
        vec![i32::MAX, i32::MAX, i32::MAX],
        vec![0, 0, 0, 0],
        vec![1, -1, 0],
        vec![5, 5, 5, 4, 4, 4, 3, 3, 3],
        vec![i32::MIN, i32::MIN + 1, i32::MAX],
        vec![i32::MAX, i32::MAX - 1, i32::MAX - 2],
        vec![-1, -2, -3],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with diverse sizes and mutations
    for _ in 0..80 {
        if count >= target { break; }
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // max
        };
        let nums = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 11) as u8;
        emit(mutate(nums, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random arrays, identity mutation
    while count < target {
        let len = rng.gen_range_usize(1, 10_000);
        let nums = random_nums(&mut rng, len);
        emit(mutate(nums, 0), &mut seen, &mut out, &mut count);
    }
}
