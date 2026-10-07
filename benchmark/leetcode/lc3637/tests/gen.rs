use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= nums.len() <= 100,
        forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
    ensures
        3 <= result.len() <= 100,
        forall|i: int| 0 <= i && i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 {
        // nudge first element up
        let mut d = nums;
        if d[0] < 1000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 2 {
        // nudge first element down
        let mut d = nums;
        if d[0] > -1000 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 4 {
        // negate first element
        let mut d = nums;
        if d[0] > -1000 && d[0] < 1000 {
            d.set(0, -d[0]);
        }
        d
    } else if mutation_kind == 5 && nums.len() < 100 {
        // grow by one element (push 0)
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 6 && nums.len() > 3 {
        // shrink by one element (pop)
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // set all elements to the same value (first element)
        let val = nums[0];
        let n = nums.len();
        let mut d = nums;
        let mut i: usize = 1;
        while i < n
            invariant
                0 < i <= n,
                d.len() == n,
                3 <= n <= 100,
                -1000 <= val <= 1000,
                forall|j: int| 0 <= j < i as int ==> d[j] == val,
                forall|j: int| i as int <= j < n as int ==> d[j] == nums[j],
                forall|j: int| 0 <= j < n as int ==> -1000 <= #[trigger] d[j] <= 1000,
            decreases n - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 8 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else if mutation_kind == 9 {
        // set first element to boundary -1000
        let mut d = nums;
        d.set(0, -1000);
        d
    } else if mutation_kind == 10 {
        // set first element to boundary 1000
        let mut d = nums;
        d.set(0, 1000);
        d
    } else {
        // fallback
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    v
}

fn make_trionic(rng: &mut Rng, len: usize) -> Vec<i32> {
    // Build an array that IS trionic: inc then dec then inc
    assert!(len >= 4);
    let p = 1 + rng.gen_range_usize(0, len.saturating_sub(4));
    let q = p + 1 + rng.gen_range_usize(0, len.saturating_sub(p + 3));
    let mut v = Vec::with_capacity(len);
    // Strictly increasing prefix [0..=p]
    let mut cur = rng.gen_range_i64(-1000, 0) as i32;
    for _ in 0..=p {
        v.push(cur);
        let step = rng.gen_range_i64(1, 10) as i32;
        cur = (cur + step).min(1000);
    }
    // Strictly decreasing mid [p+1..=q]
    cur = v[p] - 1;
    for _ in (p + 1)..=q {
        v.push(cur);
        let step = rng.gen_range_i64(1, 10) as i32;
        cur = (cur - step).max(-1000);
    }
    // Strictly increasing suffix [q+1..len-1]
    cur = v[q] + 1;
    for _ in (q + 1)..len {
        v.push(cur);
        let step = rng.gen_range_i64(1, 10) as i32;
        cur = (cur + step).min(1000);
    }
    // Clamp all values
    for x in v.iter_mut() {
        *x = (*x).max(-1000).min(1000);
    }
    v
}

fn make_monotone_inc(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    let mut cur = rng.gen_range_i64(-1000, 0) as i32;
    for _ in 0..len {
        v.push(cur);
        let step = rng.gen_range_i64(1, 10) as i32;
        cur = (cur + step).min(1000);
    }
    v
}

fn make_monotone_dec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    let mut cur = rng.gen_range_i64(0, 1000) as i32;
    for _ in 0..len {
        v.push(cur);
        let step = rng.gen_range_i64(1, 10) as i32;
        cur = (cur - step).max(-1000);
    }
    v
}

fn make_constant(len: usize, val: i32) -> Vec<i32> {
    vec![val; len]
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3637);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", nums);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_trionic(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 3, 5, 4, 2, 6],       // true
        vec![2, 1, 3],                 // false
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Seed arrays: trionic arrays (should be true)
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1, 3, 2, 4],                         // minimal trionic len=4
        vec![1, 5, 3, 2, 4, 7],
        vec![-5, 0, 10, 5, -3, 0, 8],
        vec![1, 2, 3, 2, 1, 2, 3],
        vec![-1000, 0, 1000, 0, -1000, 0, 1000],  // boundary values
    ];

    // Seed arrays: non-trionic arrays (should be false)
    let non_trionic_seeds: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],                            // strictly increasing, too short pattern
        vec![3, 2, 1],                            // strictly decreasing
        vec![5, 5, 5],                            // constant
        vec![1, 2, 3, 4, 5],                      // monotone inc
        vec![5, 4, 3, 2, 1],                      // monotone dec
        vec![1, 3, 2],                            // V-shape but len=3, no room for q
        vec![0, 0, 0, 0, 0],                      // all zeros
        vec![-1000, -1000, -1000],                 // all min boundary
        vec![1000, 1000, 1000],                    // all max boundary
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply mutations to trionic seeds
    for seed_arr in &seed_arrays {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Apply mutations to non-trionic seeds
    for seed_arr in &non_trionic_seeds {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random trionic arrays with mutations (diverse sizes)
    for i in 0..20 {
        if count >= target_count { break; }
        let len = match i % 5 {
            0 => rng.gen_range_usize(4, 6),        // tiny
            1 => rng.gen_range_usize(4, 10),       // small
            2 => rng.gen_range_usize(11, 30),      // medium
            3 => rng.gen_range_usize(31, 60),      // large
            _ => rng.gen_range_usize(61, 100),     // max
        };
        let arr = make_trionic(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Random non-trionic shapes
    for i in 0..15 {
        if count >= target_count { break; }
        let len = match i % 5 {
            0 => 3,
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 30),
            3 => rng.gen_range_usize(31, 60),
            _ => rng.gen_range_usize(61, 100),
        };
        let arr = match i % 3 {
            0 => make_monotone_inc(&mut rng, len),
            1 => make_monotone_dec(&mut rng, len),
            _ => make_constant(len, rng.gen_range_i64(-1000, 1000) as i32),
        };
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with fully random arrays + random mutations
    while count < target_count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(3, 5),
            1 => rng.gen_range_usize(3, 10),
            2 => rng.gen_range_usize(11, 50),
            _ => rng.gen_range_usize(51, 100),
        };
        let arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
