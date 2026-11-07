use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: Vec<i32>,
    target_pos: usize,
    target_val: i32,
    start_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= vals.len() <= 1000,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 10000,
        target_pos < vals.len(),
        1 <= target_val <= 10000,
        0 <= start_val < vals.len() as i32,
    ensures
        1 <= result.0.len() <= 1000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000,
        0 <= result.2 < result.0.len(),
        exists|i: int| 0 <= i < result.0.len() && #[trigger] result.0[i] == result.1,
{
    let mut v = vals;
    v.set(target_pos, target_val);

    proof {
        assert(v[target_pos as int] == target_val);
    }

    if mutation_kind == 1 {
        // Set all elements to target_val
        let ghost old_len = v.len();
        let mut j: usize = 0;
        while j < v.len()
            invariant
                0 <= j <= v.len(),
                v.len() == old_len,
                1 <= v.len() <= 1000,
                1 <= target_val <= 10000,
                forall|k: int| 0 <= k < j as int ==> #[trigger] v[k] == target_val,
                forall|k: int| j as int <= k < v.len() ==> 1 <= #[trigger] v[k] <= 10000,
            decreases v.len() - j,
        {
            v.set(j, target_val);
            j += 1;
        }
        proof {
            assert(v[0] == target_val);
        }
        (v, target_val, start_val)
    } else if mutation_kind == 2 {
        // Start at target position (distance = 0)
        (v, target_val, target_pos as i32)
    } else if mutation_kind == 3 {
        // Start at 0
        (v, target_val, 0i32)
    } else if mutation_kind == 4 {
        // Start at last position
        let last_idx = (v.len() - 1) as i32;
        (v, target_val, last_idx)
    } else if mutation_kind == 5 && v.len() > 1 {
        // Also place target at position 0
        v.set(0, target_val);
        proof {
            assert(v[0] == target_val);
        }
        (v, target_val, start_val)
    } else if mutation_kind == 6 {
        // Also place target at last position
        let last = v.len() - 1;
        v.set(last, target_val);
        proof {
            assert(v[last as int] == target_val);
        }
        (v, target_val, start_val)
    } else {
        // Identity / fallback
        (v, target_val, start_val)
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

fn random_vals(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, 10000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1848);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |nums: Vec<i32>, target: i32, start: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= goal { return; }
        let output = Solution::get_min_distance(nums.clone(), target, start);
        let line = json!({
            "input": {"nums": nums, "target": target, "start": start},
            "output": output
        }).to_string();
        if seen.insert(line.clone()) {
            writeln!(out, "{}", line).unwrap();
            *count += 1;
        }
    };

    // ---- Examples from description.md ----
    emit(vec![1,2,3,4,5], 5, 3, &mut seen, &mut out, &mut count);
    emit(vec![1], 1, 0, &mut seen, &mut out, &mut count);
    emit(vec![1,1,1,1,1,1,1,1,1,1], 1, 0, &mut seen, &mut out, &mut count);

    // ---- Seed arrays × all mutations ----
    let seed_cases: Vec<(Vec<i32>, usize, i32, i32)> = vec![
        (vec![5, 3, 7, 5, 2], 0, 5, 2),       // target at start
        (vec![5, 3, 7, 5, 2], 3, 5, 0),        // target in middle
        (vec![1, 2, 3, 4, 5], 4, 5, 0),        // target at end
        (vec![10000], 0, 10000, 0),             // single element, max value
        (vec![1], 0, 1, 0),                     // single element, min value
        (vec![100, 200, 300], 1, 200, 0),       // target already matches
        (vec![1, 1, 1, 1, 1], 2, 1, 4),        // all same, start at end
        (vec![9999, 9998, 9997], 0, 9999, 2),   // near-max values
    ];

    for (vals, tpos, tval, sval) in &seed_cases {
        for mk in 0u8..=6 {
            if count >= goal { break; }
            let (nums, target, start) = generate_test_case(
                vals.clone(), *tpos, *tval, *sval, mk,
            );
            emit(nums, target, start, &mut seen, &mut out, &mut count);
        }
    }

    // ---- Size classes with random parameters ----
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1),       // single element
        (2, 5),       // tiny
        (6, 20),      // small
        (21, 100),    // medium
        (101, 500),   // large
        (501, 1000),  // max
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..5 {
            if count >= goal { break; }
            let n = rng.gen_range_usize(*lo, *hi);
            let vals = random_vals(&mut rng, n);
            let tpos = rng.gen_range_usize(0, n - 1);
            let tval = rng.gen_range_i64(1, 10000) as i32;
            let sval = rng.gen_range_i64(0, (n - 1) as i64) as i32;
            let mk = rng.gen_range_usize(0, 6) as u8;
            let (nums, target, start) = generate_test_case(vals, tpos, tval, sval, mk);
            emit(nums, target, start, &mut seen, &mut out, &mut count);
        }
    }

    // ---- Boundary value targets with random arrays ----
    let boundary_targets: Vec<i32> = vec![1, 2, 9999, 10000, 5000];
    for &bt in &boundary_targets {
        if count >= goal { break; }
        let n = rng.gen_range_usize(2, 50);
        let vals = random_vals(&mut rng, n);
        let tpos = rng.gen_range_usize(0, n - 1);
        let sval = rng.gen_range_i64(0, (n - 1) as i64) as i32;
        let mk = rng.gen_range_usize(0, 6) as u8;
        let (nums, target, start) = generate_test_case(vals, tpos, bt, sval, mk);
        emit(nums, target, start, &mut seen, &mut out, &mut count);
    }

    // ---- Fill remaining with fully random cases ----
    while count < goal {
        let n = rng.gen_range_usize(1, 1000);
        let vals = random_vals(&mut rng, n);
        let tpos = rng.gen_range_usize(0, n - 1);
        let tval = rng.gen_range_i64(1, 10000) as i32;
        let sval = rng.gen_range_i64(0, (n - 1) as i64) as i32;
        let mk = rng.gen_range_usize(0, 6) as u8;
        let (nums, target, start) = generate_test_case(vals, tpos, tval, sval, mk);
        emit(nums, target, start, &mut seen, &mut out, &mut count);
    }
}
