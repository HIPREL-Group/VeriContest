use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, n: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 500,
        values.len() == 2 * n,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= result.1 <= 500,
        result.0.len() == 2 * result.1,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (values, n)
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut v = values;
        v.set(0, 1);
        (v, n)
    } else if mutation_kind == 2 {
        // set first element to 1000 (max boundary)
        let mut v = values;
        v.set(0, 1000);
        (v, n)
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                v.len() == 2 * n,
                1 <= n <= 500,
                forall |j: int| 0 <= j < i ==> #[trigger] v[j] == 1,
                forall |j: int| i <= j < v.len() ==> #[trigger] v[j] == values[j],
            decreases v.len() - i,
        {
            v.set(i, 1);
            i += 1;
        }
        (v, n)
    } else if mutation_kind == 4 {
        // set all elements to 1000
        let mut v = values;
        let mut i: usize = 0;
        while i < v.len()
            invariant
                0 <= i <= v.len(),
                v.len() == values.len(),
                v.len() == 2 * n,
                1 <= n <= 500,
                forall |j: int| 0 <= j < i ==> #[trigger] v[j] == 1000,
                forall |j: int| i <= j < v.len() ==> #[trigger] v[j] == values[j],
            decreases v.len() - i,
        {
            v.set(i, 1000);
            i += 1;
        }
        (v, n)
    } else if mutation_kind == 5 && values.len() >= 2 {
        // swap first and last elements
        let mut v = values;
        let last = v.len() - 1;
        let tmp_first = v[0];
        let tmp_last = v[last];
        v.set(0, tmp_last);
        v.set(last, tmp_first);
        (v, n)
    } else if mutation_kind == 6 {
        // nudge first element: if < 1000 increment, else decrement
        let mut v = values;
        if v[0] < 1000 {
            v.set(0, v[0] + 1);
        } else {
            v.set(0, v[0] - 1);
        }
        (v, n)
    } else if mutation_kind == 7 {
        // set last element to 500 (mid-range)
        let mut v = values;
        let last = v.len() - 1;
        v.set(last, 500);
        (v, n)
    } else {
        // fallback: identity
        (values, n)
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

fn random_values(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1000) as i32);
    }
    v
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
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, n: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?},{}", nums, n);
        if !seen.insert(key) { return; }
        let result = Solution::shuffle(nums.clone(), n);
        writeln!(out, "{}", json!({"input": {"nums": nums, "n": n}, "output": result})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![2, 5, 1, 3, 4, 7], 3),
        (vec![1, 2, 3, 4, 4, 3, 2, 1], 4),
        (vec![1, 1, 2, 2], 2),
    ];
    for (nums, n) in &examples {
        emit(nums.clone(), *n, &mut seen, &mut out, &mut emitted);
    }

    // Apply mutations to example inputs
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    for (nums, n) in &examples {
        for &mk in &mutation_kinds {
            let (result_nums, result_n) = generate_test_case(nums.clone(), *n, mk);
            emit(result_nums, result_n, &mut seen, &mut out, &mut emitted);
        }
    }

    // Diverse size classes with mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 1),       // minimum n=1
        (2, 5),       // tiny
        (6, 20),      // small
        (21, 100),    // medium
        (101, 300),   // large
        (301, 500),   // max
    ];

    for (lo, hi) in &size_classes {
        for &mk in &mutation_kinds {
            if emitted >= count { break; }
            let n = rng.gen_range_usize(*lo, *hi) as i32;
            let vals = random_values(&mut rng, 2 * n as usize);
            let (result_nums, result_n) = generate_test_case(vals, n, mk);
            emit(result_nums, result_n, &mut seen, &mut out, &mut emitted);
        }
    }

    // Boundary value arrays: all 1s, all 1000s, mixed boundaries
    for &n_val in &[1i32, 2, 10, 100, 500] {
        if emitted >= count { break; }
        let vals = vec![1i32; 2 * n_val as usize];
        emit(vals.clone(), n_val, &mut seen, &mut out, &mut emitted);
        let vals = vec![1000i32; 2 * n_val as usize];
        emit(vals.clone(), n_val, &mut seen, &mut out, &mut emitted);
    }

    // Fill remaining with random inputs + random mutations
    while emitted < count {
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(1, 1) as i32,
            1 => rng.gen_range_usize(2, 10) as i32,
            2 => rng.gen_range_usize(11, 100) as i32,
            3 => rng.gen_range_usize(101, 300) as i32,
            _ => rng.gen_range_usize(301, 500) as i32,
        };
        let vals = random_values(&mut rng, 2 * n as usize);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let (result_nums, result_n) = generate_test_case(vals, n, mk);
        emit(result_nums, result_n, &mut seen, &mut out, &mut emitted);
    }
}
