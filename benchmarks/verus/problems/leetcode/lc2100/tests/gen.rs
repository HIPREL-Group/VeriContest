use vstd::prelude::*;

verus! {

pub fn generate_test_case(security: Vec<i32>, time: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= security.len() <= 100_000,
        0 <= time <= 100_000,
        forall|i: int| 0 <= i < security.len() ==> 0 <= #[trigger] security[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        0 <= result.1 <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (security, time)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut s = security;
        s.set(0, 0);
        (s, time)
    } else if mutation_kind == 2 {
        // set first element to 100_000 (max boundary)
        let mut s = security;
        s.set(0, 100_000);
        (s, time)
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut s = security;
        let last = s.len() - 1;
        s.set(last, 0);
        (s, time)
    } else if mutation_kind == 4 {
        // set last element to 100_000
        let mut s = security;
        let last = s.len() - 1;
        s.set(last, 100_000);
        (s, time)
    } else if mutation_kind == 5 {
        // set all elements to the first element's value (constant array)
        let val = security[0];
        let n = security.len();
        let mut s = security;
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                s.len() == n,
                1 <= n <= 100_000,
                0 <= val <= 100_000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] s[j] == val,
                forall|j: int| i as int <= j < n as int ==> #[trigger] s[j] == security[j],
            decreases n - i,
        {
            s.set(i, val);
            i += 1;
        }
        (s, time)
    } else if mutation_kind == 6 && time > 0 {
        // set time to 0 (every day is good)
        (security, 0)
    } else if mutation_kind == 7 && time < 100_000 {
        // nudge time up
        (security, time + 1)
    } else if mutation_kind == 8 && time > 0 {
        // nudge time down
        (security, time - 1)
    } else if mutation_kind == 9 && security.len() < 100_000 {
        // grow array by pushing element 0
        let mut s = security;
        s.push(0);
        (s, time)
    } else if mutation_kind == 10 && security.len() > 1 {
        // shrink array by popping last element
        let mut s = security;
        s.pop();
        (s, time)
    } else if mutation_kind == 11 {
        // nudge first element up if possible
        let mut s = security;
        if s[0] < 100_000 {
            s.set(0, s[0] + 1);
        }
        (s, time)
    } else if mutation_kind == 12 {
        // nudge first element down if possible
        let mut s = security;
        if s[0] > 0 {
            s.set(0, s[0] - 1);
        }
        (s, time)
    } else {
        // fallback: identity
        (security, time)
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

fn mutate(security: Vec<i32>, time: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(security, time, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_security(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 100_000) as i32);
    }
    v
}

fn non_increasing_then_non_decreasing(rng: &mut Rng, len: usize, valley: usize) -> Vec<i32> {
    // Build an array that is non-increasing up to valley, then non-decreasing after
    let mut v = Vec::with_capacity(len);
    let start_val = rng.gen_range_i64(50_000, 100_000) as i32;
    v.push(start_val);
    for i in 1..len {
        if i <= valley {
            // non-increasing part
            let prev = v[i - 1];
            let next = rng.gen_range_i64(0, prev as i64) as i32;
            v.push(next);
        } else {
            // non-decreasing part
            let prev = v[i - 1];
            let next = rng.gen_range_i64(prev as i64, 100_000) as i32;
            v.push(next);
        }
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2100);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |security: Vec<i32>, time: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", security, time);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::good_days_to_rob_bank(security.clone(), time);
        writeln!(out, "{}", json!({
            "input": {"security": security, "time": time},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![5, 3, 3, 3, 5, 6, 2], 2),
        (vec![1, 1, 1, 1, 1], 0),
        (vec![1, 2, 3, 4, 5, 6], 2),
    ];
    for (sec, t) in &examples {
        emit(sec.clone(), *t, &mut seen, &mut out, &mut count);
    }

    // Seed inputs: interesting patterns
    let seed_inputs: Vec<(Vec<i32>, i32)> = vec![
        // Single element
        (vec![0], 0),
        (vec![100_000], 0),
        // All same values
        (vec![5, 5, 5, 5, 5], 1),
        (vec![5, 5, 5, 5, 5], 2),
        // Strictly decreasing then increasing (V-shape)
        (vec![5, 4, 3, 2, 1, 2, 3, 4, 5], 4),
        (vec![5, 4, 3, 2, 1, 2, 3, 4, 5], 3),
        // Strictly increasing (no good days with time > 0)
        (vec![1, 2, 3, 4, 5], 1),
        // Strictly decreasing (no good days with time > 0)
        (vec![5, 4, 3, 2, 1], 1),
        // Two elements
        (vec![3, 3], 0),
        (vec![3, 3], 1),
        // time = 0 cases
        (vec![1, 2, 3], 0),
        // Large time relative to array
        (vec![1, 2, 3], 3),
        // Flat array
        (vec![7, 7, 7, 7, 7, 7, 7], 3),
    ];
    for (sec, t) in &seed_inputs {
        emit(sec.clone(), *t, &mut seen, &mut out, &mut count);
    }

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12];

    // Apply mutations to seed inputs
    for (sec, t) in examples.iter().chain(seed_inputs.iter()) {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let (s, ti) = mutate(sec.clone(), *t, mk);
            emit(s, ti, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 20),        // small
            2 => rng.gen_range_usize(21, 200),      // medium
            3 => rng.gen_range_usize(201, 1000),    // large
            _ => rng.gen_range_usize(1001, 5000),   // very large
        };

        let time_val: i32 = match rng.gen_range_usize(0, 4) {
            0 => 0,
            1 => rng.gen_range_i64(0, n as i64 / 2) as i32,
            2 => rng.gen_range_i64(0, 100_000) as i32,
            3 => n as i32,
            _ => rng.gen_range_i64(0, 10) as i32,
        };

        // Vary array structure
        let security = match rng.gen_range_usize(0, 3) {
            0 => random_security(&mut rng, n),
            1 => {
                let valley = if n > 0 { rng.gen_range_usize(0, n - 1) } else { 0 };
                non_increasing_then_non_decreasing(&mut rng, n, valley)
            }
            _ => {
                // constant array
                let val = rng.gen_range_i64(0, 100_000) as i32;
                vec![val; n]
            }
        };

        let mk = rng.gen_range_usize(0, 12) as u8;
        let (s, t) = mutate(security, time_val.min(100_000), mk);
        emit(s, t, &mut seen, &mut out, &mut count);
    }
}
