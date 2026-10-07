use vstd::prelude::*;

verus! {

pub fn generate_test_case(hours: Vec<i32>, target: i32, mutation_kind: u8) -> (result: (Vec<i32>, i32))
    requires
        1 <= hours.len() <= 50,
        0 <= target <= 100_000,
        forall|i: int| 0 <= i < hours.len() ==> 0 <= #[trigger] hours[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 50,
        0 <= result.1 <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (hours, target)
    } else if mutation_kind == 1 {
        // set all elements to target (all meet target)
        let t = target;
        let mut h = hours;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == hours.len(),
                1 <= h.len() <= 50,
                0 <= t <= 100_000,
                forall|j: int| 0 <= j < i ==> #[trigger] h[j] == t,
                forall|j: int| i <= j < h.len() ==> #[trigger] h[j] == hours[j],
            decreases h.len() - i,
        {
            h.set(i, t);
            i += 1;
        }
        (h, t)
    } else if mutation_kind == 2 {
        // set all elements to 0 (none meet target unless target == 0)
        let mut h = hours;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == hours.len(),
                1 <= h.len() <= 50,
                forall|j: int| 0 <= j < i ==> #[trigger] h[j] == 0i32,
                forall|j: int| i <= j < h.len() ==> #[trigger] h[j] == hours[j],
            decreases h.len() - i,
        {
            h.set(i, 0);
            i += 1;
        }
        (h, target)
    } else if mutation_kind == 3 && hours.len() < 50 {
        // grow: push one element (0)
        let mut h = hours;
        h.push(0);
        (h, target)
    } else if mutation_kind == 4 && hours.len() > 1 {
        // shrink: pop one element
        let mut h = hours;
        h.pop();
        (h, target)
    } else if mutation_kind == 5 {
        // set first element to 100_000 (max boundary)
        let mut h = hours;
        h.set(0, 100_000);
        (h, target)
    } else if mutation_kind == 6 {
        // nudge first element up (if < 100_000)
        let mut h = hours;
        if h[0] < 100_000 {
            h.set(0, h[0] + 1);
        }
        (h, target)
    } else if mutation_kind == 7 {
        // nudge first element down (if > 0)
        let mut h = hours;
        if h[0] > 0 {
            h.set(0, h[0] - 1);
        }
        (h, target)
    } else if mutation_kind == 8 {
        // set target to 0 (all employees meet target)
        (hours, 0)
    } else if mutation_kind == 9 {
        // set target to 100_000 (max boundary)
        (hours, 100_000)
    } else if mutation_kind == 10 {
        // swap first and last elements
        let mut h = hours;
        let last = h.len() - 1;
        let first_val = h[0];
        let last_val = h[last];
        h.set(0, last_val);
        h.set(last, first_val);
        (h, target)
    } else {
        // fallback: identity
        (hours, target)
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

fn mutate(hours: Vec<i32>, target: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(hours, target, mutation_kind)
}

fn random_hours(rng: &mut Rng, len: usize, val_lo: i64, val_hi: i64) -> Vec<i32> {
    let mut hours = Vec::with_capacity(len);
    for _ in 0..len {
        hours.push(rng.gen_range_i64(val_lo, val_hi) as i32);
    }
    hours
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let num_mutations: u8 = 11;
    let mut generated: usize = 0;

    // Example 1 from description: hours = [0,1,2,3,4], target = 2 -> 3
    {
        let hours = vec![0, 1, 2, 3, 4];
        let target = 2;
        let result = Solution::number_of_employees_who_met_target(hours.clone(), target);
        writeln!(out, "{}", json!({"input": {"hours": hours, "target": target}, "output": result})).unwrap();
        generated += 1;
    }

    // Example 2 from description: hours = [5,1,4,2,2], target = 6 -> 0
    {
        let hours = vec![5, 1, 4, 2, 2];
        let target = 6;
        let result = Solution::number_of_employees_who_met_target(hours.clone(), target);
        writeln!(out, "{}", json!({"input": {"hours": hours, "target": target}, "output": result})).unwrap();
        generated += 1;
    }

    while generated < count {
        // Size classes for array length
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 3),      // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 25),     // medium
            3 => rng.gen_range_usize(26, 40),     // large
            _ => rng.gen_range_usize(41, 50),     // max
        };

        // Value range for hours elements
        let (val_lo, val_hi): (i64, i64) = match generated % 5 {
            0 => (0, 10),          // small values
            1 => (0, 1000),        // moderate values
            2 => (0, 50_000),      // medium values
            3 => (0, 100_000),     // full range
            _ => (0, 100_000),     // full range
        };

        let hours = random_hours(&mut rng, n, val_lo, val_hi);

        // Target with boundary mixing
        let target: i32 = if generated % 5 == 0 {
            *[0i32, 1, 100_000, 50_000].iter().nth(rng.gen_range_usize(0, 3)).unwrap()
        } else {
            rng.gen_range_i64(0, 100_000) as i32
        };

        let mutation_kind = (generated % num_mutations as usize) as u8;
        let (h, t) = mutate(hours, target, mutation_kind);

        let result = Solution::number_of_employees_who_met_target(h.clone(), t);
        writeln!(out, "{}", json!({"input": {"hours": h, "target": t}, "output": result})).unwrap();
        generated += 1;
    }
}
