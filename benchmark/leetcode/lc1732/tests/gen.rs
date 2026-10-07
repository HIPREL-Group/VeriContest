use vstd::prelude::*;

verus! {

pub fn generate_test_case(gain: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= gain.len() <= 100,
        forall|i: int| 0 <= i < gain.len() ==> -100 <= #[trigger] gain[i] <= 100,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> -100 <= #[trigger] result[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        gain
    } else if mutation_kind == 1 {
        // set last element to 100 (max boundary)
        let mut g = gain;
        let last = g.len() - 1;
        g.set(last, 100);
        g
    } else if mutation_kind == 2 {
        // set last element to -100 (min boundary)
        let mut g = gain;
        let last = g.len() - 1;
        g.set(last, -100);
        g
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut g = gain;
        let last = g.len() - 1;
        g.set(last, 0);
        g
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut g = gain;
        let mut i: usize = 0;
        while i < g.len()
            invariant
                0 <= i <= g.len(),
                g.len() == gain.len(),
                1 <= g.len() <= 100,
                forall|j: int| 0 <= j < i ==> g[j] == 0i32,
                forall|j: int| i <= j < g.len() ==> g[j] == gain[j],
            decreases g.len() - i,
        {
            g.set(i, 0);
            i += 1;
        }
        g
    } else if mutation_kind == 5 && gain.len() < 100 {
        // grow by one element (push 0)
        let mut g = gain;
        g.push(0);
        g
    } else if mutation_kind == 6 && gain.len() > 1 {
        // shrink by one element (pop)
        let mut g = gain;
        g.pop();
        g
    } else if mutation_kind == 7 {
        // nudge last element up: if < 100, increment by 1
        let mut g = gain;
        let last = g.len() - 1;
        if g[last] < 100 {
            g.set(last, g[last] + 1);
        }
        g
    } else if mutation_kind == 8 {
        // nudge last element down: if > -100, decrement by 1
        let mut g = gain;
        let last = g.len() - 1;
        if g[last] > -100 {
            g.set(last, g[last] - 1);
        }
        g
    } else if mutation_kind == 9 {
        // negate last element
        let mut g = gain;
        let last = g.len() - 1;
        g.set(last, -g[last]);
        g
    } else if mutation_kind == 10 {
        // set all elements to 100 (max altitude climb)
        let mut g = gain;
        let mut i: usize = 0;
        while i < g.len()
            invariant
                0 <= i <= g.len(),
                g.len() == gain.len(),
                1 <= g.len() <= 100,
                forall|j: int| 0 <= j < i ==> g[j] == 100i32,
                forall|j: int| i <= j < g.len() ==> g[j] == gain[j],
            decreases g.len() - i,
        {
            g.set(i, 100);
            i += 1;
        }
        g
    } else if mutation_kind == 11 {
        // set all elements to -100 (max altitude descent)
        let mut g = gain;
        let mut i: usize = 0;
        while i < g.len()
            invariant
                0 <= i <= g.len(),
                g.len() == gain.len(),
                1 <= g.len() <= 100,
                forall|j: int| 0 <= j < i ==> g[j] == -100i32,
                forall|j: int| i <= j < g.len() ==> g[j] == gain[j],
            decreases g.len() - i,
        {
            g.set(i, -100);
            i += 1;
        }
        g
    } else {
        // fallback: identity
        gain
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

fn mutate(gain: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(gain, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_gain(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut gain = Vec::with_capacity(len);
    for _ in 0..len {
        gain.push(rng.gen_range_i64(-100, 100) as i32);
    }
    gain
}

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);

    let mut rng = Rng::new(seed);
    let mut generated = 0usize;

    // Example 1 from description.md
    {
        let gain = vec![-5, 1, 5, 0, -7];
        let result = Solution::largest_altitude(gain.clone());
        writeln!(out, "{}", json!({"input": {"gain": gain}, "output": result})).unwrap();
        generated += 1;
    }

    // Example 2 from description.md
    {
        let gain = vec![-4, -3, -2, -1, 4, 3, 2];
        let result = Solution::largest_altitude(gain.clone());
        writeln!(out, "{}", json!({"input": {"gain": gain}, "output": result})).unwrap();
        generated += 1;
    }

    // Edge case: single element
    {
        let gain = vec![0];
        let result = Solution::largest_altitude(gain.clone());
        writeln!(out, "{}", json!({"input": {"gain": gain}, "output": result})).unwrap();
        generated += 1;
    }

    // Generate remaining test cases with diverse sizes and mutations
    let num_mutations: u8 = 12;

    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 30),       // medium
            3 => rng.gen_range_usize(31, 70),       // large
            _ => rng.gen_range_usize(71, 100),      // max
        };

        let base_gain = random_gain(&mut rng, n);
        let mutation_kind = (rng.next_u64() % (num_mutations as u64 + 1)) as u8;
        let gain = mutate(base_gain, mutation_kind);
        let result = Solution::largest_altitude(gain.clone());
        writeln!(out, "{}", json!({"input": {"gain": gain}, "output": result})).unwrap();
        generated += 1;
    }
}
