use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    heights: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, usize))
    requires
        2 <= heights.len() <= 100,
        forall|i: int| 0 <= i < heights.len() as int ==> 1 <= #[trigger] heights[i] as int <= 1000,
    ensures
        2 <= result.1 <= 100,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() as int ==> 1 <= #[trigger] result.0[i] as int <= 1000,
{
    let n = heights.len();
    if mutation_kind == 0 {
        // identity
        (heights, n)
    } else if mutation_kind == 1 {
        // set last element to 1 (boundary low)
        let mut h = heights;
        let last = h.len() - 1;
        h.set(last, 1);
        (h, n)
    } else if mutation_kind == 2 {
        // set last element to 1000 (boundary high)
        let mut h = heights;
        let last = h.len() - 1;
        h.set(last, 1000);
        (h, n)
    } else if mutation_kind == 3 {
        // set first element to 1
        let mut h = heights;
        h.set(0, 1);
        (h, n)
    } else if mutation_kind == 4 {
        // set first element to 1000
        let mut h = heights;
        h.set(0, 1000);
        (h, n)
    } else if mutation_kind == 5 && heights.len() < 100 {
        // grow by one element (push 1)
        let mut h = heights;
        h.push(1);
        let new_n = h.len();
        (h, new_n)
    } else if mutation_kind == 6 && heights.len() > 2 {
        // shrink by one element (pop)
        let mut h = heights;
        h.pop();
        let new_n = h.len();
        (h, new_n)
    } else if mutation_kind == 7 {
        // nudge last element up (if < 1000)
        let mut h = heights;
        let last = h.len() - 1;
        if h[last] < 1000 {
            h.set(last, h[last] + 1);
        }
        (h, n)
    } else if mutation_kind == 8 {
        // nudge last element down (if > 1)
        let mut h = heights;
        let last = h.len() - 1;
        if h[last] > 1 {
            h.set(last, h[last] - 1);
        }
        (h, n)
    } else if mutation_kind == 9 {
        // set all elements to same value (500)
        let mut h = heights;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == n,
                2 <= n <= 100,
                forall|j: int| 0 <= j < i ==> h[j] == 500i32,
                forall|j: int| i <= j < h.len() as int ==> 1 <= #[trigger] h[j] as int <= 1000,
            decreases h.len() - i,
        {
            h.set(i, 500);
            i += 1;
        }
        (h, n)
    } else if mutation_kind == 10 {
        // set all elements to 1
        let mut h = heights;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == n,
                2 <= n <= 100,
                forall|j: int| 0 <= j < i ==> h[j] == 1i32,
                forall|j: int| i <= j < h.len() as int ==> 1 <= #[trigger] h[j] as int <= 1000,
            decreases h.len() - i,
        {
            h.set(i, 1);
            i += 1;
        }
        (h, n)
    } else if mutation_kind == 11 && heights.len() >= 3 {
        // swap first two elements
        let mut h = heights;
        let tmp = h[0];
        h.set(0, h[1]);
        h.set(1, tmp);
        (h, n)
    } else {
        // fallback: identity
        (heights, n)
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

fn make_heights(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut h = Vec::new();
    for _ in 0..n {
        h.push(rng.gen_range_i64(1, 1000) as i32);
    }
    h
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

    let num_mutations: u8 = 12;
    let mut generated: usize = 0;

    // Example 1 from description.md: 5 soldiers, heights [10, 12, 13, 15, 10]
    {
        let heights = vec![10, 12, 13, 15, 10];
        let n = heights.len();
        let (ri, rj) = Solution::min_adjacent_pair(heights.clone(), n);
        writeln!(out, "{}", json!({"input": {"heights": heights, "n": n}, "output": [ri, rj]})).unwrap();
        generated += 1;
    }

    // Example 2 from description.md: 4 soldiers, heights [10, 20, 30, 40]
    {
        let heights = vec![10, 20, 30, 40];
        let n = heights.len();
        let (ri, rj) = Solution::min_adjacent_pair(heights.clone(), n);
        writeln!(out, "{}", json!({"input": {"heights": heights, "n": n}, "output": [ri, rj]})).unwrap();
        generated += 1;
    }

    // Generate remaining test cases
    while generated < count {
        // Size classes
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 100),    // large
            _ => 100,                              // max
        };

        let heights = make_heights(&mut rng, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;
        let (h, nn) = generate_test_case(heights, mk);
        let (ri, rj) = Solution::min_adjacent_pair(h.clone(), nn);
        writeln!(out, "{}", json!({"input": {"heights": h, "n": nn}, "output": [ri, rj]})).unwrap();
        generated += 1;
    }
}
