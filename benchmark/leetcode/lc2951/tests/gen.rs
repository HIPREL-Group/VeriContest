use vstd::prelude::*;

verus! {

pub fn generate_test_case(mountain: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= mountain.len() <= 100,
        forall|i: int| 0 <= i < mountain.len() ==> 1 <= #[trigger] mountain[i] <= 100,
    ensures
        result.len() <= 2147483647usize,
{
    if mutation_kind == 0 {
        // identity
        mountain
    } else if mutation_kind == 1 && mountain.len() >= 3 {
        // create a peak at index 1: set mountain[1] higher than neighbors
        let mut m = mountain;
        m.set(1, 100);
        if m[0] >= 100 {
            m.set(0, 1);
        }
        if m.len() > 2 && m[2] >= 100 {
            m.set(2, 1);
        }
        m
    } else if mutation_kind == 2 {
        // flatten: set all elements to the same value (no peaks)
        let mut m = mountain;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == mountain.len(),
                3 <= m.len() <= 100,
                forall|j: int| 0 <= j < i ==> m[j] == 50,
                forall|j: int| i <= j < m.len() ==> m[j] == mountain[j],
            decreases m.len() - i,
        {
            m.set(i, 50);
            i += 1;
        }
        m
    } else if mutation_kind == 3 {
        // strictly increasing: set m[i] = (i+1) as i32, guaranteed no peaks
        let mut m = mountain;
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == mountain.len(),
                3 <= m.len() <= 100,
                forall|j: int| 0 <= j < i ==> m[j] == (j + 1) as i32,
                forall|j: int| i <= j < m.len() ==> m[j] == mountain[j],
            decreases m.len() - i,
        {
            m.set(i, (i + 1) as i32);
            i += 1;
        }
        m
    } else if mutation_kind == 4 {
        // strictly decreasing: set m[i] = (n - i) as i32, guaranteed no peaks
        let mut m = mountain;
        let n = m.len();
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == mountain.len(),
                m.len() == n,
                3 <= m.len() <= 100,
                forall|j: int| 0 <= j < i ==> m[j] == (n - j) as i32,
                forall|j: int| i <= j < m.len() ==> m[j] == mountain[j],
            decreases m.len() - i,
        {
            m.set(i, (n - i) as i32);
            i += 1;
        }
        m
    } else if mutation_kind == 5 && mountain.len() >= 3 {
        // create peak at last valid position: set mountain[n-2] to 100, neighbors to 1
        let mut m = mountain;
        let last_inner = m.len() - 2;
        m.set(last_inner, 100);
        if m[last_inner - 1] >= 100 {
            m.set(last_inner - 1, 1);
        }
        let last = m.len() - 1;
        if m[last] >= 100 {
            m.set(last, 1);
        }
        m
    } else if mutation_kind == 6 && mountain.len() < 100 {
        // grow: append element
        let mut m = mountain;
        m.push(50);
        m
    } else if mutation_kind == 7 && mountain.len() > 3 {
        // shrink: remove last element
        let mut m = mountain;
        m.pop();
        m
    } else if mutation_kind == 8 {
        // set first element to 1
        let mut m = mountain;
        m.set(0, 1);
        m
    } else if mutation_kind == 9 {
        // set last element to 1
        let mut m = mountain;
        let last = m.len() - 1;
        m.set(last, 1);
        m
    } else {
        // fallback: identity
        mountain
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

fn make_mountain(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range_i64(1, 100) as i32).collect()
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

    // Example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 4, 4],
        vec![1, 4, 3, 8, 5],
    ];

    for mountain in &examples {
        let result = Solution::find_peaks(mountain.clone());
        writeln!(out, "{}", json!({
            "input": {"mountain": mountain},
            "output": result
        })).unwrap();
    }

    let num_random = if count > examples.len() { count - examples.len() } else { 0 };

    for i in 0..num_random {
        // Size classes
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(3, 5),     // tiny
            1 => rng.gen_range_usize(3, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };

        let mountain = make_mountain(&mut rng, n);
        let mutation_kind = (i % 10) as u8;
        let mutated = generate_test_case(mountain, mutation_kind);
        let result = Solution::find_peaks(mutated.clone());

        writeln!(out, "{}", json!({
            "input": {"mountain": mutated},
            "output": result
        })).unwrap();
    }
}
