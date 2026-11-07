use vstd::prelude::*;

verus! {

pub fn generate_test_case(matchsticks: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= matchsticks.len() <= 15,
        forall|i: int| 0 <= i < matchsticks.len() ==> 1 <= #[trigger] matchsticks[i] <= 100_000_000,
    ensures
        1 <= result.len() <= 15,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000_000,
{
    if mutation_kind == 0 {
        // identity
        matchsticks
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum boundary)
        let mut m = matchsticks;
        let last = m.len() - 1;
        m.set(last, 1);
        m
    } else if mutation_kind == 2 {
        // set last element to 100_000_000 (maximum boundary)
        let mut m = matchsticks;
        let last = m.len() - 1;
        m.set(last, 100_000_000);
        m
    } else if mutation_kind == 3 {
        // set all elements to same value
        let mut m = matchsticks;
        let val = m[0];
        let mut i: usize = 0;
        while i < m.len()
            invariant
                0 <= i <= m.len(),
                m.len() == matchsticks.len(),
                1 <= m.len() <= 15,
                1 <= val <= 100_000_000,
                forall|j: int| 0 <= j < i ==> m[j] == val,
                forall|j: int| i <= j < m.len() ==> m[j] == matchsticks[j],
            decreases m.len() - i,
        {
            m.set(i, val);
            i += 1;
        }
        m
    } else if mutation_kind == 4 && matchsticks.len() < 15 {
        // grow by one element (push value 1)
        let mut m = matchsticks;
        m.push(1);
        m
    } else if mutation_kind == 5 && matchsticks.len() > 1 {
        // shrink by one element (pop)
        let mut m = matchsticks;
        m.pop();
        m
    } else if mutation_kind == 6 {
        // nudge last element up by 1 if possible
        let mut m = matchsticks;
        let last = m.len() - 1;
        if m[last] < 100_000_000 {
            m.set(last, m[last] + 1);
        }
        m
    } else if mutation_kind == 7 {
        // nudge last element down by 1 if possible
        let mut m = matchsticks;
        let last = m.len() - 1;
        if m[last] > 1 {
            m.set(last, m[last] - 1);
        }
        m
    } else if mutation_kind == 8 {
        // swap first and last elements
        let mut m = matchsticks;
        let last = m.len() - 1;
        let first_val = m[0];
        let last_val = m[last];
        m.set(0, last_val);
        m.set(last, first_val);
        m
    } else if mutation_kind == 9 {
        // halve last element (at least 1)
        let mut m = matchsticks;
        let last = m.len() - 1;
        let halved = m[last] / 2;
        if halved >= 1 {
            m.set(last, halved);
        }
        m
    } else {
        matchsticks // fallback
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

fn mutate(matchsticks: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(matchsticks, mutation_kind)
}

fn random_matchsticks(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100_000_000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(473);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |matchsticks: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal {
            return;
        }
        let key = format!("{:?}", matchsticks);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::makesquare(matchsticks.clone());
        writeln!(out, "{}", json!({"input": {"matchsticks": matchsticks}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 1, 2, 2, 2],       // true
        vec![3, 3, 3, 3, 4],       // false
    ];

    // Curated seeds: known interesting cases
    let curated: Vec<Vec<i32>> = vec![
        vec![1, 1, 1, 1],                             // perfect square, minimal
        vec![1, 2, 3, 4],                              // sum=10, not div by 4
        vec![5, 5, 5, 5, 5, 5, 5, 5],                 // 8 sticks, side=10
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1],     // 12 ones, side=3
        vec![100_000_000],                             // single large stick
        vec![1],                                       // single small stick
        vec![2, 2, 2, 2, 2, 2, 2, 2],                 // all equal, 8 sticks
        vec![4, 4, 4, 4],                              // minimal perfect square
        vec![1, 2, 3, 4, 5, 6, 7],                     // sum=28, 28%4=0, side=7
        vec![10, 10, 10, 10, 10, 10, 10, 10, 10, 10],  // 10 tens
        vec![3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],     // 12 threes, side=9
        vec![1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3],     // mixed
        vec![99_999_999, 99_999_999, 99_999_999, 99_999_999], // large perfect
        vec![1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1], // 15 ones
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit examples with all mutations
    for ex in &examples {
        for &mk in &mutation_kinds {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Emit curated seeds with all mutations
    for seed_vec in &curated {
        for &mk in &mutation_kinds {
            emit(mutate(seed_vec.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < goal {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(4, 6),       // small
            2 => rng.gen_range_usize(7, 10),      // medium
            3 => rng.gen_range_usize(11, 13),     // large
            _ => rng.gen_range_usize(14, 15),     // max
        };

        // Mix boundary values ~20% of the time
        let sticks = if count % 5 == 0 {
            let mut v = Vec::with_capacity(len);
            for _ in 0..len {
                let bv = match rng.gen_range_usize(0, 4) {
                    0 => 1i32,
                    1 => 100_000_000i32,
                    2 => 50_000_000i32,
                    3 => 2i32,
                    _ => 1000i32,
                };
                v.push(bv);
            }
            v
        } else {
            random_matchsticks(&mut rng, len)
        };

        let mk = rng.gen_range_usize(0, 9) as u8;
        emit(mutate(sticks, mk), &mut seen, &mut out, &mut count);
    }
}
