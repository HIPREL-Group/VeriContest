use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        values
    } else if mutation_kind == 1 {
        // set first element to min boundary (1)
        let mut d = values;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to max boundary (100000)
        let mut d = values;
        d.set(0, 100000);
        d
    } else if mutation_kind == 3 {
        // set last element to min boundary (1)
        let mut d = values;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 4 {
        // set last element to max boundary (100000)
        let mut d = values;
        let last = d.len() - 1;
        d.set(last, 100000);
        d
    } else if mutation_kind == 5 && values.len() < 100000 {
        // grow: append first element value
        let mut d = values;
        let v = d[0];
        d.push(v);
        d
    } else if mutation_kind == 6 && values.len() > 1 {
        // shrink: remove last element
        let mut d = values;
        d.pop();
        d
    } else if mutation_kind == 7 && values.len() >= 2 {
        // swap first and last elements
        let mut d = values;
        let last = d.len() - 1;
        let a = d[0];
        let b = d[last];
        d.set(0, b);
        d.set(last, a);
        d
    } else if mutation_kind == 8 {
        // set all elements to values[0] (constant array)
        let val = values[0];
        let len = values.len();
        let mut d: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < len
            invariant
                0 <= j <= len,
                d.len() == j as int,
                1 <= val <= 100000,
                1 <= len <= 100000,
                forall|k: int| 0 <= k < d.len() ==> #[trigger] d[k] == val,
                forall|k: int| 0 <= k < d.len() ==> 1 <= #[trigger] d[k] <= 100000,
            decreases len - j,
        {
            d.push(val);
            j += 1;
        }
        d
    } else if mutation_kind == 9 {
        // nudge first element up (if < 100000)
        let mut d = values;
        if d[0] < 100000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 10 {
        // nudge first element down (if > 1)
        let mut d = values;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 11 {
        // nudge last element up (if < 100000)
        let mut d = values;
        let last = d.len() - 1;
        if d[last] < 100000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 12 {
        // nudge last element down (if > 1)
        let mut d = values;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else {
        // fallback: identity
        values
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

fn mutate(values: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(values, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_distance(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(335);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |distance: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", distance);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::is_self_crossing(distance.clone());
        writeln!(out, "{}", json!({"input": {"distance": distance}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 1, 1, 2],
        vec![1, 2, 3, 4],
        vec![1, 1, 1, 2, 1],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds covering crossing cases
    let hand_seeds: Vec<Vec<i32>> = vec![
        vec![1, 1, 1, 1],
        vec![3, 3, 3, 3],
        vec![10, 5, 10, 5],
        vec![1, 1, 2, 1, 1],
        vec![1, 2, 3, 2, 2],
        vec![1, 1, 2, 2, 1, 1],
        vec![1, 2, 3, 4, 5, 6, 7, 8],
        vec![1, 2, 3, 4, 5],
        vec![1],
        vec![1, 2],
        vec![1, 2, 3],
        vec![5, 5, 5, 5, 5],
        vec![100000, 100000, 100000, 100000],
        vec![1, 1, 1, 1, 1, 1],
        vec![100000, 1, 100000, 1],
        vec![1, 100000, 1, 100000],
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    for seed_arr in examples.iter().chain(hand_seeds.iter()) {
        for mk_ref in &mutation_kinds {
            let mk = *mk_ref;
            emit(mutate(seed_arr.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    while count < target_count {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let seed_arr = random_distance(&mut rng, n);
        let mk = rng.gen_range_usize(0, 12) as u8;
        emit(mutate(seed_arr, mk), &mut seen, &mut out, &mut count);
    }
}
