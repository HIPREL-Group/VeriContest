use vstd::prelude::*;

verus! {

pub fn generate_test_case(s: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        s.len() >= 1,
        forall|i: int| 0 <= i < s.len() ==> (#[trigger] s@[i] == 0 || s@[i] == 1 || s@[i] == 2),
    ensures
        result.len() >= 1,
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] result@[i] == 0 || result@[i] == 1 || result@[i] == 2),
{
    if mutation_kind == 0 {
        // identity
        s
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = s;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut d = s;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 3 {
        // set last element to 2
        let mut d = s;
        let last = d.len() - 1;
        d.set(last, 2);
        d
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut d = s;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == s.len(),
                s.len() >= 1,
                forall|j: int| 0 <= j < i as int ==> d@[j] == 0i64,
                forall|j: int| i as int <= j < d.len() ==> d@[j] == s@[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut d = s;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == s.len(),
                s.len() >= 1,
                forall|j: int| 0 <= j < i as int ==> d@[j] == 1i64,
                forall|j: int| i as int <= j < d.len() ==> d@[j] == s@[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set all elements to 2
        let mut d = s;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == s.len(),
                s.len() >= 1,
                forall|j: int| 0 <= j < i as int ==> d@[j] == 2i64,
                forall|j: int| i as int <= j < d.len() ==> d@[j] == s@[j],
            decreases d.len() - i,
        {
            d.set(i, 2);
            i += 1;
        }
        d
    } else if mutation_kind == 7 {
        // set first element to 0
        let mut d = s;
        d.set(0, 0);
        d
    } else if mutation_kind == 8 {
        // set first element to 1
        let mut d = s;
        d.set(0, 1);
        d
    } else if mutation_kind == 9 {
        // set first element to 2
        let mut d = s;
        d.set(0, 2);
        d
    } else if mutation_kind == 10 && s.len() < 300_000 {
        // grow: append a 0
        let mut d = s;
        d.push(0);
        d
    } else if mutation_kind == 11 && s.len() < 300_000 {
        // grow: append a 2
        let mut d = s;
        d.push(2);
        d
    } else if mutation_kind == 12 && s.len() > 1 {
        // shrink: pop last element
        let mut d = s;
        d.pop();
        d
    } else {
        // fallback: identity
        s
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_input(rng: &mut Rng, len: usize) -> Vec<i64> {
    let mut s = Vec::with_capacity(len);
    for _ in 0..len {
        s.push(rng.gen_range_i64(0, 2));
    }
    s
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |s: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}", s);
        if !seen.insert(key) { return; }
        let output = Solution::best_binary_string(s.clone());
        writeln!(out, "{}", json!({"input": {"s": s}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md (0=0, 1=1, 2=?)
    let examples: Vec<Vec<i64>> = vec![
        vec![2, 2, 0, 1, 2],       // ??01?
        vec![1, 0, 1, 0, 0],       // 10100 (no ?s)
        vec![1, 2, 2, 1, 0, 1],    // 1??101
        vec![2, 0, 2, 1, 2, 1, 0, 2, 1, 0], // ?0?1?10?10 (approx)
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed inputs for systematic mutations
    let seeds: Vec<Vec<i64>> = vec![
        vec![0],
        vec![1],
        vec![2],
        vec![0, 1],
        vec![1, 0],
        vec![2, 2],
        vec![0, 2, 1],
        vec![2, 0, 2, 1],
        vec![1, 1, 1, 1, 1],
        vec![0, 0, 0, 0, 0],
        vec![2, 2, 2, 2, 2],
        vec![0, 1, 2, 0, 1, 2],
        vec![1, 0, 1, 0, 1, 0, 1, 0],
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    for seed_input in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(seed_input.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(4, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 1000),  // very large
        };
        let s = random_input(&mut rng, len);
        let mk = rng.gen_range_usize(0, 12) as u8;
        let result = generate_test_case(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
