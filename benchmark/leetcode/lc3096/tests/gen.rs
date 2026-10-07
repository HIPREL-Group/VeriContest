use vstd::prelude::*;

verus! {

pub fn generate_test_case(possible: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        2 <= possible.len() <= 100000,
        forall|i: int| 0 <= i < possible.len() ==> (#[trigger] possible[i] == 0 || #[trigger] possible[i] == 1),
    ensures
        2 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> (#[trigger] result[i] == 0 || #[trigger] result[i] == 1),
{
    if mutation_kind == 0 {
        // identity
        possible
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = possible;
        d.set(0, 0);
        d
    } else if mutation_kind == 2 {
        // set first element to 1
        let mut d = possible;
        d.set(0, 1);
        d
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut d = possible;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 4 {
        // set last element to 1
        let mut d = possible;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut d = possible;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == possible.len(),
                2 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> (#[trigger] d[j] == 0 || #[trigger] d[j] == 1),
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        // set all elements to 1
        let mut d = possible;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == possible.len(),
                2 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> (#[trigger] d[j] == 0 || #[trigger] d[j] == 1),
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 7 && possible.len() < 100000 {
        // grow by one element (push 0)
        let mut d = possible;
        d.push(0);
        d
    } else if mutation_kind == 8 && possible.len() < 100000 {
        // grow by one element (push 1)
        let mut d = possible;
        d.push(1);
        d
    } else if mutation_kind == 9 && possible.len() > 2 {
        // shrink by one element (pop)
        let mut d = possible;
        d.pop();
        d
    } else if mutation_kind == 10 {
        // flip first element
        let mut d = possible;
        let v = if d[0] == 0 { 1i32 } else { 0i32 };
        d.set(0, v);
        d
    } else if mutation_kind == 11 {
        // flip last element
        let mut d = possible;
        let last = d.len() - 1;
        let v = if d[last] == 0 { 1i32 } else { 0i32 };
        d.set(last, v);
        d
    } else if mutation_kind == 12 && possible.len() >= 2 {
        // swap first two elements
        let mut d = possible;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        d
    } else {
        // fallback: identity
        possible
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(possible: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(possible, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_binary_vec(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_usize(0, 1) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3096);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |possible: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", possible);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_levels(possible.clone());
        writeln!(out, "{}", json!({"input": {"possible": possible}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 0, 1, 0],
        vec![1, 1, 1, 1, 1],
        vec![0, 0],
    ];

    let mutation_kinds: Vec<u8> = (0..=12).collect();

    // Apply every mutation to every example
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Curated seed inputs for diversity
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 1],
        vec![1, 0],
        vec![1, 1],
        vec![0, 0],
        vec![0, 0, 0, 0],
        vec![1, 1, 1, 1],
        vec![0, 1, 0, 1, 0, 1],
        vec![1, 0, 1, 0, 1, 0],
        vec![1, 1, 0, 0],
        vec![0, 0, 1, 1],
    ];

    for seed_vec in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(seed_vec.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs across diverse size classes
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 5),        // tiny
        (6, 20),       // small
        (21, 100),     // medium
        (101, 1000),   // large
        (1001, 10000), // xlarge
    ];

    for &(lo, hi) in &size_classes {
        for _ in 0..10 {
            if count >= target { break; }
            let len = rng.gen_range_usize(lo, hi);
            let v = random_binary_vec(&mut rng, len);
            let mk = rng.gen_range_usize(0, 12) as u8;
            let result = mutate(v, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random
    while count < target {
        let len = rng.gen_range_usize(2, 1000);
        let v = random_binary_vec(&mut rng, len);
        emit(mutate(v, 0), &mut seen, &mut out, &mut count);
    }
}
