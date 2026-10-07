use vstd::prelude::*;

verus! {

pub fn generate_test_case(colors: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        3 <= colors.len() <= 100,
        forall|i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 1,
    ensures
        3 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1,
{
    if mutation_kind == 0 {
        // identity
        colors
    } else if mutation_kind == 1 {
        // flip first element
        let mut c = colors;
        let v = if c[0] == 0 { 1i32 } else { 0i32 };
        c.set(0, v);
        c
    } else if mutation_kind == 2 {
        // flip last element
        let mut c = colors;
        let last = c.len() - 1;
        let v = if c[last] == 0 { 1i32 } else { 0i32 };
        c.set(last, v);
        c
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut c = colors;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == colors.len(),
                3 <= c.len() <= 100,
                forall|j: int| 0 <= j < i ==> #[trigger] c[j] == 0,
                forall|j: int| i <= j < c.len() ==> 0 <= #[trigger] c[j] <= 1,
            decreases c.len() - i,
        {
            c.set(i, 0);
            i += 1;
        }
        c
    } else if mutation_kind == 4 {
        // set all elements to 1
        let mut c = colors;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == colors.len(),
                3 <= c.len() <= 100,
                forall|j: int| 0 <= j < i ==> #[trigger] c[j] == 1,
                forall|j: int| i <= j < c.len() ==> 0 <= #[trigger] c[j] <= 1,
            decreases c.len() - i,
        {
            c.set(i, 1);
            i += 1;
        }
        c
    } else if mutation_kind == 5 {
        // make alternating pattern starting with 0: 0,1,0,1,...
        let mut c = colors;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == colors.len(),
                3 <= c.len() <= 100,
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] c[j] <= 1,
                forall|j: int| i <= j < c.len() ==> 0 <= #[trigger] c[j] <= 1,
            decreases c.len() - i,
        {
            if i % 2 == 0 {
                c.set(i, 0);
            } else {
                c.set(i, 1);
            }
            i += 1;
        }
        c
    } else if mutation_kind == 6 {
        // make alternating pattern starting with 1: 1,0,1,0,...
        let mut c = colors;
        let mut i: usize = 0;
        while i < c.len()
            invariant
                0 <= i <= c.len(),
                c.len() == colors.len(),
                3 <= c.len() <= 100,
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] c[j] <= 1,
                forall|j: int| i <= j < c.len() ==> 0 <= #[trigger] c[j] <= 1,
            decreases c.len() - i,
        {
            if i % 2 == 0 {
                c.set(i, 1);
            } else {
                c.set(i, 0);
            }
            i += 1;
        }
        c
    } else if mutation_kind == 7 && colors.len() < 100 {
        // grow by one element (push 0)
        let mut c = colors;
        c.push(0);
        c
    } else if mutation_kind == 8 && colors.len() < 100 {
        // grow by one element (push 1)
        let mut c = colors;
        c.push(1);
        c
    } else if mutation_kind == 9 && colors.len() > 3 {
        // shrink by one element (pop)
        let mut c = colors;
        c.pop();
        c
    } else if mutation_kind == 10 && colors.len() >= 2 {
        // swap first two elements
        let mut c = colors;
        let a = c[0];
        let b = c[1];
        c.set(0, b);
        c.set(1, a);
        c
    } else {
        // fallback: identity
        colors
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

include!("../code.rs");

fn mutate(colors: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(colors, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_colors(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut colors = Vec::with_capacity(len);
    for _ in 0..len {
        colors.push(rng.gen_range_usize(0, 1) as i32);
    }
    colors
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

    let mut emit = |colors: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", colors);
        if !seen.insert(key) {
            return;
        }
        let output = number_of_alternating_groups(colors.clone());
        writeln!(out, "{}", json!({"input": {"colors": colors}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 1, 1],
        vec![0, 1, 0, 0, 1],
    ];

    // Hand-crafted seeds covering edge cases
    let seeds: Vec<Vec<i32>> = vec![
        vec![0, 0, 0],
        vec![1, 1, 1],
        vec![0, 1, 0],
        vec![1, 0, 1],
        vec![0, 1, 0, 1],
        vec![1, 0, 1, 0],
        vec![0, 0, 1],
        vec![1, 0, 0],
        vec![0, 1, 1],
        vec![1, 1, 0],
        vec![0, 0, 0, 0, 0],
        vec![1, 1, 1, 1, 1],
        vec![0, 1, 0, 1, 0],
        vec![1, 0, 1, 0, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Emit examples first (identity mutation)
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds across size classes with random mutations
    for i in 0..200 {
        if count >= target {
            break;
        }
        let len = match i % 5 {
            0 => rng.gen_range_usize(3, 5),    // tiny
            1 => rng.gen_range_usize(3, 10),   // small
            2 => rng.gen_range_usize(11, 30),  // medium
            3 => rng.gen_range_usize(31, 70),  // large
            _ => rng.gen_range_usize(71, 100), // max
        };
        let s = random_colors(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let len = rng.gen_range_usize(3, 100);
        let s = random_colors(&mut rng, len);
        emit(mutate(s, 0), &mut seen, &mut out, &mut count);
    }
}
