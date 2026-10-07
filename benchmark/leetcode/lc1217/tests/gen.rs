use vstd::prelude::*;

verus! {

pub fn generate_test_case(position: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= position.len() <= 100,
        forall|i: int| 0 <= i < position.len() ==> 1 <= #[trigger] position[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        position
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum value)
        let mut p = position;
        let last = p.len() - 1;
        p.set(last, 1);
        p
    } else if mutation_kind == 2 {
        // set last element to 1_000_000_000 (maximum value)
        let mut p = position;
        let last = p.len() - 1;
        p.set(last, 1_000_000_000);
        p
    } else if mutation_kind == 3 {
        // set all elements to 1 (all same, even parity)
        let mut p = position;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == position.len(),
                1 <= p.len() <= 100,
                forall|j: int| 0 <= j < i ==> p[j] == 1i32,
                forall|j: int| i <= j < p.len() ==> p[j] == position[j],
            decreases p.len() - i,
        {
            p.set(i, 1);
            i += 1;
        }
        p
    } else if mutation_kind == 4 {
        // set all elements to 2 (all same, odd parity)
        let mut p = position;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == position.len(),
                1 <= p.len() <= 100,
                forall|j: int| 0 <= j < i ==> p[j] == 2i32,
                forall|j: int| i <= j < p.len() ==> p[j] == position[j],
            decreases p.len() - i,
        {
            p.set(i, 2);
            i += 1;
        }
        p
    } else if mutation_kind == 5 && position.len() < 100 {
        // grow: append element 1
        let mut p = position;
        p.push(1);
        p
    } else if mutation_kind == 6 && position.len() > 1 {
        // shrink: remove last element
        let mut p = position;
        p.pop();
        p
    } else if mutation_kind == 7 {
        // nudge last element: if < 1_000_000_000, increment by 1
        let mut p = position;
        let last = p.len() - 1;
        if p[last] < 1_000_000_000 {
            p.set(last, p[last] + 1);
        }
        p
    } else if mutation_kind == 8 {
        // nudge last element down: if > 1, decrement by 1
        let mut p = position;
        let last = p.len() - 1;
        if p[last] > 1 {
            p.set(last, p[last] - 1);
        }
        p
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut p = position;
        let last = p.len() - 1;
        let first_val = p[0];
        let last_val = p[last];
        p.set(0, last_val);
        p.set(last, first_val);
        p
    } else {
        position // fallback
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

fn random_position(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut pos = Vec::with_capacity(len);
    for _ in 0..len {
        pos.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    pos
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |position: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= goal { return; }
        let key = format!("{:?}", position);
        if !seen.insert(key) { return; }
        let output = Solution::min_cost_to_move_chips(position.clone());
        writeln!(out, "{}", json!({"input": {"position": position}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3],
        vec![2, 2, 2, 3, 3],
        vec![1, 1_000_000_000],
    ];

    // Interesting seed inputs
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![1_000_000_000],
        vec![1, 1],
        vec![2, 2],
        vec![1, 2],
        vec![1, 1, 1, 1, 1],
        vec![2, 4, 6, 8, 10],
        vec![1, 3, 5, 7, 9],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![999_999_999, 1_000_000_000],
        vec![1, 2, 1, 2, 1],
        vec![3, 3, 3],
        vec![4, 4, 4, 4],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Emit examples first (identity mutation)
    for ex in &examples {
        emit(generate_test_case(ex.clone(), 0), &mut seen, &mut out, &mut count);
    }

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = generate_test_case(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    // Random seeds with diverse sizes and random mutations
    while count < goal {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),      // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };
        let s = random_position(&mut rng, len);
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = generate_test_case(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
