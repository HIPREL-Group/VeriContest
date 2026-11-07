use vstd::prelude::*;

verus! {

/// Build a valid bills array of length `len` where every element is 5, 10, or 20.
/// `choices` supplies raw material: for each position we pick 5, 10, or 20 based
/// on `choices[i] % 3`. `mutation_kind` selects structural variants.
pub fn generate_test_case(choices: Vec<u8>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= choices.len() <= 100_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> result[i] == 5 || result[i] == 10 || result[i] == 20,
{
    let len = choices.len();

    if mutation_kind == 0 {
        // Map choices to bills via modulo
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let mut idx: usize = 0;
        while idx < len
            invariant
                0 <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 5 || bills[j] == 10 || bills[j] == 20,
            decreases len - idx,
        {
            let c = choices[idx] % 3;
            if c == 0 {
                bills.push(5);
            } else if c == 1 {
                bills.push(10);
            } else {
                bills.push(20);
            }
            idx = idx + 1;
        }
        bills
    } else if mutation_kind == 1 {
        // All 5s
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let mut idx: usize = 0;
        while idx < len
            invariant
                0 <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 5,
            decreases len - idx,
        {
            bills.push(5);
            idx = idx + 1;
        }
        bills
    } else if mutation_kind == 2 {
        // All 10s
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let mut idx: usize = 0;
        while idx < len
            invariant
                0 <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 10,
            decreases len - idx,
        {
            bills.push(10);
            idx = idx + 1;
        }
        bills
    } else if mutation_kind == 3 {
        // All 20s
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let mut idx: usize = 0;
        while idx < len
            invariant
                0 <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 20,
            decreases len - idx,
        {
            bills.push(20);
            idx = idx + 1;
        }
        bills
    } else if mutation_kind == 4 {
        // First half 5s, second half from choices
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let half = len / 2;
        let mut idx: usize = 0;
        while idx < half
            invariant
                0 <= idx <= half,
                half <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 5,
            decreases half - idx,
        {
            bills.push(5);
            idx = idx + 1;
        }
        while idx < len
            invariant
                half <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < half as int ==> bills[j] == 5,
                forall|j: int| half as int <= j < idx as int ==> bills[j] == 5 || bills[j] == 10 || bills[j] == 20,
            decreases len - idx,
        {
            let c = choices[idx] % 3;
            if c == 0 {
                bills.push(5);
            } else if c == 1 {
                bills.push(10);
            } else {
                bills.push(20);
            }
            idx = idx + 1;
        }
        bills
    } else if mutation_kind == 5 && len >= 2 {
        // Alternating 5 and 10
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let mut idx: usize = 0;
        while idx < len
            invariant
                0 <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                len >= 2,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 5 || bills[j] == 10,
            decreases len - idx,
        {
            if idx % 2 == 0 {
                bills.push(5);
            } else {
                bills.push(10);
            }
            idx = idx + 1;
        }
        bills
    } else if mutation_kind == 6 {
        // Single element from first choice
        let mut bills: Vec<i32> = Vec::new();
        let c = choices[0usize] % 3;
        if c == 0 {
            bills.push(5);
        } else if c == 1 {
            bills.push(10);
        } else {
            bills.push(20);
        }
        bills
    } else if mutation_kind == 7 {
        // Repeating pattern: 5, 5, 10 (classic change-making pattern)
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let mut idx: usize = 0;
        while idx < len
            invariant
                0 <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 5 || bills[j] == 10,
            decreases len - idx,
        {
            if idx % 3 < 2 {
                bills.push(5);
            } else {
                bills.push(10);
            }
            idx = idx + 1;
        }
        bills
    } else {
        // Fallback: map choices like mutation 0
        let mut bills: Vec<i32> = Vec::with_capacity(len);
        let mut idx: usize = 0;
        while idx < len
            invariant
                0 <= idx <= len,
                len == choices.len(),
                bills.len() == idx,
                1 <= len <= 100_000,
                forall|j: int| 0 <= j < idx as int ==> bills[j] == 5 || bills[j] == 10 || bills[j] == 20,
            decreases len - idx,
        {
            let c = choices[idx] % 3;
            if c == 0 {
                bills.push(5);
            } else if c == 1 {
                bills.push(10);
            } else {
                bills.push(20);
            }
            idx = idx + 1;
        }
        bills
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() & 0xFF) as u8
    }
}

struct Solution;
include!("../code.rs");

fn make_choices(rng: &mut Rng, len: usize) -> Vec<u8> {
    let mut choices = Vec::with_capacity(len);
    for _ in 0..len {
        choices.push(rng.gen_u8());
    }
    choices
}

fn mutate(choices: Vec<u8>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(choices, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(860);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |bills: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", bills);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::lemonade_change(bills.clone());
        writeln!(out, "{}", json!({"input": {"bills": bills}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let example_seeds: Vec<Vec<i32>> = vec![
        vec![5, 5, 5, 10, 20],   // Example 1: true
        vec![5, 5, 10, 10, 20],  // Example 2: false
    ];
    for ex in example_seeds {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Hand-crafted edge cases
    let edge_cases: Vec<Vec<i32>> = vec![
        vec![5],                          // single 5
        vec![10],                         // single 10 (no change)
        vec![20],                         // single 20 (no change)
        vec![5, 10],                      // basic change
        vec![5, 20],                      // can't make change for 20 with only one 5
        vec![5, 5, 10],                   // basic change for 10
        vec![5, 5, 5, 20],               // change for 20 with three 5s
        vec![5, 5, 10, 20],              // change for 20 with 10+5
        vec![5, 10, 10],                  // second 10 fails
        vec![5, 5, 5, 5, 10, 10, 20],    // mixed success
    ];
    for ec in edge_cases {
        emit(ec, &mut seen, &mut out, &mut count);
    }

    // Deterministic mutations × size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];
    let size_classes: Vec<usize> = vec![1, 2, 3, 5, 10, 20, 50, 100, 500, 1000];

    for &sz in &size_classes {
        for &mk in &mutation_kinds {
            if count >= target_count { break; }
            let choices = make_choices(&mut rng, sz);
            let bills = mutate(choices, mk);
            emit(bills, &mut seen, &mut out, &mut count);
        }
    }

    // Random cases with varied sizes and mutations
    while count < target_count {
        let len = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 20),       // small
            2 => rng.gen_range_usize(21, 200),     // medium
            3 => rng.gen_range_usize(201, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let mk = rng.gen_u8() % 9; // 0..8
        let choices = make_choices(&mut rng, len);
        let bills = mutate(choices, mk);
        emit(bills, &mut seen, &mut out, &mut count);
    }
}
