use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    alice_values: Vec<i32>,
    bob_values: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        alice_values.len() == bob_values.len(),
        1 <= alice_values.len() <= 100_000,
        forall|i: int| 0 <= i < alice_values.len() ==> 1 <= #[trigger] alice_values[i] <= 100,
        forall|i: int| 0 <= i < bob_values.len() ==> 1 <= #[trigger] bob_values[i] <= 100,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (alice_values, bob_values)
    } else if mutation_kind == 1 {
        // swap: return bob as alice and alice as bob
        (bob_values, alice_values)
    } else if mutation_kind == 2 {
        // set first alice value to 1 (min boundary)
        let mut a = alice_values;
        a.set(0, 1);
        (a, bob_values)
    } else if mutation_kind == 3 {
        // set first alice value to 100 (max boundary)
        let mut a = alice_values;
        a.set(0, 100);
        (a, bob_values)
    } else if mutation_kind == 4 {
        // set first bob value to 1 (min boundary)
        let mut b = bob_values;
        b.set(0, 1);
        (alice_values, b)
    } else if mutation_kind == 5 {
        // set first bob value to 100 (max boundary)
        let mut b = bob_values;
        b.set(0, 100);
        (alice_values, b)
    } else if mutation_kind == 6 && alice_values.len() > 1 {
        // shrink: remove last element from both
        let mut a = alice_values;
        let mut b = bob_values;
        a.pop();
        b.pop();
        (a, b)
    } else if mutation_kind == 7 && alice_values.len() < 100_000 {
        // grow: append value 50 to both
        let mut a = alice_values;
        let mut b = bob_values;
        a.push(50);
        b.push(50);
        (a, b)
    } else if mutation_kind == 8 {
        // set all alice values to 1
        let n = alice_values.len();
        let mut a = alice_values;
        let mut i: usize = 0;
        while i < n
            invariant
                n == a.len(),
                a.len() == bob_values.len(),
                1 <= n <= 100_000,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] == 1i32,

            decreases n - i,
        {
            a.set(i, 1);
            i += 1;
        }
        (a, bob_values)
    } else if mutation_kind == 9 {
        // set all bob values to 100
        let n = bob_values.len();
        let mut b = bob_values;
        let mut i: usize = 0;
        while i < n
            invariant
                n == b.len(),
                b.len() == alice_values.len(),
                1 <= n <= 100_000,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> #[trigger] b[j] == 100i32,

            decreases n - i,
        {
            b.set(i, 100);
            i += 1;
        }
        (alice_values, b)
    } else if mutation_kind == 10 && alice_values.len() >= 2 {
        // swap first two elements in alice_values
        let mut a = alice_values;
        let v0 = a[0];
        let v1 = a[1];
        a.set(0, v1);
        a.set(1, v0);
        (a, bob_values)
    } else if mutation_kind == 11 {
        // nudge first alice value up (if < 100)
        let mut a = alice_values;
        if a[0] < 100 {
            a.set(0, a[0] + 1);
        }
        (a, bob_values)
    } else if mutation_kind == 12 {
        // nudge first bob value down (if > 1)
        let mut b = bob_values;
        if b[0] > 1 {
            b.set(0, b[0] - 1);
        }
        (alice_values, b)
    } else {
        // fallback: identity
        (alice_values, bob_values)
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

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1686);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |av: Vec<i32>, bv: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}{:?}", av, bv);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::stone_game_vi(av.clone(), bv.clone());
        writeln!(out, "{}", json!({
            "input": {"aliceValues": av, "bobValues": bv},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1, 3], vec![2, 1]),
        (vec![1, 2], vec![3, 1]),
        (vec![2, 4, 3], vec![1, 6, 7]),
    ];
    for (av, bv) in examples {
        let (ra, rb) = generate_test_case(av, bv, 0);
        emit(ra, rb, &mut seen, &mut out, &mut emitted);
    }

    // Boundary / special seed cases with all mutation kinds
    let special_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1], vec![1]),                   // min length, min values
        (vec![100], vec![100]),               // min length, max values
        (vec![1], vec![100]),                 // min length, extreme diff
        (vec![100], vec![1]),                 // min length, extreme diff reversed
        (vec![50, 50], vec![50, 50]),         // draw scenario
        (vec![1, 1, 1], vec![100, 100, 100]), // bob dominates
        (vec![100, 100, 100], vec![1, 1, 1]), // alice dominates
    ];
    for (av, bv) in special_seeds {
        for mk in 0..=12u8 {
            if emitted >= count { break; }
            let (ra, rb) = generate_test_case(av.clone(), bv.clone(), mk);
            emit(ra, rb, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes and mutation kinds
    let num_mutations: u8 = 13;
    while emitted < count {
        // Size classes
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 1000),  // large
            _ => rng.gen_range_usize(1001, 5000), // very large
        };

        let av = random_array(&mut rng, n);
        let bv = random_array(&mut rng, n);
        let mk = (rng.next_u64() % num_mutations as u64) as u8;

        let (ra, rb) = generate_test_case(av, bv, mk);
        emit(ra, rb, &mut seen, &mut out, &mut emitted);
    }
}
