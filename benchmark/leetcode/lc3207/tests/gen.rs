use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    enemy_energies: Vec<i32>,
    current_energy: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= enemy_energies.len() <= 100000,
        0 <= current_energy <= 1000000000,
        forall|i: int| 0 <= i < enemy_energies.len() ==> 1 <= #[trigger] enemy_energies[i] <= 1000000000,
    ensures
        1 <= result.0.len() <= 100000,
        0 <= result.1 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        (enemy_energies, current_energy)
    } else if mutation_kind == 1 {
        // set first element to boundary low (1)
        let mut e = enemy_energies;
        e.set(0, 1);
        (e, current_energy)
    } else if mutation_kind == 2 {
        // set first element to boundary high (1_000_000_000)
        let mut e = enemy_energies;
        e.set(0, 1_000_000_000);
        (e, current_energy)
    } else if mutation_kind == 3 {
        // set current_energy to 0
        (enemy_energies, 0)
    } else if mutation_kind == 4 {
        // set current_energy to max boundary
        (enemy_energies, 1_000_000_000)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let ghost old_len = enemy_energies.len();
        let mut e = enemy_energies;
        let mut i: usize = 0;
        while i < e.len()
            invariant
                0 <= i <= e.len(),
                e.len() == old_len,
                1 <= e.len() <= 100000,
                forall|j: int| 0 <= j < i ==> e[j] == 1i32,
                forall|j: int| i <= j < e.len() ==> 1 <= #[trigger] e[j] <= 1000000000,
            decreases e.len() - i,
        {
            e.set(i, 1);
            i += 1;
        }
        (e, current_energy)
    } else if mutation_kind == 6 && enemy_energies.len() >= 2 {
        // swap first two elements
        let mut e = enemy_energies;
        let a = e[0];
        let b = e[1];
        e.set(0, b);
        e.set(1, a);
        (e, current_energy)
    } else if mutation_kind == 7 {
        // set last element to 1
        let mut e = enemy_energies;
        let last = e.len() - 1;
        e.set(last, 1);
        (e, current_energy)
    } else if mutation_kind == 8 {
        // nudge first element down (if > 1)
        let mut e = enemy_energies;
        if e[0] > 1 {
            e.set(0, e[0] - 1);
        }
        (e, current_energy)
    } else if mutation_kind == 9 {
        // nudge first element up (if < 1_000_000_000)
        let mut e = enemy_energies;
        if e[0] < 1_000_000_000 {
            e.set(0, e[0] + 1);
        }
        (e, current_energy)
    } else if mutation_kind == 10 {
        // set current_energy to first enemy energy (guarantees at least 1 point)
        let ce = enemy_energies[0];
        (enemy_energies, ce)
    } else if mutation_kind == 11 {
        // set current_energy to 1 (just below smallest possible enemy)
        (enemy_energies, 1)
    } else {
        // fallback: identity
        (enemy_energies, current_energy)
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

fn mutate(enemy_energies: Vec<i32>, current_energy: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(enemy_energies, current_energy, mutation_kind)
}

fn random_enemy_energies(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    v
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

    let mut emit = |enemy_energies: Vec<i32>, current_energy: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{:?}_{}", enemy_energies, current_energy);
        if !seen.insert(key) { return; }
        let output = Solution::maximum_points(enemy_energies.clone(), current_energy);
        writeln!(out, "{}", json!({
            "input": {"enemy_energies": enemy_energies, "current_energy": current_energy},
            "output": output
        })).unwrap();
        *count += 1;
    };

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    // Seed inputs from examples + edge cases
    let seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![3, 2, 2], 2),                           // example 1
        (vec![2], 10),                                  // example 2
        (vec![1], 0),                                   // min len, zero energy
        (vec![1], 1),                                   // min len, energy == enemy
        (vec![1_000_000_000], 1_000_000_000),          // max values
        (vec![1, 1, 1], 0),                             // zero energy, can't score
        (vec![5, 3, 1, 4, 2], 3),                      // unsorted, mid energy
        (vec![1, 2, 3, 4, 5], 15),                     // energy >= sum
        (vec![10, 20, 30], 5),                          // energy < all enemies
        (vec![1, 1000000000], 500000000),              // wide range
        (vec![1, 1], 1),                                // duplicates
        (vec![999999999, 1000000000], 999999999),      // near-max values
    ];

    // Apply every mutation to every seed
    for (ee, ce) in &seeds {
        for &mk in &mutation_kinds {
            let (re, rc) = mutate(ee.clone(), *ce, mk);
            emit(re, rc, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => 1,                                    // tiny: len = 1
            1 => rng.gen_range_usize(1, 10),           // small
            2 => rng.gen_range_usize(11, 100),         // medium
            3 => rng.gen_range_usize(101, 1000),       // large
            _ => 1,
        };
        let ee = random_enemy_energies(&mut rng, n);
        let ce = rng.gen_range_i64(0, 1_000_000_000) as i32;
        let mk = rng.gen_range_usize(0, 12) as u8;
        let (re, rc) = mutate(ee, ce, mk);
        emit(re, rc, &mut seen, &mut out, &mut count);
    }
}
