use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, rm: Vec<i32>, mutation_kind: u8) -> (result: (i32, Vec<i32>))
    requires
        1 <= n <= 5000,
        rm.len() == 6,
        forall|j: int| 0 <= j < 6 ==> 1 <= #[trigger] rm[j] <= 15,
    ensures
        1 <= result.0 <= 5000,
        result.1.len() == 6,
        forall|j: int| 0 <= j < 6 ==> 1 <= #[trigger] result.1[j] <= 15,
{
    if mutation_kind == 0 {
        // identity
        (n, rm)
    } else if mutation_kind == 1 && n < 5000 {
        // nudge n up
        (n + 1, rm)
    } else if mutation_kind == 2 && n > 1 {
        // nudge n down
        (n - 1, rm)
    } else if mutation_kind == 3 {
        // n = 1 (min boundary)
        (1, rm)
    } else if mutation_kind == 4 {
        // n = 5000 (max boundary)
        (5000, rm)
    } else if mutation_kind == 5 {
        // halve n
        let half = n / 2;
        if half >= 1 { (half, rm) } else { (1, rm) }
    } else if mutation_kind == 6 && n <= 2500 {
        // double n
        (n * 2, rm)
    } else if mutation_kind == 7 {
        // set all roll_max to 1
        let ghost old_rm = rm@;
        let mut r = rm;
        let mut i: usize = 0;
        while i < 6
            invariant
                r.len() == 6,
                0 <= i <= 6,
                forall|j: int| 0 <= j < i ==> #[trigger] r[j] == 1,
                forall|j: int| i <= j < 6 ==> #[trigger] r[j] == old_rm[j],
                forall|j: int| i <= j < 6 ==> 1 <= #[trigger] r[j] <= 15,
            decreases 6 - i,
        {
            r.set(i, 1);
            i += 1;
        }
        (n, r)
    } else if mutation_kind == 8 {
        // set all roll_max to 15
        let ghost old_rm = rm@;
        let mut r = rm;
        let mut i: usize = 0;
        while i < 6
            invariant
                r.len() == 6,
                0 <= i <= 6,
                forall|j: int| 0 <= j < i ==> #[trigger] r[j] == 15,
                forall|j: int| i <= j < 6 ==> #[trigger] r[j] == old_rm[j],
                forall|j: int| i <= j < 6 ==> 1 <= #[trigger] r[j] <= 15,
            decreases 6 - i,
        {
            r.set(i, 15);
            i += 1;
        }
        (n, r)
    } else if mutation_kind == 9 {
        // nudge first roll_max element up (if < 15)
        let mut r = rm;
        if r[0] < 15 {
            r.set(0, r[0] + 1);
        }
        (n, r)
    } else if mutation_kind == 10 {
        // nudge first roll_max element down (if > 1)
        let mut r = rm;
        if r[0] > 1 {
            r.set(0, r[0] - 1);
        }
        (n, r)
    } else if mutation_kind == 11 {
        // set first roll_max element to 1 (min)
        let mut r = rm;
        r.set(0, 1);
        (n, r)
    } else if mutation_kind == 12 {
        // set first roll_max element to 15 (max)
        let mut r = rm;
        r.set(0, 15);
        (n, r)
    } else {
        // fallback: identity
        (n, rm)
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

fn random_roll_max(rng: &mut Rng) -> Vec<i32> {
    (0..6).map(|_| rng.gen_range_i64(1, 15) as i32).collect()
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

    let mut emit = |n: i32, roll_max: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let key = format!("{}:{:?}", n, roll_max);
        if !seen.insert(key) { return; }
        let output = Solution::die_simulator(n, roll_max.clone());
        writeln!(out, "{}", json!({
            "input": {"n": n, "rollMax": roll_max},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(i32, Vec<i32>)> = vec![
        (2, vec![1, 1, 2, 2, 2, 3]),
        (2, vec![1, 1, 1, 1, 1, 1]),
        (3, vec![1, 1, 1, 2, 2, 3]),
    ];
    for (n, rm) in &examples {
        emit(*n, rm.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed pool of interesting (n, roll_max) pairs
    let n_seeds: Vec<i32> = vec![
        1, 2, 3, 5, 10, 50, 100, 500, 1000, 2500, 5000,
    ];
    let rm_seeds: Vec<Vec<i32>> = vec![
        vec![1, 1, 1, 1, 1, 1],
        vec![15, 15, 15, 15, 15, 15],
        vec![1, 2, 3, 4, 5, 6],
        vec![1, 1, 2, 2, 2, 3],
        vec![15, 1, 15, 1, 15, 1],
        vec![8, 8, 8, 8, 8, 8],
    ];

    // Apply mutations to seed pool
    for &n in &n_seeds {
        for rm in &rm_seeds {
            for mk in 0..=12u8 {
                if count >= target { break; }
                let result = generate_test_case(n, rm.clone(), mk);
                emit(result.0, result.1, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random inputs with diverse size classes for n
    while count < target {
        let n: i32 = match count % 5 {
            0 => rng.gen_range_i64(1, 5) as i32,        // tiny
            1 => rng.gen_range_i64(1, 50) as i32,       // small
            2 => rng.gen_range_i64(51, 500) as i32,     // medium
            3 => rng.gen_range_i64(501, 2500) as i32,   // large
            _ => rng.gen_range_i64(2501, 5000) as i32,  // max
        };
        let rm = random_roll_max(&mut rng);
        let mk = rng.gen_range_usize(0, 12) as u8;
        let result = generate_test_case(n, rm, mk);
        emit(result.0, result.1, &mut seen, &mut out, &mut count);
    }
}
