use vstd::prelude::*;

verus! {

pub fn generate_test_case(pref: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= pref.len() <= 100_000,
        forall|i: int| 0 <= i < pref.len() ==> 0 <= #[trigger] pref[i] <= 1_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000_000,
{
    if mutation_kind == 0 {
        // identity
        pref
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = pref;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 1_000_000 (max boundary)
        let mut d = pref;
        let last = d.len() - 1;
        d.set(last, 1_000_000);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = pref;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == pref.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == pref[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 1_000_000
        let mut d = pref;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == pref.len(),
                1 <= d.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1_000_000,
                forall|j: int| i <= j < d.len() ==> d[j] == pref[j],
            decreases d.len() - i,
        {
            d.set(i, 1_000_000);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && pref.len() < 100_000 {
        // grow by one element (push 0)
        let mut d = pref;
        d.push(0);
        d
    } else if mutation_kind == 6 && pref.len() > 1 {
        // shrink by one element (pop)
        let mut d = pref;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // nudge last element up (if < 1_000_000)
        let mut d = pref;
        let last = d.len() - 1;
        if d[last] < 1_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut d = pref;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 9 {
        // set first element to 0
        let mut d = pref;
        d.set(0, 0);
        d
    } else if mutation_kind == 10 {
        // halve last element
        let mut d = pref;
        let last = d.len() - 1;
        d.set(last, d[last] / 2);
        d
    } else {
        pref // fallback
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn mutate(pref: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(pref, mutation_kind)
}

fn random_pref(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut pref = Vec::with_capacity(len);
    for _ in 0..len {
        pref.push(rng.gen_range_i64(0, 1_000_000) as i32);
    }
    pref
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

    let mut emit = |pref: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let key = format!("{:?}", pref);
        if *count >= goal || !seen.insert(key) {
            return;
        }
        let output = Solution::find_array(pref.clone());
        writeln!(out, "{}", json!({"input": {"pref": pref}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![5, 2, 0, 3, 1],
        vec![13],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Seed pool: interesting arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],
        vec![1_000_000],
        vec![0, 0],
        vec![0, 0, 0],
        vec![1_000_000, 1_000_000],
        vec![1, 2, 3, 4, 5],
        vec![0, 1_000_000, 0, 1_000_000],
        vec![999_999, 1, 500_000],
        vec![100, 200, 300, 400, 500, 600, 700, 800, 900, 1000],
        vec![1],
        vec![0, 1],
        vec![1, 0],
        vec![42],
        vec![7, 7, 7, 7],
    ];

    let mutation_kinds: Vec<u8> = (0..=11).collect();

    // Apply every mutation to every seed
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            if count >= goal { break; }
            let result = mutate(seed_arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
        if count >= goal { break; }
    }

    // Random arrays with size classes and random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),         // tiny
        (4, 10),        // small
        (11, 100),      // medium
        (101, 1000),    // large
        (1001, 10000),  // xlarge
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            if count >= goal { break; }
            let len = rng.gen_range_usize(*lo, *hi);
            let pref = random_pref(&mut rng, len);
            let mk = rng.gen_u8() % 12;
            let result = mutate(pref, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random arrays
    while count < goal {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };
        let pref = random_pref(&mut rng, len);
        let mk = rng.gen_u8() % 12;
        let result = mutate(pref, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases to {:?}", count, out_path);
}
