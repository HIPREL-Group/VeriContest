use vstd::prelude::*;

verus! {

pub fn generate_test_case(hours: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= hours.len() <= 500000,
        forall |i: int| 0 <= i < hours.len() ==> 1 <= #[trigger] hours[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 500000,
        forall |i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        hours
    } else if mutation_kind == 1 {
        // set last element to 24 (exact multiple of 24)
        let mut h = hours;
        let last = h.len() - 1;
        h.set(last, 24);
        h
    } else if mutation_kind == 2 {
        // set last element to 12 (half day — pairs with another 12)
        let mut h = hours;
        let last = h.len() - 1;
        h.set(last, 12);
        h
    } else if mutation_kind == 3 {
        // set all elements to 24 (every pair forms a complete day)
        let mut h = hours;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == hours.len(),
                1 <= h.len() <= 500000,
                forall |j: int| 0 <= j < i ==> h[j] == 24i32,
                forall |j: int| i <= j < h.len() ==> h[j] == hours[j],
            decreases h.len() - i,
        {
            h.set(i, 24);
            i += 1;
        }
        h
    } else if mutation_kind == 4 {
        // set all elements to 1 (no pair sums to multiple of 24 for small arrays)
        let mut h = hours;
        let mut i: usize = 0;
        while i < h.len()
            invariant
                0 <= i <= h.len(),
                h.len() == hours.len(),
                1 <= h.len() <= 500000,
                forall |j: int| 0 <= j < i ==> h[j] == 1i32,
                forall |j: int| i <= j < h.len() ==> h[j] == hours[j],
            decreases h.len() - i,
        {
            h.set(i, 1);
            i += 1;
        }
        h
    } else if mutation_kind == 5 && hours.len() < 500000 {
        // append element 24
        let mut h = hours;
        h.push(24);
        h
    } else if mutation_kind == 6 && hours.len() > 1 {
        // remove last element
        let mut h = hours;
        h.pop();
        h
    } else if mutation_kind == 7 {
        // set last element to 1_000_000_000 (max boundary)
        let mut h = hours;
        let last = h.len() - 1;
        h.set(last, 1_000_000_000);
        h
    } else if mutation_kind == 8 {
        // set last element to 1 (min boundary)
        let mut h = hours;
        let last = h.len() - 1;
        h.set(last, 1);
        h
    } else if mutation_kind == 9 {
        // set first element to 48 (2 complete days)
        let mut h = hours;
        h.set(0, 48);
        h
    } else {
        hours // fallback
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn mutate(hours: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(hours, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_hours(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut hours = Vec::with_capacity(len);
    for _ in 0..len {
        hours.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    hours
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3185);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |hours: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", hours);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_complete_day_pairs(hours.clone());
        writeln!(out, "{}", json!({"input": {"hours": hours}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![12, 12, 30, 24, 24],       // expected output: 2
        vec![72, 48, 24, 3],             // expected output: 3
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Hand-crafted seeds covering interesting patterns
    let seeds: Vec<Vec<i32>> = vec![
        vec![1],                              // single element, no pairs
        vec![24, 24],                         // minimal pair
        vec![12, 12],                         // 12+12=24
        vec![1, 23],                          // 1+23=24
        vec![6, 18],                          // 6+18=24
        vec![24, 48, 72],                     // all multiples of 24
        vec![1, 2, 3, 4, 5],                  // no pairs sum to 24
        vec![1_000_000_000, 1_000_000_000],   // max values
        vec![1, 1],                           // min values
        vec![12, 36, 12, 36],                 // multiple pairs: 12+36=48
        vec![23, 1, 23, 1],                   // pairs: (0,1),(0,3),(1,2),(2,3)
        vec![8, 16, 8, 16, 8],               // 8+16=24
        vec![24],                             // single multiple of 24
        vec![11, 13, 11, 13],                 // 11+13=24
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size-class-based random generation
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),         // tiny
        (6, 20),        // small
        (21, 100),      // medium
        (101, 1000),    // large
        (1001, 5000),   // very large
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..5 {
            let len = rng.gen_range_usize(*lo, *hi);
            let hrs = random_hours(&mut rng, len);
            let mk = rng.gen_range_usize(0, 9) as u8;
            let result = mutate(hrs, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random with boundary values mixed in (~20%)
    while count < target {
        let len = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let mut hrs = Vec::with_capacity(len);
        for j in 0..len {
            let val = if j % 5 == 0 {
                // boundary values
                let choices = [1i64, 24, 12, 48, 1_000_000_000, 999_999_999, 23, 1];
                let idx = rng.gen_range_usize(0, choices.len() - 1);
                choices[idx] as i32
            } else {
                rng.gen_range_i64(1, 1_000_000_000) as i32
            };
            hrs.push(val);
        }
        let mk = rng.gen_range_usize(0, 9) as u8;
        let result = mutate(hrs, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
