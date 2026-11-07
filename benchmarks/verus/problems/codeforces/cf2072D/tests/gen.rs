use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i64>, mutation_kind: u8) -> (result: Vec<i64>)
    requires
        1 <= a.len() <= 2000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 2000,
    ensures
        1 <= result.len() <= 2000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 2000,
{
    if mutation_kind == 0 {
        // identity
        a
    } else if mutation_kind == 1 {
        // set first element to 1 (min boundary)
        let mut d = a;
        d.set(0, 1);
        d
    } else if mutation_kind == 2 {
        // set first element to 2000 (max boundary)
        let mut d = a;
        d.set(0, 2000);
        d
    } else if mutation_kind == 3 {
        // set last element to 1
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 4 {
        // set last element to 2000
        let mut d = a;
        let last = d.len() - 1;
        d.set(last, 2000);
        d
    } else if mutation_kind == 5 && a.len() < 2000 {
        // grow by one element
        let mut d = a;
        d.push(1);
        d
    } else if mutation_kind == 6 && a.len() > 1 {
        // shrink by one element
        let mut d = a;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut d = a;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == a.len(),
                1 <= d.len() <= 2000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i64,
                forall|j: int| i <= j < d.len() ==> d[j] == a[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 8 {
        // nudge first element up (if < 2000)
        let mut d = a;
        if d[0] < 2000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 9 {
        // nudge first element down (if > 1)
        let mut d = a;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        d
    } else if mutation_kind == 10 && a.len() >= 2 {
        // swap first two elements
        let mut d = a;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        d
    } else {
        // fallback: identity
        a
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

fn mutate(a: Vec<i64>, mutation_kind: u8) -> Vec<i64> {
    generate_test_case(a, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i64> {
    let mut a = Vec::with_capacity(len);
    for _ in 0..len {
        a.push(rng.gen_range_i64(1, 2000));
    }
    a
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2072);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |a: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", a);
        if !seen.insert(key) {
            return;
        }
        let (l, r) = Solution::best_shift(a.clone());
        writeln!(out, "{}", json!({"input": {"a": a}, "output": [l, r]})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description (1-indexed values)
    let examples: Vec<Vec<i64>> = vec![
        vec![1, 4, 3, 2, 5, 3, 3],
        vec![1, 4, 3, 2, 5, 3],
        vec![7, 6, 5, 8, 4, 3, 2, 1],
        vec![1, 1, 1, 5, 1, 1, 5, 6, 7, 8],
        vec![1337],
        vec![6942, 1, 2, 1],
        vec![3998, 244, 353],
        vec![1, 2, 1],
        vec![1, 1, 2, 3, 5, 8, 13, 21, 34],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Examples × all mutations
    for ex in &examples {
        for &mk in &mutation_kinds {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Specific edge cases
    // Single element
    emit(mutate(vec![1], 0), &mut seen, &mut out, &mut count);
    emit(mutate(vec![2000], 0), &mut seen, &mut out, &mut count);
    // Two elements
    emit(mutate(vec![1, 2000], 0), &mut seen, &mut out, &mut count);
    emit(mutate(vec![2000, 1], 0), &mut seen, &mut out, &mut count);
    // All same
    emit(mutate(vec![500, 500, 500, 500], 0), &mut seen, &mut out, &mut count);
    // Sorted ascending
    emit(mutate(vec![1, 2, 3, 4, 5], 0), &mut seen, &mut out, &mut count);
    // Sorted descending
    emit(mutate(vec![5, 4, 3, 2, 1], 0), &mut seen, &mut out, &mut count);

    // Random arrays with diverse sizes and mutations
    for _ in 0..80 {
        if count >= target { break; }
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 500),    // large
            _ => rng.gen_range_usize(501, 2000),   // max
        };
        let arr = random_array(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        emit(mutate(arr, mk), &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 2000),
        };
        let arr = random_array(&mut rng, n);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut count);
    }
}
