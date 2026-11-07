use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    original: Vec<i32>,
    m: i32,
    n: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= original.len() <= 50_000,
        1 <= m <= 40_000,
        1 <= n <= 40_000,
        m as int * n as int <= usize::MAX as int,
        forall|i: int| 0 <= i < original.len() ==> 1 <= #[trigger] original[i] <= 100_000,
    ensures
        1 <= result.0.len() <= 50_000,
        1 <= result.1 <= 40_000,
        1 <= result.2 <= 40_000,
        result.1 * result.2 <= usize::MAX,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (original, m, n)
    } else if mutation_kind == 1 {
        // nudge first element up
        let mut arr = original;
        if arr[0] < 100_000 {
            arr.set(0, arr[0] + 1);
        }
        (arr, m, n)
    } else if mutation_kind == 2 {
        // nudge first element down
        let mut arr = original;
        if arr[0] > 1 {
            arr.set(0, arr[0] - 1);
        }
        (arr, m, n)
    } else if mutation_kind == 3 {
        // set all elements to 1 (min boundary)
        let mut arr = original;
        let mut i: usize = 0;
        while i < arr.len()
            invariant
                0 <= i <= arr.len(),
                arr.len() == original.len(),
                1 <= arr.len() <= 50_000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] arr[j] == 1i32,
                forall|j: int| i as int <= j < arr.len() ==> 1 <= #[trigger] arr[j] <= 100_000,
            decreases arr.len() - i,
        {
            arr.set(i, 1);
            i += 1;
        }
        (arr, m, n)
    } else if mutation_kind == 4 {
        // set all elements to 100_000 (max boundary)
        let mut arr = original;
        let mut i: usize = 0;
        while i < arr.len()
            invariant
                0 <= i <= arr.len(),
                arr.len() == original.len(),
                1 <= arr.len() <= 50_000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] arr[j] == 100_000i32,
                forall|j: int| i as int <= j < arr.len() ==> 1 <= #[trigger] arr[j] <= 100_000,
            decreases arr.len() - i,
        {
            arr.set(i, 100_000);
            i += 1;
        }
        (arr, m, n)
    } else if mutation_kind == 5 && original.len() < 50_000 {
        // grow by one element
        let mut arr = original;
        arr.push(1);
        (arr, m, n)
    } else if mutation_kind == 6 && original.len() > 1 {
        // shrink by one element
        let mut arr = original;
        arr.pop();
        (arr, m, n)
    } else if mutation_kind == 7 {
        // nudge last element up
        let mut arr = original;
        let last = arr.len() - 1;
        if arr[last] < 100_000 {
            arr.set(last, arr[last] + 1);
        }
        (arr, m, n)
    } else if mutation_kind == 8 {
        // nudge last element down
        let mut arr = original;
        let last = arr.len() - 1;
        if arr[last] > 1 {
            arr.set(last, arr[last] - 1);
        }
        (arr, m, n)
    } else if mutation_kind == 9 {
        // swap first and last elements
        let mut arr = original;
        let last = arr.len() - 1;
        let first_val = arr[0];
        let last_val = arr[last];
        arr.set(0, last_val);
        arr.set(last, first_val);
        (arr, m, n)
    } else {
        // fallback: identity
        (original, m, n)
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

fn mutate(original: Vec<i32>, m: i32, n: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(original, m, n, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_array(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2022);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |original: Vec<i32>, m: i32, n: i32,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{:?}-{}-{}", original, m, n);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::construct2_d_array(original.clone(), m, n);
        writeln!(out, "{}", json!({
            "input": {"original": original, "m": m, "n": n},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    emit(vec![1,2,3,4], 2, 2, &mut seen, &mut out, &mut emitted);
    emit(vec![1,2,3], 1, 3, &mut seen, &mut out, &mut emitted);
    emit(vec![1,2], 1, 1, &mut seen, &mut out, &mut emitted);

    // Seed inputs: (original, m, n)
    let seeds: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1], 1, 1),                           // single element, valid
        (vec![1], 2, 1),                           // single element, invalid
        (vec![1,2,3,4,5,6], 2, 3),                // 2x3, valid
        (vec![1,2,3,4,5,6], 3, 2),                // 3x2, valid
        (vec![1,2,3,4,5,6], 6, 1),                // 6x1, valid
        (vec![1,2,3,4,5,6], 1, 6),                // 1x6, valid
        (vec![1,2,3,4,5,6], 4, 2),                // invalid (6 != 8)
        (vec![100_000], 1, 1),                     // max element value
        (vec![1, 100_000, 50_000], 1, 3),          // mixed values
        (vec![1,2,3,4,5,6,7,8,9,10,11,12], 3, 4), // 3x4, valid
        (vec![1,2,3,4,5,6,7,8,9,10,11,12], 4, 3), // 4x3, valid
        (vec![1,2,3,4,5,6,7,8,9,10,11,12], 2, 5), // invalid (12 != 10)
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every seed
    for (orig, m, n) in &seeds {
        for &mk in &mutation_kinds {
            let (new_orig, new_m, new_n) = mutate(orig.clone(), *m, *n, mk);
            emit(new_orig, new_m, new_n, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random test cases with diverse sizes and m/n configurations
    while emitted < count {
        // Choose array length from size classes
        let len: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 50_000), // max
        };

        let arr = random_array(&mut rng, len);

        // Sometimes choose m, n so m*n == len (valid reshape), sometimes not
        let (m, n) = if rng.gen_range_usize(0, 1) == 0 && len <= 40_000 {
            // Try to find a valid factorization
            let mut m_val = 0i32;
            let mut n_val = 0i32;
            for f in 1..=len.min(40_000) {
                if len % f == 0 && len / f <= 40_000 {
                    m_val = f as i32;
                    n_val = (len / f) as i32;
                    break;
                }
            }
            if m_val == 0 {
                (rng.gen_range_i64(1, 40_000) as i32, rng.gen_range_i64(1, 40_000) as i32)
            } else {
                (m_val, n_val)
            }
        } else {
            (rng.gen_range_i64(1, 40_000) as i32, rng.gen_range_i64(1, 40_000) as i32)
        };

        let mk = rng.gen_range_usize(0, 9) as u8;
        let (new_orig, new_m, new_n) = mutate(arr, m, n, mk);
        emit(new_orig, new_m, new_n, &mut seen, &mut out, &mut emitted);
    }
}
