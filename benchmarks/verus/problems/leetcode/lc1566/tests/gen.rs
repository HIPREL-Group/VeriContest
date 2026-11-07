use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr: Vec<i32>,
    m: i32,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32))
    requires
        2 <= arr.len() <= 100,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
        1 <= m <= 100,
        2 <= k <= 100,
    ensures
        2 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
        2 <= result.2 <= 100,
{
    if mutation_kind == 0 {
        // identity
        (arr, m, k)
    } else if mutation_kind == 1 {
        // nudge first element up
        let mut a = arr;
        if a[0] < 100 {
            a.set(0, a[0] + 1);
        }
        (a, m, k)
    } else if mutation_kind == 2 {
        // nudge first element down
        let mut a = arr;
        if a[0] > 1 {
            a.set(0, a[0] - 1);
        }
        (a, m, k)
    } else if mutation_kind == 3 {
        // set all elements to the first element's value
        let val = arr[0];
        let len = arr.len();
        let mut a = arr;
        let mut i: usize = 1;
        while i < len
            invariant
                0 < i <= len,
                a.len() == len,
                2 <= len <= 100,
                1 <= val <= 100,
                forall|j: int| 0 <= j < i as int ==> a[j] == val,
            decreases len - i,
        {
            a.set(i, val);
            i += 1;
        }
        (a, m, k)
    } else if mutation_kind == 4 && arr.len() < 100 {
        // grow array by one element (push value 1)
        let mut a = arr;
        a.push(1);
        (a, m, k)
    } else if mutation_kind == 5 && arr.len() > 2 {
        // shrink array by one element
        let mut a = arr;
        a.pop();
        (a, m, k)
    } else if mutation_kind == 6 {
        // set last element to 1
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1);
        (a, m, k)
    } else if mutation_kind == 7 {
        // set last element to 100
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 100);
        (a, m, k)
    } else if mutation_kind == 8 && m < 100 {
        // nudge m up
        (arr, m + 1, k)
    } else if mutation_kind == 9 && m > 1 {
        // nudge m down
        (arr, m - 1, k)
    } else if mutation_kind == 10 && k < 100 {
        // nudge k up
        (arr, m, k + 1)
    } else if mutation_kind == 11 && k > 2 {
        // nudge k down
        (arr, m, k - 1)
    } else if mutation_kind == 12 {
        // set m = 1
        (arr, 1, k)
    } else if mutation_kind == 13 {
        // set k = 2
        (arr, m, 2)
    } else if mutation_kind == 14 {
        // swap first two elements
        let mut a = arr;
        let v0 = a[0];
        let v1 = a[1];
        a.set(0, v1);
        a.set(1, v0);
        (a, m, k)
    } else {
        // fallback: identity
        (arr, m, k)
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

fn gen(arr: Vec<i32>, m: i32, k: i32, mutation_kind: u8) -> (Vec<i32>, i32, i32) {
    generate_test_case(arr, m, k, mutation_kind)
}

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 100) as i32);
    }
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, m: i32, k: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}-{}-{}", arr, m, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::contains_pattern(arr.clone(), m, k);
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "m": m, "k": k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32, i32)> = vec![
        (vec![1,2,4,4,4,4], 1, 3),
        (vec![1,2,1,2,1,1,1,3], 2, 2),
        (vec![1,2,1,2,1,3], 2, 3),
    ];
    for (arr, m, k) in &examples {
        emit(arr.clone(), *m, *k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with interesting structures
    let seed_arrs: Vec<Vec<i32>> = vec![
        vec![1, 1],
        vec![1, 2],
        vec![1, 1, 1, 1, 1],
        vec![1, 2, 1, 2, 1, 2],
        vec![1, 2, 3, 1, 2, 3, 1, 2, 3],
        vec![100, 100, 100, 100],
        vec![50, 50, 50, 50, 50, 50, 50, 50],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![1; 100],
        vec![99, 100, 99, 100, 99, 100],
    ];
    let seed_ms: Vec<i32> = vec![1, 2, 3, 5, 10, 50, 100];
    let seed_ks: Vec<i32> = vec![2, 3, 5, 10, 50, 100];
    let mutation_kinds: Vec<u8> = (0..=14).collect();

    // Apply seeds × m × k × mutations
    for arr in &seed_arrs {
        for &m in &seed_ms {
            for &k in &seed_ks {
                for &mk in &mutation_kinds {
                    if count >= target_count { break; }
                    let (ra, rm, rk) = gen(arr.clone(), m, k, mk);
                    emit(ra, rm, rk, &mut seen, &mut out, &mut count);
                }
            }
        }
    }

    // Random test cases with diverse sizes
    while count < target_count {
        let len = match count % 5 {
            0 => rng.gen_range_usize(2, 5),     // tiny
            1 => rng.gen_range_usize(2, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let arr = random_arr(&mut rng, len);
        let m = rng.gen_range_i64(1, 100) as i32;
        let k = rng.gen_range_i64(2, 100) as i32;
        let mk = rng.gen_range_usize(0, 14) as u8;
        let (ra, rm, rk) = gen(arr, m, k, mk);
        emit(ra, rm, rk, &mut seen, &mut out, &mut count);
    }
}
