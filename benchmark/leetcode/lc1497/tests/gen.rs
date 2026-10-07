use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, k: i32, mutation_kind: u8) -> (res: (Vec<i32>, i32))
    requires
        arr@.len() % 2 == 0,
        2 <= arr@.len() <= 100000,
        1 <= k <= 100000,
        forall|i: int| 0 <= i < arr@.len() ==> -1000000000 <= #[trigger] arr@[i] <= 1000000000,
    ensures
        res.0@.len() % 2 == 0,
        2 <= res.0@.len() <= 100000,
        1 <= res.1 <= 100000,
        forall|i: int| 0 <= i < res.0@.len() ==> -1000000000 <= #[trigger] res.0@[i] <= 1000000000,
{
    if mutation_kind == 0 {
        // identity
        (arr, k)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut a = arr;
        a.set(0, 0);
        (a, k)
    } else if mutation_kind == 2 {
        // set first element to max boundary
        let mut a = arr;
        a.set(0, 1000000000);
        (a, k)
    } else if mutation_kind == 3 {
        // set first element to min boundary
        let mut a = arr;
        a.set(0, -1000000000);
        (a, k)
    } else if mutation_kind == 4 {
        // swap first two elements
        let mut a = arr;
        let tmp0 = a[0];
        let tmp1 = a[1];
        a.set(0, tmp1);
        a.set(1, tmp0);
        (a, k)
    } else if mutation_kind == 5 {
        // set all elements to 0
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                a@.len() % 2 == 0,
                2 <= a@.len() <= 100000,
                forall|j: int| 0 <= j < i ==> a@[j] == 0i32,
                forall|j: int| i <= j < a@.len() ==> a@[j] == arr@[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        (a, k)
    } else if mutation_kind == 6 && k < 100000 {
        // nudge k up
        (arr, k + 1)
    } else if mutation_kind == 7 && k > 1 {
        // nudge k down
        (arr, k - 1)
    } else if mutation_kind == 8 {
        // set k to 1
        (arr, 1)
    } else if mutation_kind == 9 {
        // set k to max
        (arr, 100000)
    } else if mutation_kind == 10 && arr.len() <= 99998 {
        // grow by 2 elements
        let mut a = arr;
        a.push(0);
        a.push(0);
        (a, k)
    } else if mutation_kind == 11 && arr.len() > 2 {
        // shrink by 2 elements
        let mut a = arr;
        a.pop();
        a.pop();
        (a, k)
    } else if mutation_kind == 12 {
        // set last element to max boundary
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1000000000);
        (a, k)
    } else if mutation_kind == 13 {
        // set last element to min boundary
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, -1000000000);
        (a, k)
    } else {
        // fallback: identity
        (arr, k)
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

fn mutate(arr: Vec<i32>, k: i32, mutation_kind: u8) -> (Vec<i32>, i32) {
    generate_test_case(arr, k, mutation_kind)
}

fn random_even_arr(rng: &mut Rng, half_len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let len = half_len * 2;
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(lo, hi) as i32);
    }
    arr
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::collections::HashSet;
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, k: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}_{}", arr, k);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::can_arrange(arr.clone(), k);
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "k": k},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![1,2,3,4,5,10,6,7,8,9], 5),
        (vec![1,2,3,4,5,6], 7),
        (vec![1,2,3,4,5,6], 10),
    ];

    for (arr, k) in &examples {
        emit(arr.clone(), *k, &mut seen, &mut out, &mut count);
    }

    // Seed arrays with interesting patterns
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![0, 0],
        vec![1, -1],
        vec![1000000000, -1000000000],
        vec![0, 0, 0, 0],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![-1, -2, -3, -4],
        vec![5, 5, 5, 5, 5, 5],
        vec![0, 1, 0, 1],
        vec![999999999, 1000000000, -999999999, -1000000000],
        vec![7, 14, 21, 28],
    ];
    let seed_ks: Vec<i32> = vec![1, 2, 3, 5, 7, 10, 100, 1000, 99999, 100000];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13];

    // Apply mutations to seed arrays × seed k values
    for arr in &seed_arrays {
        for &k in &seed_ks {
            for &mk in &mutation_kinds {
                if count >= target_count { break; }
                let (out_arr, out_k) = mutate(arr.clone(), k, mk);
                emit(out_arr, out_k, &mut seen, &mut out, &mut count);
            }
        }
    }

    // Random test cases with diverse sizes
    while count < target_count {
        let half_len: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny (2-6 elements)
            1 => rng.gen_range_usize(2, 10),        // small (4-20 elements)
            2 => rng.gen_range_usize(10, 50),       // medium (20-100 elements)
            3 => rng.gen_range_usize(50, 500),      // large (100-1000 elements)
            _ => rng.gen_range_usize(500, 5000),    // big (1000-10000 elements)
        };

        // Value range diversity
        let (lo, hi): (i64, i64) = match count % 4 {
            0 => (-1000000000, 1000000000),   // full range
            1 => (-100, 100),                  // small values
            2 => (0, 1000000000),              // non-negative
            _ => (-1000000000, 0),             // non-positive
        };

        let arr = random_even_arr(&mut rng, half_len, lo, hi);

        // k diversity
        let k: i32 = match count % 5 {
            0 => 1,
            1 => rng.gen_range_i64(1, 10) as i32,
            2 => rng.gen_range_i64(1, 1000) as i32,
            3 => rng.gen_range_i64(1, 100000) as i32,
            _ => 100000,
        };

        let mk = rng.gen_range_usize(0, 13) as u8;
        let (out_arr, out_k) = mutate(arr, k, mk);
        emit(out_arr, out_k, &mut seen, &mut out, &mut count);
    }
}
