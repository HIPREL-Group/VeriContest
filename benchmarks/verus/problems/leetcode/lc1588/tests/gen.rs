use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 100,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set last element to boundary min (1)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1);
        a
    } else if mutation_kind == 2 {
        // set last element to boundary max (1000)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1000);
        a
    } else if mutation_kind == 3 {
        // set first element to boundary min (1)
        let mut a = arr;
        a.set(0, 1);
        a
    } else if mutation_kind == 4 {
        // set first element to boundary max (1000)
        let mut a = arr;
        a.set(0, 1000);
        a
    } else if mutation_kind == 5 {
        // nudge first element up (if < 1000)
        let mut a = arr;
        if a[0] < 1000 {
            a.set(0, a[0] + 1);
        }
        a
    } else if mutation_kind == 6 {
        // nudge first element down (if > 1)
        let mut a = arr;
        if a[0] > 1 {
            a.set(0, a[0] - 1);
        }
        a
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100,
                forall|j: int| 0 <= j < i ==> a[j] == 1,
                forall|j: int| i <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000,
            decreases a.len() - i,
        {
            a.set(i, 1);
            i += 1;
        }
        a
    } else if mutation_kind == 8 {
        // set all elements to 1000
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100,
                forall|j: int| 0 <= j < i ==> a[j] == 1000,
                forall|j: int| i <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000,
            decreases a.len() - i,
        {
            a.set(i, 1000);
            i += 1;
        }
        a
    } else if mutation_kind == 9 && arr.len() < 100 {
        // grow by one element (push 500)
        let mut a = arr;
        a.push(500);
        a
    } else if mutation_kind == 10 && arr.len() > 1 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 11 && arr.len() >= 2 {
        // swap first two elements
        let mut a = arr;
        let v0 = a[0];
        let v1 = a[1];
        a.set(0, v1);
        a.set(1, v0);
        a
    } else if mutation_kind == 12 {
        // halve all elements (each becomes max(1, arr[i]/2))
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100,
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] a[j] <= 500,
                forall|j: int| i <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000,
            decreases a.len() - i,
        {
            let v = a[i] / 2;
            if v < 1 {
                a.set(i, 1);
            } else {
                a.set(i, v);
            }
            i += 1;
        }
        a
    } else {
        arr // fallback
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

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(1, 1000) as i32);
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
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", arr);
        if !seen.insert(key) { return; }
        let output = Solution::sum_odd_length_subarrays(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 4, 2, 5, 3],
        vec![1, 2],
        vec![10, 11, 12],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut emitted);
    }

    // Seed arrays with specific patterns
    let seed_arrays: Vec<Vec<i32>> = vec![
        vec![1],                           // single element (min length)
        vec![1, 2, 3],                     // small odd-length array
        vec![1, 2, 3, 4],                 // small even-length array
        vec![1000],                        // single max value
        vec![1, 1, 1, 1, 1],             // all ones
        vec![1000, 1000, 1000],           // all max values
        vec![1, 1000, 1, 1000],           // alternating min/max
        vec![500, 500, 500, 500, 500],    // all same mid value
    ];

    let num_mutations: u8 = 13;
    for seed_arr in &seed_arrays {
        for mk in 0..num_mutations {
            emit(generate_test_case(seed_arr.clone(), mk), &mut seen, &mut out, &mut emitted);
        }
    }

    // Random arrays across size classes with mutations
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 30),     // medium
            3 => rng.gen_range_usize(31, 70),     // large
            _ => rng.gen_range_usize(71, 100),    // max
        };
        let arr = random_arr(&mut rng, n);
        let mk = rng.gen_range_usize(0, (num_mutations - 1) as usize) as u8;
        emit(generate_test_case(arr, mk), &mut seen, &mut out, &mut emitted);
    }
}
