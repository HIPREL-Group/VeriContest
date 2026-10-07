use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 40_000,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 40_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut a = arr;
        a.set(0, 0);
        a
    } else if mutation_kind == 2 {
        // set first element to 1_000_000_000 (max boundary)
        let mut a = arr;
        a.set(0, 1_000_000_000);
        a
    } else if mutation_kind == 3 {
        // set last element to 0
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 0);
        a
    } else if mutation_kind == 4 {
        // set last element to 1_000_000_000
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1_000_000_000);
        a
    } else if mutation_kind == 5 {
        // set all elements to 0 (all equal — turbulence length 1)
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 40_000,
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] == 0i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        a
    } else if mutation_kind == 6 && arr.len() < 40_000 {
        // grow by one element (push 0)
        let mut a = arr;
        a.push(0);
        a
    } else if mutation_kind == 7 && arr.len() > 1 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 8 {
        // nudge first element up: if < 1_000_000_000, increment by 1
        let mut a = arr;
        if a[0] < 1_000_000_000 {
            a.set(0, a[0] + 1);
        }
        a
    } else if mutation_kind == 9 {
        // nudge first element down: if > 0, decrement by 1
        let mut a = arr;
        if a[0] > 0 {
            a.set(0, a[0] - 1);
        }
        a
    } else if mutation_kind == 10 && arr.len() >= 2 {
        // swap first two elements
        let mut a = arr;
        let tmp = a[0];
        a.set(0, a[1]);
        a.set(1, tmp);
        a
    } else if mutation_kind == 11 {
        // set all elements to 1_000_000_000
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 40_000,
                forall|j: int| 0 <= j < i ==> #[trigger] a[j] == 1_000_000_000i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 1_000_000_000);
            i += 1;
        }
        a
    } else {
        // fallback: identity
        arr
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

fn mutate(arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(arr, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    v
}

fn turbulent_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    // Build an array with alternating up/down pattern for interesting turbulence
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        if i % 2 == 0 {
            v.push(rng.gen_range_i64(0, 499_999_999) as i32);
        } else {
            v.push(rng.gen_range_i64(500_000_000, 1_000_000_000) as i32);
        }
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(978);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", arr);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_turbulence_size(arr.clone());
        writeln!(out, "{}", json!({
            "input": {"arr": arr},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![9, 4, 2, 10, 7, 8, 8, 1, 9], &mut seen, &mut out, &mut count);  // expected 5
    emit(vec![4, 8, 12, 16], &mut seen, &mut out, &mut count);                  // expected 2
    emit(vec![100], &mut seen, &mut out, &mut count);                            // expected 1

    // Seed inputs × mutations
    let seed_inputs: Vec<Vec<i32>> = vec![
        vec![9, 4, 2, 10, 7, 8, 8, 1, 9],
        vec![4, 8, 12, 16],
        vec![100],
        vec![0, 0, 0, 0],
        vec![1, 2, 1, 2, 1],
        vec![1_000_000_000, 0, 1_000_000_000, 0],
        vec![5, 5, 5],
        vec![1, 3, 2, 4, 3, 5],
        vec![0],
        vec![1_000_000_000],
        vec![1, 2],
        vec![2, 1],
        vec![1, 1],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11];

    for s in &seed_inputs {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases with diverse sizes
    while count < target_count {
        let n = match count % 6 {
            0 => rng.gen_range_usize(1, 3),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            4 => rng.gen_range_usize(1001, 10000),  // very large
            _ => rng.gen_range_usize(10001, 40000), // max
        };
        // Alternate between random and turbulent arrays
        let arr = if count % 2 == 0 {
            random_arr(&mut rng, n)
        } else {
            turbulent_arr(&mut rng, n)
        };
        let mk = rng.gen_range_usize(0, 11) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
