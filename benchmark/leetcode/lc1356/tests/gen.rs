use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 500,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 10000,
    ensures
        1 <= result.len() <= 500,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 0);
        a
    } else if mutation_kind == 2 {
        // set last element to 10000 (max boundary)
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 10000);
        a
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 500,
                forall|j: int| 0 <= j < i ==> a[j] == 0,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        a
    } else if mutation_kind == 4 && arr.len() < 500 {
        // grow by one element (push 0)
        let mut a = arr;
        a.push(0);
        a
    } else if mutation_kind == 5 && arr.len() > 1 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 6 {
        // nudge last element up (if < 10000)
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] < 10000 {
            a.set(last, a[last] + 1);
        }
        a
    } else if mutation_kind == 7 {
        // nudge last element down (if > 0)
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] > 0 {
            a.set(last, a[last] - 1);
        }
        a
    } else if mutation_kind == 8 && arr.len() >= 2 {
        // swap first and last elements
        let mut a = arr;
        let last = a.len() - 1;
        let tmp = a[0];
        a.set(0, a[last]);
        a.set(last, tmp);
        a
    } else if mutation_kind == 9 {
        // set all elements to the same value (first element)
        let val = arr[0];
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 500,
                0 <= val <= 10000,
                forall|j: int| 0 <= j < i ==> a[j] == val,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, val);
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

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 10000) as i32);
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
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", arr);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::sort_by_bits(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![0, 1, 2, 3, 4, 5, 6, 7, 8],
        vec![1024, 512, 256, 128, 64, 32, 16, 8, 4, 2, 1],
    ];
    for ex in examples {
        emit(ex, &mut seen, &mut out, &mut count);
    }

    // Boundary and special seed arrays
    let specials: Vec<Vec<i32>> = vec![
        vec![0],
        vec![10000],
        vec![0, 10000],
        vec![10000, 0],
        vec![1, 1, 1],
        vec![0, 0, 0, 0, 0],
        vec![7, 7, 7],               // same bit count, same value
        vec![1, 3, 5, 7, 9],         // odd numbers
        vec![2, 4, 8, 16, 32, 64],   // powers of two (1 bit each)
        vec![3, 5, 6, 9, 10, 12],    // 2 bits each
        vec![7, 11, 13, 14],         // 3 bits each
        vec![15, 23, 27, 29, 30],    // 4 bits each
        vec![255, 511, 1023, 2047, 4095, 8191], // high bit counts
    ];
    for s in specials {
        for mk in 0u8..=10 {
            if count >= target { break; }
            emit(generate_test_case(s.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random arrays with diverse sizes × mutations
    let num_mutations = 10u8;
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 300),   // large
            _ => rng.gen_range_usize(301, 500),   // max
        };
        let arr = random_arr(&mut rng, n);
        let mk = (rng.next_u64() % (num_mutations as u64 + 1)) as u8;
        emit(generate_test_case(arr, mk), &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
