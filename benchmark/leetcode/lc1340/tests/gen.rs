use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr: Vec<i32>,
    d_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= arr.len() <= 1000,
        1 <= d_val <= arr.len(),
        forall|i: int| 0 <= i < arr.len() ==> 1 <= (#[trigger] arr[i]) <= 100_000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= (#[trigger] result.0[i]) <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (arr, d_val)
    } else if mutation_kind == 1 {
        // set d to 1 (minimum jump distance)
        (arr, 1i32)
    } else if mutation_kind == 2 {
        // set d to arr.len() (maximum jump distance)
        let d = arr.len() as i32;
        (arr, d)
    } else if mutation_kind == 3 {
        // set all elements to the same value
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == 1i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 1);
            i += 1;
        }
        (a, d_val)
    } else if mutation_kind == 4 {
        // make strictly decreasing: arr[i] = len - i
        let mut a = arr;
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == (n - j) as i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases n - i,
        {
            a.set(i, (n - i) as i32);
            i += 1;
        }
        (a, d_val)
    } else if mutation_kind == 5 {
        // make strictly increasing: arr[i] = i + 1
        let mut a = arr;
        let n = a.len();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n == a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 1000,
                forall|j: int| 0 <= j < i ==> a[j] == (j + 1) as i32,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases n - i,
        {
            a.set(i, (i + 1) as i32);
            i += 1;
        }
        (a, d_val)
    } else if mutation_kind == 6 && arr.len() < 1000 {
        // grow by one element (push 1)
        let mut a = arr;
        a.push(1);
        let d = if d_val <= a.len() as i32 { d_val } else { a.len() as i32 };
        (a, d)
    } else if mutation_kind == 7 && arr.len() > 1 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        let d = if d_val <= a.len() as i32 { d_val } else { a.len() as i32 };
        (a, d)
    } else if mutation_kind == 8 {
        // set first element to max value
        let mut a = arr;
        a.set(0, 100_000);
        (a, d_val)
    } else if mutation_kind == 9 {
        // set last element to max value
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 100_000);
        (a, d_val)
    } else {
        // fallback: identity
        (arr, d_val)
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

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    v
}

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
    let mut total = 0usize;

    let mut emit = |arr: Vec<i32>, d: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}:{}", arr, d);
        if !seen.insert(key) { return; }
        let result = Solution::max_jumps(arr.clone(), d);
        writeln!(out, "{}", json!({
            "input": {"arr": arr, "d": d},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![6, 4, 14, 6, 8, 13, 9, 7, 10, 6, 12], 2),
        (vec![3, 3, 3, 3, 3], 3),
        (vec![7, 6, 5, 4, 3, 2, 1], 1),
    ];
    for (arr, d) in examples {
        emit(arr, d, &mut seen, &mut out, &mut total);
    }

    // Edge case seeds
    let edge_seeds: Vec<(Vec<i32>, i32)> = vec![
        (vec![1], 1),
        (vec![1, 2], 1),
        (vec![2, 1], 1),
        (vec![1, 2], 2),
        (vec![2, 1], 2),
        (vec![1, 1, 1], 1),
        (vec![3, 2, 1], 1),
        (vec![1, 2, 3], 1),
        (vec![3, 1, 2], 1),
        (vec![5, 1, 5, 1, 5], 1),
        (vec![5, 1, 5, 1, 5], 2),
        (vec![5, 1, 5, 1, 5], 5),
        (vec![100_000], 1),
        (vec![1, 100_000, 1], 2),
        (vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1], 1),
        (vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1], 5),
        (vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1], 10),
        (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 1),
        (vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10], 10),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];

    // Apply every mutation to every edge seed
    for (arr, d) in &edge_seeds {
        for &mk in &mutation_kinds {
            let (a, d_out) = generate_test_case(arr.clone(), *d, mk);
            emit(a, d_out, &mut seen, &mut out, &mut total);
        }
    }

    // Random test cases with diverse sizes
    while total < count {
        let n: usize = match total % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 20),      // small
            2 => rng.gen_range_usize(21, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 1000),  // max
        };
        let arr = random_arr(&mut rng, n);
        let d = rng.gen_range_i64(1, n as i64) as i32;
        let mk = rng.gen_range_usize(0, 9) as u8;
        let (a, d_out) = generate_test_case(arr, d, mk);
        emit(a, d_out, &mut seen, &mut out, &mut total);
    }
}
