use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 10_000,
        forall|k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
    ensures
        1 <= result.len() <= 10_000,
        forall|k: int| 0 <= k < result.len() ==> 0 <= #[trigger] result[k] <= 10_000,
{
    if mutation_kind == 0 {
        // identity
        arr
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = arr;
        d.set(0, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 0
        let mut d = arr;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 3 {
        // set first element to 10_000
        let mut d = arr;
        d.set(0, 10_000);
        d
    } else if mutation_kind == 4 && arr.len() < 10_000 {
        // grow by one element (push 0)
        let mut d = arr;
        d.push(0);
        d
    } else if mutation_kind == 5 && arr.len() > 1 {
        // shrink by one element (pop)
        let mut d = arr;
        d.pop();
        d
    } else if mutation_kind == 6 {
        // nudge first element up: if < 10_000, increment
        let mut d = arr;
        if d[0] < 10_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 7 {
        // nudge last element down: if > 0, decrement
        let mut d = arr;
        let last = d.len() - 1;
        if d[last] > 0 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 {
        // set all elements to 5 (flat array, not a mountain)
        let mut d = arr;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == arr.len(),
                1 <= d.len() <= 10_000,
                forall|j: int| 0 <= j < i ==> d[j] == 5,
                forall|j: int| i <= j < d.len() ==> d[j] == arr[j],
            decreases d.len() - i,
        {
            d.set(i, 5);
            i += 1;
        }
        d
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

fn make_mountain(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Build a valid mountain array of length n (n >= 3)
    let peak_idx = rng.gen_range_usize(1, n - 2);
    let mut arr = Vec::with_capacity(n);
    // Ascending part: 0..=peak_idx strictly increasing
    let mut val = rng.gen_range_i64(0, 5000) as i32;
    arr.push(val);
    for _ in 1..=peak_idx {
        let step = rng.gen_range_i64(1, 100) as i32;
        val = (val + step).min(10_000);
        arr.push(val);
    }
    // Descending part: peak_idx+1..n strictly decreasing
    for _ in (peak_idx + 1)..n {
        let step = rng.gen_range_i64(1, 100) as i32;
        val = (val - step).max(0);
        arr.push(val);
    }
    arr
}

fn make_random_arr(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(n);
    for _ in 0..n {
        arr.push(rng.gen_range_i64(0, 10_000) as i32);
    }
    arr
}

fn make_ascending(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(n);
    let mut val = rng.gen_range_i64(0, 100) as i32;
    for _ in 0..n {
        arr.push(val);
        val = (val + rng.gen_range_i64(1, 50) as i32).min(10_000);
    }
    arr
}

fn make_descending(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(n);
    let mut val = rng.gen_range_i64(9000, 10_000) as i32;
    for _ in 0..n {
        arr.push(val);
        val = (val - rng.gen_range_i64(1, 50) as i32).max(0);
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(941);
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
        let output = Solution::valid_mountain_array(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![2, 1],
        vec![3, 5, 5],
        vec![0, 3, 2, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    // Apply all mutations to examples
    for ex in &examples {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    // Edge case seeds
    let edge_cases: Vec<Vec<i32>> = vec![
        vec![1],                             // length 1
        vec![1, 2],                          // length 2, ascending
        vec![2, 1],                          // length 2, descending
        vec![0, 1, 0],                       // minimal mountain
        vec![0, 10_000, 0],                  // mountain with max peak
        vec![5, 5, 5],                       // flat
        vec![1, 2, 3],                       // only ascending
        vec![3, 2, 1],                       // only descending
        vec![1, 3, 2, 2],                    // plateau on descent
        vec![1, 1, 3, 2],                    // plateau on ascent
        vec![0, 0, 0, 0],                    // all zeros
        vec![10_000, 10_000, 10_000],        // all max
    ];

    for ex in &edge_cases {
        for &mk in &mutation_kinds {
            let result = mutate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    // Generate mountains of various sizes
    let sizes = [3, 4, 5, 10, 50, 100, 500, 1000];
    for &n in &sizes {
        let arr = make_mountain(&mut rng, n);
        for &mk in &mutation_kinds {
            let result = mutate(arr.clone(), mk);
            emit(result, &mut seen, &mut out, &mut emitted);
        }
    }

    // Random arrays with various structures
    for _ in 0..20 {
        let n = rng.gen_range_usize(1, 200);
        let kind = rng.gen_range_usize(0, 3);
        let arr = match kind {
            0 => make_random_arr(&mut rng, n),
            1 => if n >= 3 { make_mountain(&mut rng, n) } else { make_random_arr(&mut rng, n) },
            2 => make_ascending(&mut rng, n),
            _ => make_descending(&mut rng, n),
        };
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(arr, mk);
        emit(result, &mut seen, &mut out, &mut emitted);
    }

    // Fill remaining with random arrays, identity mutation
    while emitted < count {
        let n = rng.gen_range_usize(1, 500);
        let arr = make_random_arr(&mut rng, n);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut emitted);
    }
}
