use vstd::prelude::*;

verus! {

pub fn generate_test_case(arr: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= arr.len() <= 100_000,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000_000_000,
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
        // set last element to max boundary
        let mut a = arr;
        let last = a.len() - 1;
        a.set(last, 1_000_000_000);
        a
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut a = arr;
        a.set(0, 0);
        a
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> a[j] == 0,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 0);
            i += 1;
        }
        a
    } else if mutation_kind == 5 && arr.len() < 100_000 {
        // grow by one element (push 0)
        let mut a = arr;
        a.push(0);
        a
    } else if mutation_kind == 6 && arr.len() > 1 {
        // shrink by one element (pop)
        let mut a = arr;
        a.pop();
        a
    } else if mutation_kind == 7 && arr.len() >= 2 {
        // swap first and last elements
        let mut a = arr;
        let last = a.len() - 1;
        let first_val = a[0];
        let last_val = a[last];
        a.set(0, last_val);
        a.set(last, first_val);
        a
    } else if mutation_kind == 8 {
        // set all elements to max boundary
        let mut a = arr;
        let mut i: usize = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                a.len() == arr.len(),
                1 <= a.len() <= 100_000,
                forall|j: int| 0 <= j < i ==> a[j] == 1_000_000_000,
                forall|j: int| i <= j < a.len() ==> a[j] == arr[j],
            decreases a.len() - i,
        {
            a.set(i, 1_000_000_000);
            i += 1;
        }
        a
    } else if mutation_kind == 9 {
        // nudge last element up by 1 if possible
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] < 1_000_000_000 {
            a.set(last, a[last] + 1);
        }
        a
    } else if mutation_kind == 10 {
        // nudge last element down by 1 if possible
        let mut a = arr;
        let last = a.len() - 1;
        if a[last] > 0 {
            a.set(last, a[last] - 1);
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

fn mutate(arr: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(arr, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    arr
}

fn sorted_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    let mut cur: i64 = rng.gen_range_i64(0, 100);
    for _ in 0..len {
        arr.push(cur as i32);
        cur += rng.gen_range_i64(0, 10);
        if cur > 1_000_000_000 {
            cur = 1_000_000_000;
        }
    }
    arr
}

fn reverse_sorted_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut arr = sorted_arr(rng, len);
    arr.reverse();
    arr
}

fn sorted_with_dip(rng: &mut Rng, len: usize) -> Vec<i32> {
    // Create sorted, then insert an unsorted middle section
    let mut arr = sorted_arr(rng, len);
    if len >= 3 {
        let dip_start = len / 3;
        let dip_end = 2 * len / 3;
        // Set middle portion to random (lower) values
        for i in dip_start..dip_end {
            arr[i] = rng.gen_range_i64(0, arr[dip_start.saturating_sub(1).max(0)] as i64) as i32;
        }
    }
    arr
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1574);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |arr: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, n: &mut usize| {
        if *n >= count {
            return;
        }
        let key = format!("{:?}", arr);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_length_of_shortest_subarray(arr.clone());
        writeln!(out, "{}", json!({"input": {"arr": arr}, "output": output})).unwrap();
        *n += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 10, 4, 2, 3, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 2, 3],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

    // Apply every mutation to example inputs
    for ex in &examples {
        for &mk in &mutation_kinds {
            emit(mutate(ex.clone(), mk), &mut seen, &mut out, &mut n);
        }
    }

    // Interesting seed arrays
    let seeds: Vec<Vec<i32>> = vec![
        vec![0],                                    // single element, min value
        vec![1_000_000_000],                        // single element, max value
        vec![0, 0],                                 // two equal min
        vec![0, 1_000_000_000],                     // two elements, sorted
        vec![1_000_000_000, 0],                     // two elements, reversed
        vec![1, 3, 2, 4],                           // small dip
        vec![1, 2, 5, 3, 4, 6],                     // dip in middle
        vec![2, 1, 3, 4, 5],                        // dip at start
        vec![1, 2, 3, 4, 2],                        // dip at end
        vec![1, 1, 1, 1, 1],                        // all equal
    ];

    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            emit(mutate(seed_arr.clone(), mk), &mut seen, &mut out, &mut n);
        }
    }

    // Random arrays across size classes with random mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 5),         // tiny
        (6, 20),        // small
        (21, 100),      // medium
        (101, 1000),    // large
        (1001, 10000),  // xlarge
    ];

    for (lo, hi) in &size_classes {
        for _ in 0..4 {
            let len = rng.gen_range_usize(*lo, *hi);
            let arr = random_arr(&mut rng, len);
            let mk = rng.gen_range_usize(0, 10) as u8;
            emit(mutate(arr, mk), &mut seen, &mut out, &mut n);
        }
    }

    // Sorted arrays (edge: already sorted → answer 0)
    for (lo, hi) in &size_classes {
        let len = rng.gen_range_usize(*lo, *hi);
        let arr = sorted_arr(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut n);
    }

    // Reverse sorted arrays (edge: answer = len - 1)
    for (lo, hi) in &size_classes {
        let len = rng.gen_range_usize(*lo, *hi);
        let arr = reverse_sorted_arr(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut n);
    }

    // Sorted with dip in middle
    for (lo, hi) in &size_classes {
        let len = rng.gen_range_usize((*lo).max(3), *hi);
        let arr = sorted_with_dip(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut n);
    }

    // Fill remaining with random arrays, identity mutation
    while n < count {
        let len = rng.gen_range_usize(1, 10000);
        let arr = random_arr(&mut rng, len);
        emit(mutate(arr, 0), &mut seen, &mut out, &mut n);
    }
}
