use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 500,
        forall|i: int| 0 <= i < result.len() ==> -1000 <= #[trigger] result[i] <= 1000,
{
    let n = if values.len() == 0 { 1usize } else if values.len() > 500 { 500usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 500, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> -1000 <= #[trigger] result[j] <= 1000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { -1000 };
        result.push(if value < -1000 { -1000 } else if value > 1000 { 1000 } else { value });
        i += 1;
    }
    result
}

pub fn generate_test_case(arr1: Vec<i32>, arr2: Vec<i32>, d: i32) -> (result: (Vec<i32>, Vec<i32>, i32))
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1.len() <= 500,
        0 <= result.2 <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
        forall|i: int| 0 <= i < result.1.len() ==> -1000 <= #[trigger] result.1[i] <= 1000,
{
    (bounded_values(&arr1), bounded_values(&arr2), if d < 0 { 0 } else if d > 100 { 100 } else { d })
}


pub fn generate_candidate(
    arr1: Vec<i32>,
    arr2: Vec<i32>,
    d: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= arr1.len() <= 500,
        1 <= arr2.len() <= 500,
        0 <= d <= 100,
        forall|i: int| 0 <= i < arr1.len() ==> -1000 <= #[trigger] arr1[i] <= 1000,
        forall|j: int| 0 <= j < arr2.len() ==> -1000 <= #[trigger] arr2[j] <= 1000,
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1.len() <= 500,
        0 <= result.2 <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> -1000 <= #[trigger] result.0[i] <= 1000,
        forall|j: int| 0 <= j < result.1.len() ==> -1000 <= #[trigger] result.1[j] <= 1000,
{
    if mutation_kind == 0 {
        // identity
        (arr1, arr2, d)
    } else if mutation_kind == 1 {
        // set last element of arr1 to -1000 (min boundary)
        let mut a1 = arr1;
        let last = a1.len() - 1;
        a1.set(last, -1000);
        (a1, arr2, d)
    } else if mutation_kind == 2 {
        // set last element of arr1 to 1000 (max boundary)
        let mut a1 = arr1;
        let last = a1.len() - 1;
        a1.set(last, 1000);
        (a1, arr2, d)
    } else if mutation_kind == 3 {
        // set last element of arr2 to -1000 (min boundary)
        let mut a2 = arr2;
        let last = a2.len() - 1;
        a2.set(last, -1000);
        (arr1, a2, d)
    } else if mutation_kind == 4 {
        // set last element of arr2 to 1000 (max boundary)
        let mut a2 = arr2;
        let last = a2.len() - 1;
        a2.set(last, 1000);
        (arr1, a2, d)
    } else if mutation_kind == 5 {
        // set d to 0 (minimum distance)
        (arr1, arr2, 0)
    } else if mutation_kind == 6 {
        // set d to 100 (maximum distance)
        (arr1, arr2, 100)
    } else if mutation_kind == 7 {
        // set all arr1 elements to 0
        let mut a1 = arr1;
        let mut i: usize = 0;
        while i < a1.len()
            invariant
                0 <= i <= a1.len(),
                a1.len() == arr1.len(),
                1 <= a1.len() <= 500,
                forall|j: int| 0 <= j < i ==> a1[j] == 0int,
                forall|j: int| i <= j < a1.len() ==> a1[j] == arr1[j],
            decreases a1.len() - i,
        {
            a1.set(i, 0);
            i += 1;
        }
        (a1, arr2, d)
    } else if mutation_kind == 8 {
        // set all arr2 elements to 0
        let mut a2 = arr2;
        let mut i: usize = 0;
        while i < a2.len()
            invariant
                0 <= i <= a2.len(),
                a2.len() == arr2.len(),
                1 <= a2.len() <= 500,
                forall|j: int| 0 <= j < i ==> a2[j] == 0int,
                forall|j: int| i <= j < a2.len() ==> a2[j] == arr2[j],
            decreases a2.len() - i,
        {
            a2.set(i, 0);
            i += 1;
        }
        (arr1, a2, d)
    } else if mutation_kind == 9 && arr1.len() < 500 {
        // grow arr1 by one element
        let mut a1 = arr1;
        a1.push(0);
        (a1, arr2, d)
    } else if mutation_kind == 10 && arr2.len() < 500 {
        // grow arr2 by one element
        let mut a2 = arr2;
        a2.push(0);
        (arr1, a2, d)
    } else if mutation_kind == 11 && arr1.len() > 1 {
        // shrink arr1 by one element
        let mut a1 = arr1;
        a1.pop();
        (a1, arr2, d)
    } else if mutation_kind == 12 && arr2.len() > 1 {
        // shrink arr2 by one element
        let mut a2 = arr2;
        a2.pop();
        (arr1, a2, d)
    } else if mutation_kind == 13 {
        // nudge d up by 1 if possible
        if d < 100 {
            (arr1, arr2, d + 1)
        } else {
            (arr1, arr2, d)
        }
    } else if mutation_kind == 14 {
        // nudge d down by 1 if possible
        if d > 0 {
            (arr1, arr2, d - 1)
        } else {
            (arr1, arr2, d)
        }
    } else if mutation_kind == 15 && arr1.len() >= 2 {
        // swap first two elements of arr1
        let mut a1 = arr1;
        let tmp = a1[0];
        a1.set(0, a1[1]);
        a1.set(1, tmp);
        (a1, arr2, d)
    } else if mutation_kind == 16 {
        // nudge last arr1 element up
        let mut a1 = arr1;
        let last = a1.len() - 1;
        if a1[last] < 1000 {
            a1.set(last, a1[last] + 1);
        }
        (a1, arr2, d)
    } else if mutation_kind == 17 {
        // nudge last arr2 element down
        let mut a2 = arr2;
        let last = a2.len() - 1;
        if a2[last] > -1000 {
            a2.set(last, a2[last] - 1);
        }
        (arr1, a2, d)
    } else {
        // fallback
        (arr1, arr2, d)
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

fn mutate(arr1: Vec<i32>, arr2: Vec<i32>, d: i32, mutation_kind: u8) -> (Vec<i32>, Vec<i32>, i32) {
    generate_candidate(arr1, arr2, d, mutation_kind)
}

fn random_arr(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut a = Vec::with_capacity(len);
    for _ in 0..len {
        a.push(rng.gen_range_i64(-1000, 1000) as i32);
    }
    a
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

    let mut emit = |arr1: Vec<i32>, arr2: Vec<i32>, d: i32, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let (arr1, arr2, d) = generate_test_case(arr1, arr2, d);
        if *count >= target {
            return;
        }
        let key = format!("{:?}|{:?}|{}", arr1, arr2, d);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::find_the_distance_value(arr1.clone(), arr2.clone(), d);
        writeln!(out, "{}", json!({"input": {"arr1": arr1, "arr2": arr2, "d": d}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![4, 5, 8], vec![10, 9, 1, 8], 2),
        (vec![1, 4, 2, 3], vec![-4, -3, 6, 10, 20, 30], 3),
        (vec![2, 1, 100, 3], vec![-5, -2, 10, -3, 7], 6),
    ];

    // Boundary/special seeds
    let special_seeds: Vec<(Vec<i32>, Vec<i32>, i32)> = vec![
        (vec![0], vec![0], 0),
        (vec![1000], vec![-1000], 100),
        (vec![-1000], vec![1000], 0),
        (vec![0, 0, 0], vec![0, 0, 0], 50),
        (vec![500, -500], vec![500, -500], 100),
        (vec![1000, -1000], vec![0], 999),
    ];

    let mutation_kinds: Vec<u8> = (0..=17).collect();

    // Apply every mutation to examples
    for (a1, a2, d) in &examples {
        for &mk in &mutation_kinds {
            let (r1, r2, rd) = mutate(a1.clone(), a2.clone(), *d, mk);
            emit(r1, r2, rd, &mut seen, &mut out, &mut count);
        }
    }

    // Apply some mutations to special seeds
    for (a1, a2, d) in &special_seeds {
        for &mk in &[0u8, 1, 2, 5, 6, 7, 8] {
            let (r1, r2, rd) = mutate(a1.clone(), a2.clone(), *d, mk);
            emit(r1, r2, rd, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with random mutations across size classes
    for i in 0..80 {
        let len1 = match i % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 500),
        };
        let len2 = match i % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 200),
            _ => rng.gen_range_usize(201, 500),
        };
        let a1 = random_arr(&mut rng, len1);
        let a2 = random_arr(&mut rng, len2);
        let d = if i % 5 == 0 {
            *[0i32, 100, 1, 50].get(i % 4).unwrap_or(&0)
        } else {
            rng.gen_range_i64(0, 100) as i32
        };
        let mk = rng.gen_range_usize(0, 17) as u8;
        let (r1, r2, rd) = mutate(a1, a2, d, mk);
        emit(r1, r2, rd, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random seeds, identity mutation
    while count < target {
        let len1 = rng.gen_range_usize(1, 500);
        let len2 = rng.gen_range_usize(1, 500);
        let a1 = random_arr(&mut rng, len1);
        let a2 = random_arr(&mut rng, len2);
        let d = rng.gen_range_i64(0, 100) as i32;
        let (r1, r2, rd) = mutate(a1, a2, d, 0);
        emit(r1, r2, rd, &mut seen, &mut out, &mut count);
    }
}
