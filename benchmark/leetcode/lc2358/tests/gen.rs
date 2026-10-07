use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 100000 { 100000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(
    // Construction parameters: length and per-element values
    len: usize,
    values: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        1 <= len <= 100000,
        len <= values.len(),
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
{
    // Take the first `len` elements from values
    let mut grades: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < len
        invariant
            0 <= idx <= len,
            len <= values.len(),
            grades.len() == idx,
            1 <= len <= 100000,
            forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
            forall|i: int| 0 <= i < grades.len() ==> 1 <= #[trigger] grades[i] <= 100000,
        decreases len - idx,
    {
        grades.push(values[idx]);
        idx += 1;
    }

    if mutation_kind == 0 {
        // identity
        grades
    } else if mutation_kind == 1 {
        // set last element to 1 (minimum value)
        let last = grades.len() - 1;
        grades.set(last, 1);
        grades
    } else if mutation_kind == 2 {
        // set last element to 100000 (maximum value)
        let last = grades.len() - 1;
        grades.set(last, 100000);
        grades
    } else if mutation_kind == 3 {
        // set all elements to 1
        let mut i: usize = 0;
        while i < grades.len()
            invariant
                0 <= i <= grades.len(),
                grades.len() == len,
                1 <= grades.len() <= 100000,
                forall|j: int| 0 <= j < i ==> grades[j] == 1i32,
                forall|j: int| i <= j < grades.len() ==> 1 <= #[trigger] grades[j] <= 100000,
            decreases grades.len() - i,
        {
            grades.set(i, 1);
            i += 1;
        }
        grades
    } else if mutation_kind == 4 {
        // set all elements to 100000
        let mut i: usize = 0;
        while i < grades.len()
            invariant
                0 <= i <= grades.len(),
                grades.len() == len,
                1 <= grades.len() <= 100000,
                forall|j: int| 0 <= j < i ==> grades[j] == 100000i32,
                forall|j: int| i <= j < grades.len() ==> 1 <= #[trigger] grades[j] <= 100000,
            decreases grades.len() - i,
        {
            grades.set(i, 100000);
            i += 1;
        }
        grades
    } else if mutation_kind == 5 && grades.len() < 100000 {
        // grow by one element
        grades.push(1);
        grades
    } else if mutation_kind == 6 && grades.len() > 1 {
        // shrink by one element
        grades.pop();
        grades
    } else if mutation_kind == 7 {
        // set first element to 1
        grades.set(0, 1);
        grades
    } else if mutation_kind == 8 {
        // set first element to 100000
        grades.set(0, 100000);
        grades
    } else if mutation_kind == 9 {
        // nudge last element: if < 100000, increment by 1
        let last = grades.len() - 1;
        if grades[last] < 100000 {
            grades.set(last, grades[last] + 1);
        }
        grades
    } else {
        // fallback: identity
        grades
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

fn gen(len: usize, values: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_candidate(len, values, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn random_grades(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(1, 100000) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2358);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);
    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |grades: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let grades = generate_test_case(grades);
        if *count >= target { return; }
        let key = format!("{:?}", grades);
        if !seen.insert(key) { return; }
        let output = Solution::maximum_groups(grades.clone());
        writeln!(out, "{}", json!({"input": {"grades": grades}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![10, 6, 12, 7, 3, 5],
        vec![8, 8],
    ];
    for ex in examples {
        for mk in 0..=10u8 {
            let vals = ex.clone();
            let len = vals.len();
            let result = gen(len, vals, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Seed pools: specific interesting lengths
    let seed_lengths: Vec<usize> = vec![1, 2, 3, 5, 6, 10, 15, 21, 50, 100, 1000, 10000, 100000];

    for &slen in &seed_lengths {
        let vals = random_grades(&mut rng, slen);
        for mk in 0..=10u8 {
            let result = gen(slen, vals.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Diverse size classes with random mutations
    for i in 0..60usize {
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 10),        // small
            2 => rng.gen_range_usize(11, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 100000), // max
        };
        let vals = random_grades(&mut rng, n);
        let mk = rng.gen_range_usize(0, 10) as u8;
        let result = gen(n, vals, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random inputs, identity mutation
    while count < target {
        let n = rng.gen_range_usize(1, 100000);
        let vals = random_grades(&mut rng, n);
        emit(gen(n, vals, 0), &mut seen, &mut out, &mut count);
    }
}
