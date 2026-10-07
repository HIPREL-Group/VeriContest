use vstd::prelude::*;

verus! {

pub fn generate_test_case(triangle: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        1 <= triangle.len() <= 200,
        triangle[0].len() == 1,
        forall|row: int| 0 <= row < triangle.len() ==> #[trigger] triangle[row].len() == row + 1,
        forall|row: int, col: int|
            0 <= row < triangle.len() && 0 <= col < triangle[row].len() ==> -10000 <= #[trigger] triangle[row][col] <= 10000,
    ensures
        1 <= result.len() <= 200,
        result[0].len() == 1,
        forall|row: int| 0 <= row < result.len() ==> #[trigger] result[row].len() == row + 1,
        forall|row: int, col: int|
            0 <= row < result.len() && 0 <= col < result[row].len() ==> -10000 <= #[trigger] result[row][col] <= 10000,
{
    if mutation_kind == 0 {
        // identity
        triangle
    } else if mutation_kind == 1 {
        // negate top element
        let val = triangle[0][0];
        let mut new_row0: Vec<i32> = Vec::new();
        new_row0.push(-val);
        assert(-10000 <= -val <= 10000);
        let mut t = triangle;
        t.set(0, new_row0);
        assert(t[0].len() == 1);
        t
    } else if mutation_kind == 2 {
        // set top to 0
        let mut new_row0: Vec<i32> = Vec::new();
        new_row0.push(0i32);
        let mut t = triangle;
        t.set(0, new_row0);
        t
    } else if mutation_kind == 3 {
        // set top to -10000
        let mut new_row0: Vec<i32> = Vec::new();
        new_row0.push(-10000i32);
        let mut t = triangle;
        t.set(0, new_row0);
        t
    } else if mutation_kind == 4 {
        // set top to 10000
        let mut new_row0: Vec<i32> = Vec::new();
        new_row0.push(10000i32);
        let mut t = triangle;
        t.set(0, new_row0);
        t
    } else if mutation_kind == 5 {
        // replace last row with all zeros
        let n = triangle.len();
        let mut new_last: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                new_last.len() == i as int,
                1 <= n <= 200,
                forall|j: int| 0 <= j < i as int ==> new_last[j] == 0i32,
            decreases n - i,
        {
            new_last.push(0i32);
            i += 1;
        }
        assert(new_last.len() == n);
        let mut t = triangle;
        t.set(n - 1, new_last);
        assert(t[n - 1 as int].len() == n);
        t
    } else if mutation_kind == 6 {
        // replace last row with all 10000
        let n = triangle.len();
        let mut new_last: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                new_last.len() == i as int,
                1 <= n <= 200,
                forall|j: int| 0 <= j < i as int ==> new_last[j] == 10000i32,
            decreases n - i,
        {
            new_last.push(10000i32);
            i += 1;
        }
        let mut t = triangle;
        t.set(n - 1, new_last);
        t
    } else if mutation_kind == 7 {
        // replace last row with all -10000
        let n = triangle.len();
        let mut new_last: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                new_last.len() == i as int,
                1 <= n <= 200,
                forall|j: int| 0 <= j < i as int ==> new_last[j] == -10000i32,
            decreases n - i,
        {
            new_last.push(-10000i32);
            i += 1;
        }
        let mut t = triangle;
        t.set(n - 1, new_last);
        t
    } else {
        // fallback: identity
        triangle
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

extern crate serde_json;
use serde_json::json;

fn random_triangle(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut triangle = Vec::with_capacity(n);
    for row in 0..n {
        let mut r = Vec::with_capacity(row + 1);
        for _ in 0..=row {
            r.push(rng.gen_range_i64(-10000, 10000) as i32);
        }
        triangle.push(r);
    }
    triangle
}

fn mutate(triangle: Vec<Vec<i32>>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(triangle, mutation_kind)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(120);
    let count_target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |triangle: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= count_target {
            return;
        }
        let key = format!("{:?}", triangle);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::minimum_total(triangle.clone());
        writeln!(out, "{}", json!({"input": {"triangle": triangle}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example1: Vec<Vec<i32>> = vec![vec![2], vec![3, 4], vec![6, 5, 7], vec![4, 1, 8, 3]];
    let example2: Vec<Vec<i32>> = vec![vec![-10]];

    let seeds: Vec<Vec<Vec<i32>>> = vec![
        example1,
        example2,
        vec![vec![0]],
        vec![vec![1], vec![2, 3]],
        vec![vec![10000]],
        vec![vec![-10000]],
        vec![vec![0], vec![0, 0], vec![0, 0, 0]],
        vec![vec![1], vec![-1, 1], vec![1, -1, 1]],
        vec![vec![5], vec![3, 7], vec![1, 2, 4], vec![8, 6, 9, 3]],
        vec![vec![-1], vec![-2, -3], vec![-4, -5, -6]],
        vec![vec![10000], vec![-10000, 10000]],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random triangles with diverse sizes and random mutations
    for i in 0..200 {
        if count >= count_target {
            break;
        }
        let n = match i % 5 {
            0 => rng.gen_range_usize(1, 3),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 100),     // large
            _ => rng.gen_range_usize(101, 200),    // max
        };
        let tri = random_triangle(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(tri, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < count_target {
        let n = rng.gen_range_usize(1, 200);
        let tri = random_triangle(&mut rng, n);
        emit(mutate(tri, 0), &mut seen, &mut out, &mut count);
    }
}
