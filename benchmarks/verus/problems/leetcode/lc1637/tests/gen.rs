use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    xs: Vec<i32>,
    ys: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        xs.len() == ys.len(),
        2 <= xs.len() <= 100_000,
        forall|i: int| 0 <= i < xs.len() ==> 0 <= #[trigger] xs[i] <= 1_000_000_000i32,
        forall|i: int| 0 <= i < ys.len() ==> 0 <= #[trigger] ys[i] <= 1_000_000_000i32,
    ensures
        2 <= result.len() <= 100_000,
        forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
            result@[i]@.len() == 2,
        forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
            0 <= result@[i]@[0] <= 1_000_000_000,
        forall|i: int| #![trigger result@[i]] 0 <= i < result@.len() ==>
            0 <= result@[i]@[1] <= 1_000_000_000,
{
    let n = xs.len();
    let mut points: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    if mutation_kind == 1 && n >= 3 {
        // Mutation: set all x coords to xs[0] (all same x => max gap = 0)
        let x0 = xs[0];
        while i < n
            invariant
                0 <= i <= n,
                n == xs.len(),
                n == ys.len(),
                points.len() == i,
                2 <= n <= 100_000,
                0 <= x0 <= 1_000_000_000i32,
                forall|j: int| 0 <= j < ys.len() ==> 0 <= #[trigger] ys[j] <= 1_000_000_000i32,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    points@[j]@.len() == 2,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[0] <= 1_000_000_000,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[1] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(x0);
            pt.push(ys[i]);
            assert(pt@.len() == 2);
            assert(0 <= pt@[0] <= 1_000_000_000);
            assert(0 <= pt@[1] <= 1_000_000_000);
            points.push(pt);
            i = i + 1;
        }
        points
    } else if mutation_kind == 2 && n >= 2 {
        // Mutation: swap first two points' x coordinates
        while i < n
            invariant
                0 <= i <= n,
                n == xs.len(),
                n == ys.len(),
                points.len() == i,
                2 <= n <= 100_000,
                forall|j: int| 0 <= j < xs.len() ==> 0 <= #[trigger] xs[j] <= 1_000_000_000i32,
                forall|j: int| 0 <= j < ys.len() ==> 0 <= #[trigger] ys[j] <= 1_000_000_000i32,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    points@[j]@.len() == 2,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[0] <= 1_000_000_000,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[1] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            let x_val = if i == 0 {
                xs[1]
            } else if i == 1 {
                xs[0]
            } else {
                xs[i]
            };
            pt.push(x_val);
            pt.push(ys[i]);
            assert(pt@.len() == 2);
            points.push(pt);
            i = i + 1;
        }
        points
    } else if mutation_kind == 3 {
        // Mutation: set all y coords to 0
        while i < n
            invariant
                0 <= i <= n,
                n == xs.len(),
                n == ys.len(),
                points.len() == i,
                2 <= n <= 100_000,
                forall|j: int| 0 <= j < xs.len() ==> 0 <= #[trigger] xs[j] <= 1_000_000_000i32,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    points@[j]@.len() == 2,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[0] <= 1_000_000_000,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[1] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(0i32);
            assert(pt@.len() == 2);
            points.push(pt);
            i = i + 1;
        }
        points
    } else if mutation_kind == 4 && n > 2 {
        // Mutation: drop last element (shrink by 1)
        let new_n = n - 1;
        while i < new_n
            invariant
                0 <= i <= new_n,
                new_n == n - 1,
                n == xs.len(),
                n == ys.len(),
                points.len() == i,
                2 <= new_n,
                new_n <= 100_000,
                forall|j: int| 0 <= j < xs.len() ==> 0 <= #[trigger] xs[j] <= 1_000_000_000i32,
                forall|j: int| 0 <= j < ys.len() ==> 0 <= #[trigger] ys[j] <= 1_000_000_000i32,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    points@[j]@.len() == 2,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[0] <= 1_000_000_000,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[1] <= 1_000_000_000,
            decreases new_n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(ys[i]);
            assert(pt@.len() == 2);
            points.push(pt);
            i = i + 1;
        }
        points
    } else if mutation_kind == 5 && n < 100_000 {
        // Mutation: duplicate first point (grow by 1)
        while i < n
            invariant
                0 <= i <= n,
                n == xs.len(),
                n == ys.len(),
                points.len() == i,
                2 <= n <= 100_000,
                n < 100_000,
                forall|j: int| 0 <= j < xs.len() ==> 0 <= #[trigger] xs[j] <= 1_000_000_000i32,
                forall|j: int| 0 <= j < ys.len() ==> 0 <= #[trigger] ys[j] <= 1_000_000_000i32,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    points@[j]@.len() == 2,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[0] <= 1_000_000_000,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[1] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(ys[i]);
            assert(pt@.len() == 2);
            points.push(pt);
            i = i + 1;
        }
        // Duplicate first point
        let mut dup: Vec<i32> = Vec::new();
        dup.push(xs[0]);
        dup.push(ys[0]);
        assert(dup@.len() == 2);
        points.push(dup);
        points
    } else {
        // Identity: pair xs[i] with ys[i]
        while i < n
            invariant
                0 <= i <= n,
                n == xs.len(),
                n == ys.len(),
                points.len() == i,
                2 <= n <= 100_000,
                forall|j: int| 0 <= j < xs.len() ==> 0 <= #[trigger] xs[j] <= 1_000_000_000i32,
                forall|j: int| 0 <= j < ys.len() ==> 0 <= #[trigger] ys[j] <= 1_000_000_000i32,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    points@[j]@.len() == 2,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[0] <= 1_000_000_000,
                forall|j: int| #![trigger points@[j]] 0 <= j < i as int ==>
                    0 <= points@[j]@[1] <= 1_000_000_000,
            decreases n - i,
        {
            let mut pt: Vec<i32> = Vec::new();
            pt.push(xs[i]);
            pt.push(ys[i]);
            assert(pt@.len() == 2);
            points.push(pt);
            i = i + 1;
        }
        points
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

fn build_random_coords(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut xs = Vec::with_capacity(n);
    let mut ys = Vec::with_capacity(n);
    for _ in 0..n {
        xs.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
        ys.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    (xs, ys)
}

fn mutate(xs: Vec<i32>, ys: Vec<i32>, mutation_kind: u8) -> Vec<Vec<i32>> {
    generate_test_case(xs, ys, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1637);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |points: Vec<Vec<i32>>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", points);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_width_of_vertical_area(points.clone());
        writeln!(out, "{}", json!({"input": {"points": points}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let example_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![8, 9, 7, 9], vec![7, 9, 4, 7]),           // Example 1: output 1
        (vec![3, 9, 1, 1, 5, 8], vec![1, 0, 0, 4, 3, 8]), // Example 2: output 3
    ];
    for (xs, ys) in &example_seeds {
        for mk in 0..=5u8 {
            let result = mutate(xs.clone(), ys.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Boundary/special seeds
    let special_seeds: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![0, 1_000_000_000], vec![0, 0]),               // max gap possible
        (vec![0, 0], vec![0, 1_000_000_000]),                // same x, different y
        (vec![500_000_000, 500_000_000], vec![0, 1]),         // same x coords
        (vec![0, 1], vec![0, 0]),                             // minimal gap
        (vec![0, 1, 2], vec![0, 0, 0]),                       // consecutive x
        (vec![0, 500_000_000, 1_000_000_000], vec![0, 0, 0]), // evenly spaced
    ];
    for (xs, ys) in &special_seeds {
        for mk in 0..=5u8 {
            let result = mutate(xs.clone(), ys.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Size classes with random values and mutations
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 5),        // tiny
        (6, 20),       // small
        (21, 100),     // medium
        (101, 1000),   // large
        (1001, 5000),  // xlarge
    ];

    for &(lo, hi) in &size_classes {
        for mk in 0..=5u8 {
            if count >= target { break; }
            let n = rng.gen_range_usize(lo, hi);
            let (xs, ys) = build_random_coords(&mut rng, n);
            let result = mutate(xs, ys, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Fill remaining with random sizes and random mutations
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(21, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let (xs, ys) = build_random_coords(&mut rng, n);
        let mk = rng.gen_range_usize(0, 5) as u8;
        let result = mutate(xs, ys, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
