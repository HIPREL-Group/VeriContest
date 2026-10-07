use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    range_starts: Vec<i32>,
    range_ends: Vec<i32>,
    left: i32,
    right: i32,
    mutation_kind: u8,
) -> (result: (Vec<Vec<i32>>, i32, i32))
    requires
        1 <= range_starts.len() <= 50,
        range_starts.len() == range_ends.len(),
        forall |j: int| 0 <= j < range_starts.len() ==>
            1 <= #[trigger] range_starts[j] && range_starts[j] <= range_ends[j] && range_ends[j] <= 50,
        1 <= left <= right <= 50,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= result.2 <= 50,
        forall |j: int| 0 <= j < result.0.len() ==> #[trigger] result.0[j]@.len() == 2,
        forall |j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j][0] && result.0[j][0] <= result.0[j][1] && result.0[j][1] <= 50,
{
    let n = range_starts.len();
    let mut ranges: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            i <= n,
            n == range_starts.len(),
            n == range_ends.len(),
            1 <= n <= 50,
            ranges.len() == i as int,
            forall |j: int| 0 <= j < range_starts.len() ==>
                1 <= #[trigger] range_starts[j] && range_starts[j] <= range_ends[j] && range_ends[j] <= 50,
            forall |j: int| 0 <= j < i as int ==> #[trigger] ranges[j]@.len() == 2,
            forall |j: int| 0 <= j < i as int ==>
                1 <= #[trigger] ranges[j][0] && ranges[j][0] <= ranges[j][1] && ranges[j][1] <= 50,
        decreases n - i,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(range_starts[i]);
        pair.push(range_ends[i]);
        assert(pair@.len() == 2);
        assert(pair[0] == range_starts[i as int]);
        assert(pair[1] == range_ends[i as int]);
        ranges.push(pair);
        i += 1;
    }

    if mutation_kind == 1 && ranges.len() < 50 {
        // Grow: add [left, right]
        let mut pair: Vec<i32> = Vec::new();
        pair.push(left);
        pair.push(right);
        assert(pair@.len() == 2);
        assert(pair[0] == left);
        assert(pair[1] == right);
        ranges.push(pair);
        (ranges, left, right)
    } else if mutation_kind == 2 && ranges.len() > 1 {
        // Shrink: remove last range
        ranges.pop();
        (ranges, left, right)
    } else if mutation_kind == 3 && left < right {
        // Nudge left up
        (ranges, left + 1, right)
    } else if mutation_kind == 4 && left < right {
        // Nudge right down
        (ranges, left, right - 1)
    } else if mutation_kind == 5 {
        // Set left to minimum
        (ranges, 1i32, right)
    } else if mutation_kind == 6 {
        // Set right to maximum
        (ranges, left, 50i32)
    } else if mutation_kind == 7 {
        // Single point query: left = right
        (ranges, left, left)
    } else {
        // Identity / fallback
        (ranges, left, right)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn build_and_emit(
    range_starts: Vec<i32>,
    range_ends: Vec<i32>,
    left: i32,
    right: i32,
    mutation_kind: u8,
    seen: &mut std::collections::HashSet<String>,
    out: &mut std::io::BufWriter<std::fs::File>,
    emitted: &mut usize,
    target_count: usize,
) {
    if *emitted >= target_count {
        return;
    }
    let (ranges, l, r) = generate_test_case(range_starts, range_ends, left, right, mutation_kind);
    let key = format!("{:?},{},{}", ranges, l, r);
    if !seen.insert(key) {
        return;
    }
    let output = Solution::is_covered(ranges.clone(), l, r);
    writeln!(
        out,
        "{}",
        json!({"input": {"ranges": ranges, "left": l, "right": r}, "output": output})
    )
    .unwrap();
    *emitted += 1;
}

use std::io::Write;

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!())
        .parent()
        .unwrap()
        .join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = std::collections::HashSet::new();
    let mut emitted = 0usize;

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // ---- LeetCode examples ----
    // Example 1: ranges = [[1,2],[3,4],[5,6]], left = 2, right = 5 → true
    for &mk in &mutation_kinds {
        build_and_emit(
            vec![1, 3, 5], vec![2, 4, 6], 2, 5, mk,
            &mut seen, &mut out, &mut emitted, count,
        );
    }
    // Example 2: ranges = [[1,10],[10,20]], left = 21, right = 21 → false
    for &mk in &mutation_kinds {
        build_and_emit(
            vec![1, 10], vec![10, 20], 21, 21, mk,
            &mut seen, &mut out, &mut emitted, count,
        );
    }

    // ---- Fixed seed configurations with all mutations ----
    let configs: Vec<(Vec<i32>, Vec<i32>, i32, i32)> = vec![
        // Single full-coverage range
        (vec![1], vec![50], 1, 50),
        // Single point range and query
        (vec![25], vec![25], 25, 25),
        // Multiple contiguous ranges
        (vec![1, 6, 11], vec![5, 10, 15], 1, 15),
        // Overlapping ranges
        (vec![1, 3, 5], vec![4, 7, 10], 1, 10),
        // Gap in coverage
        (vec![1, 10], vec![5, 15], 1, 15),
        // Boundary: query at range boundary
        (vec![1], vec![50], 50, 50),
        (vec![1], vec![50], 1, 1),
        // Many small ranges
        (vec![1, 2, 3, 4, 5], vec![1, 2, 3, 4, 5], 1, 5),
        // Single range, wide query
        (vec![10], vec![20], 5, 25),
        // All ranges at same position
        (vec![25, 25, 25], vec![25, 25, 25], 25, 25),
    ];

    for (starts, ends, l, r) in &configs {
        for &mk in &mutation_kinds {
            build_and_emit(
                starts.clone(), ends.clone(), *l, *r, mk,
                &mut seen, &mut out, &mut emitted, count,
            );
        }
    }

    // ---- Random test cases ----
    while emitted < count {
        // Size classes for number of ranges
        let n = match rng.gen_range_usize(0, 4) {
            0 => 1,                              // single range
            1 => rng.gen_range_usize(2, 5),      // small
            2 => rng.gen_range_usize(6, 20),     // medium
            3 => rng.gen_range_usize(21, 50),    // large
            _ => rng.gen_range_usize(1, 50),     // any
        };

        let mut starts = Vec::with_capacity(n);
        let mut ends = Vec::with_capacity(n);
        for _ in 0..n {
            let a = rng.gen_range_i64(1, 50) as i32;
            let b = rng.gen_range_i64(1, 50) as i32;
            starts.push(a.min(b));
            ends.push(a.max(b));
        }

        let l = rng.gen_range_i64(1, 50) as i32;
        let r_val = rng.gen_range_i64(l as i64, 50) as i32;
        let mk = rng.gen_range_usize(0, 7) as u8;

        build_and_emit(
            starts, ends, l, r_val, mk,
            &mut seen, &mut out, &mut emitted, count,
        );
    }
}
