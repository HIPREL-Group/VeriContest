use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    d: usize,
    sum_time: i32,
    min_vals: Vec<i32>,
    gap_vals: Vec<i32>,
    mutation_kind: u8,
) -> (result: (usize, i32, Vec<i32>, Vec<i32>))
    requires
        1 <= d <= 30,
        d == min_vals.len(),
        d == gap_vals.len(),
        0 <= sum_time <= 240,
        forall|i: int| 0 <= i < d as int ==> 0 <= #[trigger] min_vals@[i] <= 8,
        forall|i: int| 0 <= i < d as int ==> 0 <= #[trigger] gap_vals@[i] <= 8,
    ensures
        (result.0 as int) >= 1 && (result.0 as int) <= 30,
        result.0 == result.2.len(),
        result.0 == result.3.len(),
        0 <= result.1 <= 240,
        forall|i: int|
            0 <= i < result.0 as int ==> 0 <= (#[trigger] result.2@[i] as int) && (result.2@[i] as int) <= (result.3@[i] as int)
                && (result.3@[i] as int) <= 8,
{
    if mutation_kind == 1 {
        // Tight bounds: max_t == min_t for all days
        let mut tight_max: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < d
            invariant
                0 <= idx <= d,
                1 <= d <= 30,
                d == min_vals.len(),
                tight_max.len() == idx,
                forall|j: int| 0 <= j < idx as int ==>
                    (#[trigger] tight_max@[j] as int) == (min_vals@[j] as int),
                forall|i: int| 0 <= i < d as int ==> 0 <= #[trigger] min_vals@[i] <= 8,
            decreases d - idx,
        {
            tight_max.push(min_vals[idx]);
            idx = idx + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < d as int implies
                0 <= (#[trigger] min_vals@[i] as int) && (min_vals@[i] as int) <= (tight_max@[i] as int)
                && (tight_max@[i] as int) <= 8
            by {
                assert(tight_max@[i] == min_vals@[i]);
            };
        }
        return (d, sum_time, min_vals, tight_max);
    }

    if mutation_kind == 2 {
        // Wide bounds: min=0, max=8 for all days
        let mut zero_min: Vec<i32> = Vec::new();
        let mut full_max: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < d
            invariant
                0 <= idx <= d,
                1 <= d <= 30,
                zero_min.len() == idx,
                full_max.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] zero_min@[j]) == 0i32,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] full_max@[j]) == 8i32,
            decreases d - idx,
        {
            zero_min.push(0i32);
            full_max.push(8i32);
            idx = idx + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < d as int implies
                0 <= (#[trigger] zero_min@[i] as int) && (zero_min@[i] as int) <= (full_max@[i] as int)
                && (full_max@[i] as int) <= 8
            by {
                assert(zero_min@[i] == 0i32);
                assert(full_max@[i] == 8i32);
            };
        }
        return (d, sum_time, zero_min, full_max);
    }

    if mutation_kind == 3 {
        // All max: min=8, max=8 for all days
        let mut all_eight: Vec<i32> = Vec::new();
        let mut all_eight_max: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < d
            invariant
                0 <= idx <= d,
                1 <= d <= 30,
                all_eight.len() == idx,
                all_eight_max.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] all_eight@[j]) == 8i32,
                forall|j: int| 0 <= j < idx as int ==> (#[trigger] all_eight_max@[j]) == 8i32,
            decreases d - idx,
        {
            all_eight.push(8i32);
            all_eight_max.push(8i32);
            idx = idx + 1;
        }
        proof {
            assert forall|i: int| 0 <= i < d as int implies
                0 <= (#[trigger] all_eight@[i] as int) && (all_eight@[i] as int) <= (all_eight_max@[i] as int)
                && (all_eight_max@[i] as int) <= 8
            by {
                assert(all_eight@[i] == 8i32);
                assert(all_eight_max@[i] == 8i32);
            };
        }
        return (d, sum_time, all_eight, all_eight_max);
    }

    // Default (mutation_kind == 0 or fallback): construct max_t = min(min_vals[i] + gap_vals[i], 8)
    let mut max_t: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < d
        invariant
            0 <= idx <= d,
            1 <= d <= 30,
            d == min_vals.len(),
            d == gap_vals.len(),
            max_t.len() == idx,
            forall|j: int| 0 <= j < idx as int ==>
                (min_vals@[j] as int) <= (#[trigger] max_t@[j] as int) && (max_t@[j] as int) <= 8,
            forall|i: int| 0 <= i < d as int ==> 0 <= #[trigger] min_vals@[i] <= 8,
            forall|i: int| 0 <= i < d as int ==> 0 <= #[trigger] gap_vals@[i] <= 8,
        decreases d - idx,
    {
        let min_v = min_vals[idx];
        let gap = gap_vals[idx];
        let raw: i32 = min_v + gap;
        let max_v: i32 = if raw > 8 { 8i32 } else { raw };
        max_t.push(max_v);
        idx = idx + 1;
    }

    proof {
        assert forall|i: int| 0 <= i < d as int implies
            0 <= (#[trigger] min_vals@[i] as int) && (min_vals@[i] as int) <= (max_t@[i] as int)
            && (max_t@[i] as int) <= 8
        by {};
    }

    (d, sum_time, min_vals, max_t)
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

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
    let mut generated = 0usize;

    let mut emit = |d: usize, sum_time: i32, min_t: Vec<i32>, max_t: Vec<i32>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    generated: &mut usize| {
        if *generated >= count { return; }
        let key = format!("{}:{}:{:?}:{:?}", d, sum_time, min_t, max_t);
        if !seen.insert(key) { return; }
        let (feasible, schedule) = Solution::before_exam_schedule(
            d, sum_time, min_t.clone(), max_t.clone(),
        );
        writeln!(out, "{}", json!({
            "input": {"d": d, "sum_time": sum_time, "min_t": min_t, "max_t": max_t},
            "output": {"feasible": feasible, "schedule": schedule}
        })).unwrap();
        *generated += 1;
    };

    // Example inputs from description.md
    emit(1, 48, vec![5], vec![7], &mut seen, &mut out, &mut generated);
    emit(2, 5, vec![0, 3], vec![1, 5], &mut seen, &mut out, &mut generated);

    // Boundary: single day
    emit(1, 0, vec![0], vec![0], &mut seen, &mut out, &mut generated);
    emit(1, 8, vec![0], vec![8], &mut seen, &mut out, &mut generated);
    emit(1, 4, vec![4], vec![4], &mut seen, &mut out, &mut generated);

    // Size classes for d
    let d_classes: Vec<(usize, usize)> = vec![
        (1, 1),     // minimal
        (2, 5),     // tiny
        (6, 10),    // small
        (11, 20),   // medium
        (21, 30),   // max
    ];

    // Generate with verified generator across size classes and mutations
    for &(lo, hi) in &d_classes {
        for mk in 0..=3u8 {
            for _ in 0..3 {
                if generated >= count { break; }
                let d = rng.gen_range_usize(lo, hi);
                // Sample sum_time with boundary mixing
                let sum_time = if rng.gen_u8() % 5 == 0 {
                    *[0i32, 1, 120, 239, 240].iter()
                        .nth(rng.gen_range_usize(0, 4)).unwrap()
                } else {
                    rng.gen_range_i64(0, 240) as i32
                };
                // Build min_vals and gap_vals
                let mut min_vals = Vec::new();
                let mut gap_vals = Vec::new();
                for _ in 0..d {
                    min_vals.push(rng.gen_range_i64(0, 8) as i32);
                    gap_vals.push(rng.gen_range_i64(0, 8) as i32);
                }
                let (d_out, st_out, min_t, max_t) =
                    generate_test_case(d, sum_time, min_vals, gap_vals, mk);
                emit(d_out, st_out, min_t, max_t, &mut seen, &mut out, &mut generated);
            }
        }
    }

    // Fill remaining with random parameters
    while generated < count {
        let class = rng.gen_range_usize(0, 4);
        let (lo, hi) = d_classes[class];
        let d = rng.gen_range_usize(lo, hi);
        let sum_time = rng.gen_range_i64(0, 240) as i32;
        let mut min_vals = Vec::new();
        let mut gap_vals = Vec::new();
        for _ in 0..d {
            min_vals.push(rng.gen_range_i64(0, 8) as i32);
            gap_vals.push(rng.gen_range_i64(0, 8) as i32);
        }
        let mk = rng.gen_u8() % 4;
        let (d_out, st_out, min_t, max_t) =
            generate_test_case(d, sum_time, min_vals, gap_vals, mk);
        emit(d_out, st_out, min_t, max_t, &mut seen, &mut out, &mut generated);
    }
}
