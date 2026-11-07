use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    starts: Vec<i32>,
    gaps: Vec<i32>,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= starts.len() <= 1000,
        starts.len() == gaps.len(),
        forall|i: int| 0 <= i < starts.len() ==> 0 <= #[trigger] starts[i],
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= #[trigger] gaps[i],
        forall|i: int| 0 <= i < starts.len() ==> starts[i] + gaps[i] <= 100_000,
        forall|i: int, j: int| 0 <= i < j < starts.len() ==> starts[i] < starts[j],
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==>
            (#[trigger] result[i]).len() == 2,
        forall|i: int| 0 <= i < result.len() ==>
            0 <= (#[trigger] result[i])[0] < result[i][1] <= 100_000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==>
            !(result[i][0] == result[j][0] && result[i][1] == result[j][1]),
{
    let n = starts.len();
    let mut intervals: Vec<Vec<i32>> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            k <= n,
            n == starts.len(),
            n == gaps.len(),
            1 <= n <= 1000,
            intervals.len() == k,
            forall|i: int| 0 <= i < n as int ==> 0 <= #[trigger] starts[i],
            forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] gaps[i],
            forall|i: int| 0 <= i < n as int ==> starts[i] + gaps[i] <= 100_000,
            forall|i: int, j: int| 0 <= i < j < n as int ==> starts[i] < starts[j],
            forall|i: int| 0 <= i < k as int ==> (#[trigger] intervals[i]).len() == 2,
            forall|i: int| 0 <= i < k as int ==> intervals[i][0] == starts[i],
            forall|i: int| 0 <= i < k as int ==>
                0 <= (#[trigger] intervals[i])[0] < intervals[i][1] <= 100_000,
            forall|i: int, j: int| 0 <= i < j < k as int ==>
                !(intervals[i][0] == intervals[j][0] && intervals[i][1] == intervals[j][1]),
        decreases n - k,
    {
        let s = starts[k];

        // Compute gap based on mutation_kind
        let g: i32 = if mutation_kind == 1 {
            // Narrow: all gaps = 1
            1i32
        } else if mutation_kind == 2 {
            // Wide: extend to 100_000
            (100_000i32 - s)
        } else if mutation_kind == 3 && gaps[k] <= 50_000 && s + gaps[k] * 2 <= 100_000 {
            // Double the gap
            gaps[k] * 2
        } else if mutation_kind == 4 && gaps[k] >= 2 {
            // Halve the gap
            gaps[k] / 2
        } else {
            // Normal (mutation 0, 5+, or fallback)
            gaps[k]
        };

        assert(g >= 1i32);
        assert(s + g <= 100_000i32);

        let mut iv: Vec<i32> = Vec::new();
        iv.push(s);
        iv.push(s + g);

        // Prove uniqueness: starts are strictly increasing,
        // so iv[0] = starts[k] != intervals[j][0] = starts[j] for all j < k
        proof {
            assert forall|j: int| 0 <= j < k as int implies
                !(intervals[j][0] == s && intervals[j][1] == (s + g))
            by {
                assert(intervals[j][0] == starts[j]);
                assert(starts[j] < starts[k as int]);
            }
        }

        intervals.push(iv);
        k += 1;
    }

    intervals
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

fn gen_valid_params(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    // Generate n sorted unique starts in [0, 99_999] and positive gaps
    let mut starts: Vec<i32> = Vec::with_capacity(n);
    let mut cur: i64 = rng.gen_range_i64(0, 50);
    for _ in 0..n {
        if cur > 99_999 { cur = 99_999; }
        starts.push(cur as i32);
        let step = rng.gen_range_i64(1, std::cmp::max(1, (99_999 - cur) / (n as i64).max(1)));
        cur += step;
    }
    // Ensure strictly increasing
    for i in 1..starts.len() {
        if starts[i] <= starts[i - 1] {
            starts[i] = (starts[i - 1] + 1).min(99_999);
        }
    }
    // Deduplicate in case of overflow at 99_999
    starts.dedup();
    let n = starts.len();

    let mut gaps: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let max_gap = 100_000 - starts[i];
        let g = rng.gen_range_i64(1, max_gap as i64) as i32;
        gaps.push(g);
    }
    (starts, gaps)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1288);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    let mut emit = |intervals: Vec<Vec<i32>>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{:?}", intervals);
        if !seen.insert(key) { return; }
        let output = Solution::remove_covered_intervals(intervals.clone());
        writeln!(out, "{}", json!({
            "input": {"intervals": intervals},
            "output": output
        })).unwrap();
        *total += 1;
    };

    // Example test cases from description.md
    emit(vec![vec![1,4], vec![3,6], vec![2,8]], &mut seen, &mut out, &mut total);
    emit(vec![vec![1,4], vec![2,3]], &mut seen, &mut out, &mut total);

    // Hand-crafted edge cases
    emit(vec![vec![0,100_000]], &mut seen, &mut out, &mut total);
    emit(vec![vec![0,1]], &mut seen, &mut out, &mut total);
    emit(vec![vec![0,1], vec![0,2]], &mut seen, &mut out, &mut total);
    emit(vec![vec![0,100_000], vec![1,99_999]], &mut seen, &mut out, &mut total);
    emit(vec![vec![0,2], vec![1,3], vec![2,4]], &mut seen, &mut out, &mut total);
    emit(vec![vec![1,2], vec![1,3], vec![1,4]], &mut seen, &mut out, &mut total);

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    // Size classes for diverse array lengths
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),       // tiny
        (4, 10),      // small
        (11, 50),     // medium
        (51, 200),    // large
        (201, 1000),  // max
    ];

    // Generate test cases with diverse sizes and mutations
    for (lo, hi) in &size_classes {
        for &mk in &mutation_kinds {
            if total >= count { break; }
            let n = rng.gen_range_usize(*lo, *hi);
            let (starts, gaps) = gen_valid_params(&mut rng, n);
            let result = generate_test_case(starts, gaps, mk);
            emit(result, &mut seen, &mut out, &mut total);
        }
    }

    // Fill remaining with random sizes and mutations
    while total < count {
        let n = match total % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 50),
            3 => rng.gen_range_usize(50, 200),
            _ => rng.gen_range_usize(200, 1000),
        };
        let mk = rng.gen_range_usize(0, 4) as u8;
        let (starts, gaps) = gen_valid_params(&mut rng, n);
        let result = generate_test_case(starts, gaps, mk);
        emit(result, &mut seen, &mut out, &mut total);
    }
}
