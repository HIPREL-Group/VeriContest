use vstd::prelude::*;

verus! {

/// Constructs a valid `(n, ranges)` pair for the Minimum Number of Taps problem
/// from a seed `ranges` vector, applying mutations for diversity.
pub fn generate_test_case(ranges: Vec<i32>, mutation_kind: u8) -> (result: (i32, Vec<i32>))
    requires
        2 <= ranges.len() <= 10_001,
        forall|i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
    ensures
        1 <= result.0 <= 10_000,
        result.1.len() == result.0 + 1,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 100,
{
    let n: i32 = (ranges.len() - 1) as i32;

    if mutation_kind == 0 {
        // Identity
        (n, ranges)
    } else if mutation_kind == 1 {
        // Set all elements to 0 (no tap covers anything — likely returns -1)
        let mut r = ranges;
        let mut k: usize = 0;
        while k < r.len()
            invariant
                0 <= k <= r.len(),
                r.len() == ranges.len(),
                forall|j: int| 0 <= j < k as int ==> r[j] == 0i32,
                forall|j: int| k as int <= j < r.len() as int ==> r[j] == ranges[j],
            decreases r.len() - k,
        {
            r.set(k, 0);
            k += 1;
        }
        (n, r)
    } else if mutation_kind == 2 {
        // Set all elements to 100 (max coverage — minimal taps needed)
        let mut r = ranges;
        let mut k: usize = 0;
        while k < r.len()
            invariant
                0 <= k <= r.len(),
                r.len() == ranges.len(),
                forall|j: int| 0 <= j < k as int ==> r[j] == 100i32,
                forall|j: int| k as int <= j < r.len() as int ==> r[j] == ranges[j],
            decreases r.len() - k,
        {
            r.set(k, 100);
            k += 1;
        }
        (n, r)
    } else if mutation_kind == 3 {
        // Set first tap to max range
        let mut r = ranges;
        r.set(0, 100);
        (n, r)
    } else if mutation_kind == 4 {
        // Set last tap to max range
        let mut r = ranges;
        let last = r.len() - 1;
        r.set(last, 100);
        (n, r)
    } else if mutation_kind == 5 {
        // Disable first tap
        let mut r = ranges;
        r.set(0, 0);
        (n, r)
    } else if mutation_kind == 6 && ranges.len() < 10_001 {
        // Grow by one tap (push 0)
        let mut r = ranges;
        r.push(0);
        let new_n: i32 = (r.len() - 1) as i32;
        (new_n, r)
    } else if mutation_kind == 7 && ranges.len() > 2 {
        // Shrink by one tap (pop)
        let mut r = ranges;
        r.pop();
        let new_n: i32 = (r.len() - 1) as i32;
        (new_n, r)
    } else if mutation_kind == 8 {
        // Nudge first tap up
        let mut r = ranges;
        if r[0] < 100 {
            r.set(0, r[0] + 1);
        }
        (n, r)
    } else if mutation_kind == 9 {
        // Nudge last tap down
        let mut r = ranges;
        let last = r.len() - 1;
        if r[last] > 0 {
            r.set(last, r[last] - 1);
        }
        (n, r)
    } else {
        // Fallback: identity
        (n, ranges)
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

fn random_ranges(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut ranges = Vec::with_capacity(n + 1);
    for _ in 0..=n {
        ranges.push(rng.gen_range_i64(0, 100) as i32);
    }
    ranges
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1326);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, ranges: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{},{:?}", n, ranges);
        if !seen.insert(key) { return; }
        let output = Solution::min_taps(n, ranges.clone());
        writeln!(out, "{}", json!({"input": {"n": n, "ranges": ranges}, "output": output})).unwrap();
        *count += 1;
    };

    // Example 1: n = 5, ranges = [3,4,1,1,0,0] -> 1
    {
        let r = vec![3, 4, 1, 1, 0, 0];
        for mk in 0u8..=9 {
            let (n, rr) = generate_test_case(r.clone(), mk);
            emit(n, rr, &mut seen, &mut out, &mut count);
        }
    }

    // Example 2: n = 3, ranges = [0,0,0,0] -> -1
    {
        let r = vec![0, 0, 0, 0];
        for mk in 0u8..=9 {
            let (n, rr) = generate_test_case(r.clone(), mk);
            emit(n, rr, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: n=1, ranges=[1,1] (minimal garden, full coverage)
    {
        let r = vec![1, 1];
        for mk in 0u8..=9 {
            let (n, rr) = generate_test_case(r.clone(), mk);
            emit(n, rr, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: n=1, ranges=[0,0] (minimal garden, no coverage)
    {
        let r = vec![0, 0];
        for mk in 0u8..=9 {
            let (n, rr) = generate_test_case(r.clone(), mk);
            emit(n, rr, &mut seen, &mut out, &mut count);
        }
    }

    // Edge: single tap covers entire garden
    {
        let r = vec![50, 0, 0, 0, 0];
        for mk in 0u8..=9 {
            let (n, rr) = generate_test_case(r.clone(), mk);
            emit(n, rr, &mut seen, &mut out, &mut count);
        }
    }

    // Random test cases across size classes
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9];
    while count < target_count {
        let n: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),         // tiny
            1 => rng.gen_range_usize(1, 20),        // small
            2 => rng.gen_range_usize(21, 100),      // medium
            3 => rng.gen_range_usize(101, 1000),    // large
            _ => rng.gen_range_usize(1001, 10_000), // max
        };
        let ranges = random_ranges(&mut rng, n);
        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let (nn, rr) = generate_test_case(ranges, mk);
        emit(nn, rr, &mut seen, &mut out, &mut count);
    }
}
