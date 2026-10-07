use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when deltas >= 1.
proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// Two partial sums differ by at least (b - a) when every delta >= 1.
proof fn lemma_sum_deltas_strict(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) + (b - a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if b - a == 1 {
    } else {
        lemma_sum_deltas_strict(deltas, a, b - 1);
    }
}

/// sum_deltas(deltas, 0) == 0
proof fn lemma_sum_deltas_zero(deltas: Seq<i32>)
    ensures sum_deltas(deltas, 0) == 0,
{
}

/// sum_deltas(deltas, k+1) == sum_deltas(deltas, k) + deltas[k]
proof fn lemma_sum_deltas_step(deltas: Seq<i32>, k: int)
    requires 0 <= k < deltas.len(),
    ensures sum_deltas(deltas, k + 1) == sum_deltas(deltas, k) + deltas[k] as int,
{
}

pub fn generate_test_case(
    base: i32,
    deltas: &Vec<i32>,
    gaps: &Vec<i32>,
    gap_max: i32,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        gaps.len() == deltas.len() + 1,
        1 <= gaps.len() <= 20_000,
        -1_000_000 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        0 <= gap_max,
        forall|i: int| 0 <= i < gaps.len() ==> 0 <= #[trigger] gaps[i] <= gap_max,
        base as int + sum_deltas(deltas@, deltas.len() as int) + gap_max as int <= 1_000_000,
    ensures
        1 <= result.len() <= 20_000,
        forall |i: int| 0 <= i < result.len() ==> result[i].len() == 2,
        forall |i: int| 0 <= i < result.len() ==> -1_000_000 <= #[trigger] result[i][0] <= result[i][1] <= 1_000_000,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i][0] != result[j][0],
{
    let n = gaps.len();
    let mut intervals: Vec<Vec<i32>> = Vec::new();
    let mut current: i32 = base;
    let mut k: usize = 0;

    proof { lemma_sum_deltas_zero(deltas@); }

    while k < n
        invariant
            0 <= k <= n,
            n == gaps.len(),
            1 <= n <= 20_000,
            gaps.len() == deltas.len() + 1,
            intervals.len() == k,
            -1_000_000 <= base,
            0 <= gap_max,
            forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
            forall|i: int| 0 <= i < gaps.len() ==> 0 <= #[trigger] gaps[i] <= gap_max,
            base as int + sum_deltas(deltas@, deltas.len() as int) + gap_max as int <= 1_000_000,
            k < n ==> current as int == base as int + sum_deltas(deltas@, k as int),
            forall|i: int| 0 <= i < k as int ==> #[trigger] intervals[i].len() == 2,
            forall|i: int| 0 <= i < k as int ==>
                intervals[i][0] as int == base as int + sum_deltas(deltas@, i),
            forall|i: int| 0 <= i < k as int ==>
                -1_000_000 <= #[trigger] intervals[i][0] <= intervals[i][1] <= 1_000_000,
            forall|i: int, j: int| 0 <= i < j < k as int ==>
                intervals[i][0] < intervals[j][0],
        decreases n - k,
    {
        // Prove current is in range for this iteration
        proof {
            lemma_sum_deltas_mono(deltas@, k as int, deltas.len() as int);
            assert(sum_deltas(deltas@, k as int) <= sum_deltas(deltas@, deltas.len() as int));
            assert(current as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
            assert(current as int + gap_max as int <= 1_000_000);
            lemma_sum_deltas_mono(deltas@, 0, k as int);
            assert(sum_deltas(deltas@, k as int) >= 0);
            assert(current as int >= base as int);
            assert(-1_000_000 <= current);
        }

        let g: i32 = if mutation_kind == 1 {
            0i32
        } else if mutation_kind == 2 {
            gap_max
        } else {
            gaps[k]
        };

        let end_val: i32 = current + g;

        proof {
            assert(0 <= g <= gap_max);
            assert(end_val as int == current as int + g as int);
            assert(end_val as int <= current as int + gap_max as int);
            assert(end_val as int <= 1_000_000);
            assert(end_val >= current);
            assert(-1_000_000 <= current <= end_val <= 1_000_000);
        }

        // Prove strict ordering: new start > all previous starts
        proof {
            assert forall|j: int| 0 <= j < k as int
                implies intervals[j][0] < current by
            {
                assert(intervals[j][0] as int == base as int + sum_deltas(deltas@, j));
                assert(current as int == base as int + sum_deltas(deltas@, k as int));
                lemma_sum_deltas_strict(deltas@, j, k as int);
            };
        }

        let mut interval: Vec<i32> = Vec::new();
        interval.push(current);
        interval.push(end_val);

        let ghost old_len = intervals.len();
        intervals.push(interval);

        proof {
            // Properties of the newly pushed interval
            assert(intervals[k as int].len() == 2);
            assert(intervals[k as int][0] == current);
            assert(intervals[k as int][1] == end_val);
            assert(intervals[k as int][0] as int == base as int + sum_deltas(deltas@, k as int));
            assert(-1_000_000 <= intervals[k as int][0]
                <= intervals[k as int][1] <= 1_000_000);

            // Strict monotonicity is maintained
            assert forall|i: int, j: int| 0 <= i < j < intervals.len()
                implies intervals[i][0] < intervals[j][0] by
            {
                if j < old_len as int {
                    // Both old elements — use previous invariant
                } else {
                    // j == k, i < k — new element is larger
                    assert(j == k as int);
                    assert(intervals[j][0] == current);
                }
            };
        }

        // Advance current to the next start value
        if k < deltas.len() {
            proof {
                lemma_sum_deltas_step(deltas@, k as int);
                lemma_sum_deltas_mono(deltas@, (k + 1) as int, deltas.len() as int);
                assert(base as int + sum_deltas(deltas@, (k + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (k + 1) as int)
                    <= 1_000_000 - gap_max as int);
                assert(base as int + sum_deltas(deltas@, (k + 1) as int) <= 1_000_000);
                lemma_sum_deltas_mono(deltas@, 0, (k + 1) as int);
                assert(base as int + sum_deltas(deltas@, (k + 1) as int) >= base as int);
                assert(base as int + sum_deltas(deltas@, (k + 1) as int) >= -1_000_000);
            }
            current = current + deltas[k];
            proof {
                assert(current as int == base as int + sum_deltas(deltas@, (k + 1) as int));
            }
        }

        k = k + 1;
    }

    // Mutation 3: shrink by removing the last interval
    if mutation_kind == 3 && intervals.len() > 1 {
        intervals.pop();
    }

    // Prove the final ensures from strict monotonicity
    proof {
        assert forall|i: int, j: int| 0 <= i < j < intervals.len()
            implies intervals[i][0] != intervals[j][0] by
        {
            assert(intervals[i][0] < intervals[j][0]);
        };
    }

    intervals
}

} // verus!

// ---------- Unverified test-generation harness ----------

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

fn random_deltas(rng: &mut Rng, count: usize, max_d: i32) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..count {
        v.push(rng.gen_range_i64(1, max_d as i64) as i32);
    }
    v
}

fn random_gaps(rng: &mut Rng, count: usize, gap_max: i32) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..count {
        v.push(rng.gen_range_i64(0, gap_max as i64) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(436);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // Helper: emit a test case from raw intervals (for examples)
    let mut emit_raw = |intervals: Vec<Vec<i32>>,
                        seen: &mut HashSet<String>,
                        out: &mut std::io::BufWriter<std::fs::File>,
                        count: &mut usize| {
        if *count >= goal { return; }
        let result = Solution::find_right_interval(intervals.clone());
        let line = json!({"input": {"intervals": intervals}, "output": result}).to_string();
        if seen.insert(line.clone()) {
            writeln!(out, "{}", line).unwrap();
            *count += 1;
        }
    };

    // ---- LeetCode examples ----
    emit_raw(vec![vec![1, 2]], &mut seen, &mut out, &mut count);
    emit_raw(vec![vec![3, 4], vec![2, 3], vec![1, 2]], &mut seen, &mut out, &mut count);
    emit_raw(vec![vec![1, 4], vec![2, 3], vec![3, 4]], &mut seen, &mut out, &mut count);

    // Helper: emit a test case via the verified generator
    macro_rules! emit {
        ($base:expr, $deltas:expr, $gaps:expr, $gap_max:expr, $mk:expr) => {
            if count < goal {
                let base_v: i32 = $base;
                let deltas_v: Vec<i32> = $deltas;
                let gaps_v: Vec<i32> = $gaps;
                let gap_max_v: i32 = $gap_max;
                let mk_v: u8 = $mk;
                let intervals = generate_test_case(
                    base_v, &deltas_v, &gaps_v, gap_max_v, mk_v,
                );
                let result = Solution::find_right_interval(intervals.clone());
                let line = json!({
                    "input": {"intervals": intervals},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- Single interval, all mutations ----
    for mk in 0u8..=3 {
        emit!(0, vec![], vec![0], 0, mk);
        emit!(-1_000_000, vec![], vec![0], 0, mk);
        emit!(0, vec![], vec![1_000_000], 1_000_000, mk);
        emit!(-500_000, vec![], vec![1_000_000], 1_000_000, mk);
    }

    // ---- Two intervals, all mutations ----
    for mk in 0u8..=3 {
        emit!(0, vec![1], vec![0, 0], 0, mk);          // point intervals at 0,1
        emit!(0, vec![10], vec![5, 5], 5, mk);          // overlapping
        emit!(0, vec![5], vec![5, 5], 5, mk);           // touching
        emit!(-999_999, vec![1], vec![0, 0], 0, mk);    // near min boundary
    }

    // ---- Small arrays (3-10), varied gaps, all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(3, 10);
        let nd = n - 1;
        let max_d = std::cmp::max(1, (2_000_000 / n) as i32);
        let deltas = random_deltas(&mut rng, nd, std::cmp::min(max_d, 100));
        let total_delta: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total_delta);
        if hi < -1_000_000 { continue; }
        let base = rng.gen_range_i64(-1_000_000, hi) as i32;
        let space = 1_000_000i64 - base as i64 - total_delta;
        let gap_max = rng.gen_range_i64(0, std::cmp::min(space, 1_000_000)) as i32;
        let gaps = random_gaps(&mut rng, n, gap_max);
        for mk in 0u8..=3 {
            emit!(base, deltas.clone(), gaps.clone(), gap_max, mk);
        }
    }

    // ---- Medium arrays (11-200), mixed deltas ----
    for _ in 0..6 {
        let n = rng.gen_range_usize(11, 200);
        let nd = n - 1;
        let max_d = std::cmp::max(1, (2_000_000 / n) as i32);
        let deltas = random_deltas(&mut rng, nd, std::cmp::min(max_d, 50));
        let total_delta: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total_delta);
        if hi < -1_000_000 { continue; }
        let base = rng.gen_range_i64(-1_000_000, hi) as i32;
        let space = 1_000_000i64 - base as i64 - total_delta;
        let gap_max = rng.gen_range_i64(0, std::cmp::min(space, 100_000)) as i32;
        let gaps = random_gaps(&mut rng, n, gap_max);
        let mk = (rng.next_u64() % 4) as u8;
        emit!(base, deltas.clone(), gaps.clone(), gap_max, mk);
    }

    // ---- Large arrays (201-5000), delta=1 ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(201, 5000);
        let nd = n - 1;
        let deltas = vec![1i32; nd];
        let total_delta = nd as i64;
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total_delta);
        if hi < -1_000_000 { continue; }
        let base = rng.gen_range_i64(-1_000_000, hi) as i32;
        let space = 1_000_000i64 - base as i64 - total_delta;
        let gap_max = if space > 0 { rng.gen_range_i64(0, std::cmp::min(space, 10_000)) as i32 } else { 0 };
        let gaps = random_gaps(&mut rng, n, std::cmp::max(gap_max, 0));
        for mk in [0u8, 1, 2, 3] {
            emit!(base, deltas.clone(), gaps.clone(), gap_max, mk);
        }
    }

    // ---- Maximum size (20000), delta=1 ----
    {
        let n = 20_000usize;
        let nd = n - 1;
        let deltas = vec![1i32; nd];
        let total_delta = nd as i64;
        let base = -10_000i32; // leaves room: -10000 + 19999 = 9999
        let space = 1_000_000i64 - base as i64 - total_delta;
        let gap_max = std::cmp::min(space, 10_000) as i32;
        let gaps = random_gaps(&mut rng, n, gap_max);
        emit!(base, deltas.clone(), gaps.clone(), gap_max, 0);
        emit!(base, deltas.clone(), gaps.clone(), gap_max, 1);
        emit!(base, deltas.clone(), gaps.clone(), gap_max, 2);
    }

    // ---- Point intervals (all gaps = 0) via mutation 1 ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(5, 50);
        let nd = n - 1;
        let deltas = random_deltas(&mut rng, nd, 100);
        let total_delta: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total_delta);
        if hi < -1_000_000 { continue; }
        let base = rng.gen_range_i64(-1_000_000, hi) as i32;
        let gaps = vec![0i32; n];
        emit!(base, deltas.clone(), gaps, 0, 1);
    }

    // ---- Wide-gap intervals (all gaps = gap_max) via mutation 2 ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(2, 20);
        let nd = n - 1;
        let max_d = std::cmp::max(1, (1_000_000 / n) as i32);
        let deltas = random_deltas(&mut rng, nd, std::cmp::min(max_d, 200));
        let total_delta: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total_delta);
        if hi < -1_000_000 { continue; }
        let base = rng.gen_range_i64(-1_000_000, hi) as i32;
        let space = 1_000_000i64 - base as i64 - total_delta;
        let gap_max = if space > 0 { std::cmp::min(space, 500_000) as i32 } else { 0 };
        let gaps = vec![gap_max; n];
        emit!(base, deltas.clone(), gaps, gap_max, 2);
    }

    // ---- Fill remaining with random sizes and mutations ----
    while count < goal {
        let n = rng.gen_range_usize(1, 500);
        let nd = if n > 1 { n - 1 } else { 0 };
        let max_d = std::cmp::max(1, (2_000_000 / std::cmp::max(n, 1)) as i32);
        let deltas = random_deltas(&mut rng, nd, std::cmp::min(max_d, 200));
        let total_delta: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(1_000_000i64, 1_000_000 - total_delta);
        if hi < -1_000_000 { continue; }
        let base = rng.gen_range_i64(-1_000_000, hi) as i32;
        let space = 1_000_000i64 - base as i64 - total_delta;
        let gap_max = if space > 0 {
            rng.gen_range_i64(0, std::cmp::min(space, 1_000_000)) as i32
        } else { 0 };
        let gaps = random_gaps(&mut rng, n, std::cmp::max(gap_max, 0));
        let mk = (rng.next_u64() % 4) as u8;
        emit!(base, deltas, gaps, gap_max, mk);
    }
}
