use vstd::prelude::*;

verus! {

proof fn scan_span_bound(ts: Seq<i32>, duration: int, i: nat, total: int)
    requires i < ts.len(), duration >= 0,
    ensures scan_spec(ts, duration, i, total) <= total + ts[ts.len() - 1] - ts[i as int] + duration,
    decreases ts.len() - i,
{
    if i + 1 < ts.len() {
        let gap = ts[(i + 1) as int] - ts[i as int];
        let contrib = if gap < duration { gap } else { duration };
        scan_span_bound(ts, duration, i + 1, total + contrib);
    }
}
pub fn generate_test_case(raw: Vec<i32>, duration: i32) -> (result: (Vec<i32>, i32))
    ensures 1 <= result.0.len() <= 10000, 0 <= result.1 <= 10000000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 10000000,
        forall|i: int| 0 <= i < result.0.len() - 1 ==> #[trigger] result.0[i] <= result.0[i + 1],
        find_poisoned_duration_spec(result.0@, result.1 as int) <= i32::MAX,
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 10000 { 10000usize } else { raw.len() };
    let duration = if duration < 0 { 0 } else if duration > 10000000 { 10000000 } else { duration };
    let mut ts: Vec<i32> = Vec::new();
    let mut previous = 0i32;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 10000, ts.len() == i, 0 <= previous <= 10000000,
            i > 0 ==> previous == ts[i - 1],
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] ts[j] <= 10000000,
            forall|j: int| 0 <= j < i - 1 ==> #[trigger] ts[j] <= ts[j + 1],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { previous };
        let v = if v < previous { previous } else if v > 10000000 { 10000000 } else { v };
        ts.push(v); previous = v; i += 1;
    }
    proof { scan_span_bound(ts@, duration as int, 0, 0); }
    (ts, duration)
}


// Helper: sum of the first `end` elements of `deltas`
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

// Spec fns copied from spec.rs (free-standing versions)
pub open spec fn scan_spec(ts: Seq<i32>, duration: int, i: nat, total: int) -> int
    recommends i <= ts.len(),
    decreases ts.len() - i,
{
    if i >= ts.len() {
        total
    } else if i + 1 >= ts.len() {
        total + duration
    } else {
        let gap = (ts[(i + 1) as int] as int) - (ts[i as int] as int);
        let contrib = if gap < duration { gap } else { duration };
        scan_spec(ts, duration, i + 1, total + contrib)
    }
}

pub open spec fn find_poisoned_duration_spec(ts: Seq<i32>, duration: int) -> int {
    if ts.len() == 0 { 0 } else { scan_spec(ts, duration, 0, 0) }
}

// Lemma: scan_spec(ts, d, i, total) <= total + (len - i) * d
proof fn lemma_scan_bound(ts: Seq<i32>, duration: int, i: nat, total: int)
    requires
        i <= ts.len(),
        duration >= 0,
    ensures
        scan_spec(ts, duration, i, total) <= total + (ts.len() - i as int) * duration,
    decreases ts.len() - i,
{
    if i >= ts.len() {
        assert(i as int == ts.len());
        assert(scan_spec(ts, duration, i, total) == total);
        assert((ts.len() - i as int) == 0);
        assert((ts.len() - i as int) * duration == 0) by (nonlinear_arith)
            requires ts.len() - i as int == 0, duration >= 0 {};
    } else if i + 1 >= ts.len() {
        assert(scan_spec(ts, duration, i, total) == total + duration);
        assert(ts.len() - i as int >= 1);
        assert((ts.len() - i as int) * duration >= duration) by (nonlinear_arith)
            requires ts.len() - i as int >= 1, duration >= 0 {};
    } else {
        let gap = ts[(i + 1) as int] as int - ts[i as int] as int;
        let contrib = if gap < duration { gap } else { duration };
        lemma_scan_bound(ts, duration, (i + 1) as nat, total + contrib);
        assert(contrib <= duration);
        assert(total + contrib + (ts.len() - (i as int + 1)) * duration
            <= total + (ts.len() - i as int) * duration) by (nonlinear_arith)
            requires
                contrib <= duration,
                duration >= 0,
                ts.len() - i as int >= 2,
        {};
    }
}

pub fn generate_candidate(
    deltas: &Vec<i32>,
    base: i32,
    duration: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        deltas.len() + 1 <= 10_000,
        0 <= base,
        0 <= duration <= 10_000_000,
        forall|i: int| 0 <= i < deltas@.len() ==> 0 <= #[trigger] deltas@[i],
        base as int + sum_deltas(deltas@, deltas@.len() as int) <= 10_000_000,
        (deltas.len() as int + 1) * duration as int <= i32::MAX as int,
    ensures
        1 <= result.0.len() <= 10_000,
        0 <= result.1 <= 10_000_000,
        forall|j: int| 0 <= j < result.0@.len() ==> 0 <= #[trigger] result.0@[j] <= 10_000_000i32,
        forall|j: int| 0 <= j < result.0@.len() - 1 ==>
            #[trigger] result.0@[j] <= result.0@[j + 1],
        find_poisoned_duration_spec(result.0@, result.1 as int) <= i32::MAX as int,
{
    let mut ts: Vec<i32> = Vec::new();

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas@.len() as int);
        assert(sum_deltas(deltas@, 0) == 0);
    }

    ts.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            ts.len() == i + 1,
            deltas.len() + 1 <= 10_000,
            0 <= base,
            0 <= duration <= 10_000_000,
            forall|k: int| 0 <= k < deltas@.len() ==> 0 <= #[trigger] deltas@[k],
            base as int + sum_deltas(deltas@, deltas@.len() as int) <= 10_000_000,
            (deltas.len() as int + 1) * duration as int <= i32::MAX as int,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] ts@[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < ts@.len() ==>
                0 <= #[trigger] ts@[k] <= 10_000_000i32,
            forall|k: int, l: int| 0 <= k < l < ts@.len() ==> ts@[k] <= ts@[l],
        decreases deltas.len() - i,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas@.len() as int);
            lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
        }

        let next = ts[i] + deltas[i];

        proof {
            assert(sum_deltas(deltas@, (i + 1) as int)
                == sum_deltas(deltas@, i as int) + deltas@[i as int] as int);
            assert(ts@[i as int] as int == base as int + sum_deltas(deltas@, i as int));
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(0 <= next) by {
                assert(sum_deltas(deltas@, 0) == 0);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
            };
            assert(next as int <= 10_000_000);
            assert forall|k: int| 0 <= k < ts@.len() implies ts@[k] <= next by {
                assert(ts@[k] as int == base as int + sum_deltas(deltas@, k));
                lemma_sum_deltas_mono(deltas@, k, (i + 1) as int);
            };
        }

        ts.push(next);
        i += 1;
    }

    // Apply duration mutation (only decrease to preserve overflow bound)
    let dur: i32 = if mutation_kind == 0 {
        duration                                          // identity
    } else if mutation_kind == 1 {
        0i32                                              // zero duration
    } else if mutation_kind == 2 {
        duration / 2                                      // halve
    } else if mutation_kind == 3 && duration > 0 {
        duration - 1                                      // nudge down
    } else {
        duration                                          // fallback
    };

    proof {
        assert(0 <= dur <= duration);
        assert(0 <= dur <= 10_000_000);
        assert(1 <= ts@.len() <= 10_000);
        lemma_scan_bound(ts@, dur as int, 0 as nat, 0);
        assert(find_poisoned_duration_spec(ts@, dur as int)
            == scan_spec(ts@, dur as int, 0 as nat, 0));
        assert(scan_spec(ts@, dur as int, 0 as nat, 0)
            <= ts@.len() as int * dur as int);
        assert(ts@.len() as int * dur as int <= i32::MAX as int) by (nonlinear_arith)
            requires
                0 <= dur as int <= duration as int,
                ts@.len() as int >= 1,
                ts@.len() as int == deltas@.len() as int + 1,
                (deltas@.len() as int + 1) * duration as int <= i32::MAX as int,
        {};
    }

    (ts, dur)
}

} // verus!

// --- Unverified main() ---

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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn series_to_deltas(vals: &[i32]) -> Vec<i32> {
    let mut deltas = Vec::new();
    for i in 1..vals.len() {
        deltas.push(vals[i] - vals[i - 1]);
    }
    deltas
}

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(0, max_d as i64) as i32);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $duration:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let dur_val: i32 = $duration;
                let mk_val: u8 = $mk;
                let (ts_out, dur_out) = generate_candidate(
                    &deltas_val, base_val, dur_val, mk_val,
                );
                let (ts_out, dur_out) = generate_test_case(ts_out, dur_out);
                let result = Solution::find_poisoned_duration(ts_out.clone(), dur_out);
                let line = json!({
                    "input": {"timeSeries": ts_out, "duration": dur_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    emit!(series_to_deltas(&[1, 4]), 1, 2, 0);   // Example 1
    emit!(series_to_deltas(&[1, 2]), 1, 2, 0);   // Example 2

    // ---- Single element, all mutations ----
    for mk in 0u8..=3 {
        emit!(vec![], 0, 5, mk);
        emit!(vec![], 0, 0, mk);
        emit!(vec![], 10_000_000, 0, mk);
        emit!(vec![], 0, 10_000_000, mk);
    }

    // ---- Small arrays, various gaps, all mutations ----
    for mk in 0u8..=3 {
        emit!(vec![3], 1, 2, mk);
        emit!(vec![1], 1, 2, mk);
        emit!(vec![0], 5, 3, mk);
        emit!(vec![1, 1, 1], 0, 1, mk);
        emit!(vec![0, 0, 0], 0, 5, mk);
    }

    // ---- All same timestamps (deltas=0) ----
    for mk in 0u8..=3 {
        emit!(vec![0; 99], 0, 10, mk);
        emit!(vec![0; 9], 10_000_000, 0, mk);
    }

    // ---- Large duration with small array ----
    emit!(vec![], 0, 10_000_000, 0);
    emit!(vec![100], 0, 1_073_741_823, 0);

    // ---- Consecutive timestamps (delta=1), various sizes ----
    for mk in 0u8..=3 {
        emit!(vec![1; 9], 0, 3, mk);
        emit!(vec![1; 99], 0, 50, mk);
    }

    // ---- Large gaps, small duration ----
    emit!(vec![1000, 1000, 1000], 0, 5, 0);
    emit!(vec![1000, 1000, 1000], 0, 5, 1);
    emit!(vec![1000, 1000, 1000], 0, 5, 2);

    // ---- Duration equals gap ----
    emit!(vec![5, 5, 5], 0, 5, 0);

    // ---- Duration larger than gap ----
    emit!(vec![1, 1, 1], 0, 100, 0);

    // ---- Random: tiny arrays (1-5 elements) ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(1, 5);
        let base = rng.gen_range_i64(0, 5_000_000) as i32;
        let remaining = 10_000_000i64 - base as i64;
        let max_d = if n > 1 { (remaining / (n as i64 - 1)).max(0) as i32 } else { 0 };
        let deltas = random_deltas(&mut rng, n, max_d.max(0));
        let max_dur = std::cmp::min(10_000_000i64, i32::MAX as i64 / n as i64);
        let dur = rng.gen_range_i64(0, max_dur) as i32;
        let mk = (rng.gen_range_i64(0, 3) as u8) % 4;
        emit!(deltas, base, dur, mk);
    }

    // ---- Random: small arrays (6-50 elements) ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(6, 50);
        let base = rng.gen_range_i64(0, 5_000_000) as i32;
        let remaining = 10_000_000i64 - base as i64;
        let max_d = (remaining / (n as i64 - 1).max(1)) as i32;
        let deltas = random_deltas(&mut rng, n, max_d.max(0));
        let max_dur = std::cmp::min(10_000_000i64, i32::MAX as i64 / n as i64);
        let dur = rng.gen_range_i64(0, max_dur) as i32;
        let mk = (rng.gen_range_i64(0, 3) as u8) % 4;
        emit!(deltas, base, dur, mk);
    }

    // ---- Random: medium arrays (51-500) ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(51, 500);
        let base = rng.gen_range_i64(0, 1_000_000) as i32;
        let remaining = 10_000_000i64 - base as i64;
        let max_d = (remaining / (n as i64 - 1).max(1)) as i32;
        let deltas = random_deltas(&mut rng, n, max_d.max(1));
        let max_dur = std::cmp::min(10_000_000i64, i32::MAX as i64 / n as i64);
        let dur = rng.gen_range_i64(0, max_dur) as i32;
        let mk = (rng.gen_range_i64(0, 3) as u8) % 4;
        emit!(deltas, base, dur, mk);
    }

    // ---- Random: large arrays (501-5000) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(501, 5000);
        let base = rng.gen_range_i64(0, 100_000) as i32;
        let remaining = 10_000_000i64 - base as i64;
        let max_d = (remaining / (n as i64 - 1).max(1)) as i32;
        let deltas = random_deltas(&mut rng, n, max_d.max(1));
        let max_dur = std::cmp::min(10_000_000i64, i32::MAX as i64 / n as i64);
        let dur = rng.gen_range_i64(0, max_dur) as i32;
        let mk = (rng.gen_range_i64(0, 3) as u8) % 4;
        emit!(deltas, base, dur, mk);
    }

    // ---- Random: max arrays (5001-10000) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(5001, 10000);
        let base = 0i32;
        let remaining = 10_000_000i64;
        let max_d = (remaining / (n as i64 - 1).max(1)) as i32;
        let deltas = random_deltas(&mut rng, n, max_d.max(1));
        let max_dur = std::cmp::min(10_000_000i64, i32::MAX as i64 / n as i64);
        let dur = rng.gen_range_i64(0, max_dur) as i32;
        let mk = (rng.gen_range_i64(0, 3) as u8) % 4;
        emit!(deltas, base, dur, mk);
    }

    // ---- Maximum size, delta=1, small duration ----
    {
        let deltas = vec![1i32; 9999];
        emit!(deltas.clone(), 0, 100, 0);
        emit!(deltas.clone(), 0, 100, 1);
        emit!(deltas.clone(), 0, 100, 2);
        emit!(deltas.clone(), 0, 100, 3);
    }

    // ---- Fill remaining with random sizes ----
    while count < goal {
        let n = rng.gen_range_usize(1, 10000);
        let base = rng.gen_range_i64(0, 5_000_000) as i32;
        let remaining = 10_000_000i64 - base as i64;
        let max_d = if n > 1 {
            (remaining / (n as i64 - 1).max(1)) as i32
        } else {
            0
        };
        let deltas = random_deltas(&mut rng, n, max_d.max(0));
        let sum: i64 = deltas.iter().map(|d| *d as i64).sum();
        if base as i64 + sum > 10_000_000 { continue; }
        let max_dur = std::cmp::min(10_000_000i64, i32::MAX as i64 / n as i64);
        let dur = rng.gen_range_i64(0, max_dur) as i32;
        let mk = (rng.gen_range_i64(0, 3) as u8) % 4;
        emit!(deltas, base, dur, mk);
    }
}
