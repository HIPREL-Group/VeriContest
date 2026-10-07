use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> valid_event(#[trigger] result[i]@),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> 1 <= (#[trigger] result[i])[0] <= 100000 && 1 <= result[i][1] <= 100000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i][1] < #[trigger] result[j][1],
{
    let count = if raw.len() == 0 { 1usize } else if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    let mut previous = 0i32;
    while i < count
        invariant
            1 <= count <= 1000, 0 <= i <= count, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j][0] <= 100000 && 1 <= result[j][1] <= 100000,
            0 <= previous <= 100000 - count as int + i as int,
            i > 0 ==> result[i - 1][1] == previous,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> #[trigger] result[j][1] < #[trigger] result[k][1],
        decreases count - i,
    {
        let a = if i < raw.len() && raw[i].len() > 0 { raw[i][0] } else { 1 };
        let b = if i < raw.len() && raw[i].len() > 1 { raw[i][1] } else { 1 };
        let mut a = if a < 1 { 1 } else if a > 100000 { 100000 } else { a };
        let mut b = if b < 1 { 1 } else if b > 100000 { 100000 } else { b };
        let upper = 100000 - count as i32 + i as i32 + 1;
        let v = b;
        let v = if v > upper { upper } else { v };
        let v = if v <= previous { previous + 1 } else { v };
        b = v;
        assert forall|j: int| 0 <= j < result.len() implies result[j][1] < v by {
            if j < i - 1 { assert(result[j][1] < result[(i - 1) as int][1]); }
        }
        previous = v;
        let mut row = Vec::new();
        row.push(a);
        row.push(b);
        result.push(row);
        i += 1;
    }
    assert forall|j: int| 0 <= j < result.len() implies valid_event(#[trigger] result[j]@) by {
        assert(result[j].len() == 2);
        assert(1 <= result[j][0] <= 100000 && 1 <= result[j][1] <= 100000);
    }
    result
}


pub open spec fn valid_event(e: Seq<i32>) -> bool {
    e.len() == 2 && 1 <= e[0] <= 100000 && 1 <= e[1] <= 100000
}

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when every delta >= 0.
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

pub fn generate_candidate(
    indices: &Vec<i32>,
    deltas: &Vec<i32>,
    base_time: i32,
    mutation_kind: u8,
) -> (result: Vec<Vec<i32>>)
    requires
        1 <= indices.len() <= 1000,
        deltas.len() + 1 == indices.len(),
        forall|i: int| 0 <= i < indices.len() ==> 1 <= #[trigger] indices[i] <= 100000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        1 <= base_time,
        base_time as int + sum_deltas(deltas@, deltas.len() as int) <= 100000,
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> valid_event(result[i]@),
        forall|i: int, j: int|
            0 <= i < j < result.len()
            && valid_event(result[i]@)
            && valid_event(result[j]@)
            ==> result[i][1] <= result[j][1],
{
    let mut events: Vec<Vec<i32>> = Vec::new();
    let mut cur_time: i32 = base_time;

    // Choose the index for position 0 based on mutation_kind
    let idx0: i32 =
        if mutation_kind == 1 {
            1i32          // boundary low
        } else if mutation_kind == 2 {
            100000i32     // boundary high
        } else {
            indices[0]
        };

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(sum_deltas(deltas@, 0) == 0);
        assert(base_time <= 100000);
    }

    let mut ev0: Vec<i32> = Vec::new();
    ev0.push(idx0);
    ev0.push(cur_time);

    proof {
        assert(ev0@.len() == 2);
        assert(1 <= idx0 <= 100000);
        assert(1 <= cur_time <= 100000);
        assert(valid_event(ev0@));
    }

    events.push(ev0);

    proof {
        assert(events.len() == 1);
        assert(valid_event(events[0]@));
        assert(events[0][1] as int == base_time as int + sum_deltas(deltas@, 0int));
    }

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            events.len() == i + 1,
            deltas.len() + 1 == indices.len(),
            1 <= indices.len() <= 1000,
            forall|k: int| 0 <= k < indices.len() ==> 1 <= #[trigger] indices[k] <= 100000,
            forall|k: int| 0 <= k < deltas.len() ==> 0 <= #[trigger] deltas[k],
            1 <= base_time,
            base_time as int + sum_deltas(deltas@, deltas.len() as int) <= 100000,
            cur_time as int == base_time as int + sum_deltas(deltas@, i as int),
            1 <= cur_time <= 100000,
            forall|k: int| 0 <= k < events.len() ==> valid_event(#[trigger] events[k]@),
            forall|k: int| 0 <= k < events.len() ==>
                #[trigger] events[k][1] as int == base_time as int + sum_deltas(deltas@, k),
            forall|k: int, l: int|
                0 <= k < l < events.len()
                && valid_event(events[k]@) && valid_event(events[l]@)
                ==> events[k][1] <= events[l][1],
        decreases deltas.len() - i,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next_time = cur_time + deltas[i];

        proof {
            assert(next_time as int == base_time as int + sum_deltas(deltas@, (i + 1) as int));
            assert(1 <= next_time <= 100000) by {
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                assert(next_time as int == base_time as int + sum_deltas(deltas@, (i + 1) as int));
                assert(next_time as int <= base_time as int + sum_deltas(deltas@, deltas.len() as int));
            };
        }

        // Choose index based on mutation_kind
        let idx: i32 =
            if mutation_kind == 1 {
                1i32          // all indices = 1
            } else if mutation_kind == 2 {
                100000i32     // all indices = 100000
            } else if mutation_kind == 3 {
                indices[0]    // all same as first
            } else {
                indices[i + 1]
            };

        let mut ev: Vec<i32> = Vec::new();
        ev.push(idx);
        ev.push(next_time);

        proof {
            assert(valid_event(ev@));
            assert forall|k: int| 0 <= k < events.len()
                && valid_event(events[k]@)
                implies events[k][1] <= next_time by {
                assert(events[k][1] as int == base_time as int + sum_deltas(deltas@, k));
                assert(next_time as int == base_time as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_mono(deltas@, k, (i + 1) as int);
            };
        }

        let ghost old_len = events.len();
        events.push(ev);
        cur_time = next_time;
        i = i + 1;

        proof {
            assert forall|k: int, l: int|
                0 <= k < l < events.len()
                && valid_event(events[k]@) && valid_event(events[l]@)
                implies events[k][1] <= events[l][1] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                }
            };

            assert forall|k: int| 0 <= k < events.len() implies
                #[trigger] events[k][1] as int == base_time as int + sum_deltas(deltas@, k) by {
                if k < old_len as int {
                } else {
                    assert(k == old_len as int);
                }
            };
        }
    }

    events
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0
            .wrapping_mul(6364136223846793005)
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

fn random_indices(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n {
        v.push(rng.gen_range_i64(1, 100000) as i32);
    }
    v
}

fn random_deltas(rng: &mut Rng, n_minus_1: usize, max_delta: i32) -> Vec<i32> {
    let mut v = Vec::new();
    for _ in 0..n_minus_1 {
        v.push(rng.gen_range_i64(0, max_delta as i64) as i32);
    }
    v
}

fn events_to_json(events: &Vec<Vec<i32>>) -> serde_json::Value {
    let arr: Vec<serde_json::Value> = events
        .iter()
        .map(|e| json!([e[0], e[1]]))
        .collect();
    serde_json::Value::Array(arr)
}

fn make_events_from_arrays(idxs: &[i32], times: &[i32]) -> (Vec<i32>, Vec<i32>, i32) {
    assert!(idxs.len() == times.len() && !idxs.is_empty());
    let indices: Vec<i32> = idxs.to_vec();
    let base_time = times[0];
    let mut deltas = Vec::new();
    for i in 1..times.len() {
        deltas.push(times[i] - times[i - 1]);
    }
    (indices, deltas, base_time)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3386);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($indices:expr, $deltas:expr, $base:expr, $mk:expr) => {
            if count < goal {
                let indices_val: Vec<i32> = $indices;
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let mk_val: u8 = $mk;
                let events = generate_candidate(
                    &indices_val, &deltas_val, base_val, mk_val,
                );
                let events = generate_test_case(events);
                let result = Solution::button_with_longest_time(events.clone());
                let line = json!({
                    "input": {"events": events_to_json(&events)},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- Example inputs from description.md ----
    {
        let (idx, del, base) = make_events_from_arrays(&[1, 2, 3, 1], &[2, 5, 9, 15]);
        emit!(idx, del, base, 0);
    }
    {
        let (idx, del, base) = make_events_from_arrays(&[10, 1], &[5, 7]);
        emit!(idx, del, base, 0);
    }

    // ---- Single event, all mutations ----
    for mk in 0u8..=3 {
        emit!(vec![1], vec![], 1, mk);
        emit!(vec![100000], vec![], 100000, mk);
        emit!(vec![50000], vec![], 50000, mk);
    }

    // ---- Two events, all mutations ----
    for mk in 0u8..=3 {
        emit!(vec![1, 2], vec![0], 1, mk);          // same time
        emit!(vec![1, 2], vec![99999], 1, mk);       // max gap
        emit!(vec![100000, 1], vec![5], 10, mk);      // higher idx first
        emit!(vec![5, 5], vec![10], 10, mk);           // same index
    }

    // ---- Small arrays with uniform deltas, all mutations ----
    for mk in 0u8..=3 {
        emit!(vec![1, 2, 3, 4, 5], vec![10, 10, 10, 10], 1, mk);
        emit!(vec![3, 1, 4, 1, 5], vec![0, 0, 0, 0], 100, mk);  // all same time
        emit!(vec![5, 4, 3, 2, 1], vec![1, 1, 1, 1], 1, mk);
    }

    // ---- One large gap among small ones ----
    for mk in 0u8..=3 {
        emit!(vec![1, 2, 3, 4], vec![1, 1000, 1], 1, mk);
        emit!(vec![1, 2, 3, 4], vec![1000, 1, 1], 1, mk);
        emit!(vec![1, 2, 3, 4], vec![1, 1, 1000], 1, mk);
    }

    // ---- Boundary indices ----
    emit!(vec![1, 1, 1], vec![50, 50], 1, 0);
    emit!(vec![100000, 100000, 100000], vec![50, 50], 1, 0);
    emit!(vec![1, 100000], vec![99999], 1, 0);

    // ---- Random tiny arrays (1-5 elements), all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(1, 5);
        let indices = random_indices(&mut rng, n);
        let max_d = if n <= 1 { 0 } else { std::cmp::min(99999 / n, 1000) as i32 };
        let deltas = random_deltas(&mut rng, n.saturating_sub(1), max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(100000i64, 100000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        for mk in 0u8..=3 {
            emit!(indices.clone(), deltas.clone(), base, mk);
        }
    }

    // ---- Random small arrays (6-20 elements), random mutations ----
    for _ in 0..6 {
        let n = rng.gen_range_usize(6, 20);
        let indices = random_indices(&mut rng, n);
        let max_d = std::cmp::min((99999 / n) as i32, 500);
        let deltas = random_deltas(&mut rng, n - 1, max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(100000i64, 100000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        emit!(indices.clone(), deltas.clone(), base, mk);
        emit!(indices.clone(), deltas.clone(), base, 0);
    }

    // ---- Random medium arrays (50-200 elements), random mutations ----
    for _ in 0..6 {
        let n = rng.gen_range_usize(50, 200);
        let indices = random_indices(&mut rng, n);
        let max_d = std::cmp::min((99999 / n) as i32, 100);
        let deltas = random_deltas(&mut rng, n - 1, max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(100000i64, 100000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        emit!(indices, deltas, base, mk);
    }

    // ---- Random large arrays (500-1000 elements), delta=0 or 1 ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(500, 1000);
        let indices = random_indices(&mut rng, n);
        let deltas = random_deltas(&mut rng, n - 1, 1);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(100000i64, 100000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        for mk in [0u8, 1, 2, 3] {
            emit!(indices.clone(), deltas.clone(), base, mk);
        }
    }

    // ---- Maximum size (1000 elements), delta=0 (all same time) ----
    {
        let indices = random_indices(&mut rng, 1000);
        let deltas = vec![0i32; 999];
        emit!(indices.clone(), deltas.clone(), 1, 0);
        emit!(indices.clone(), deltas.clone(), 100000, 1);
        emit!(indices, deltas, 50000, 3);
    }

    // ---- Maximum size (1000 elements), delta=1 ----
    {
        let indices = random_indices(&mut rng, 1000);
        let deltas = vec![1i32; 999];
        emit!(indices.clone(), deltas.clone(), 1, 0);
        emit!(indices.clone(), deltas.clone(), 99001, 1);
        emit!(indices, deltas, 50000, 2);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    while count < goal {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let indices = random_indices(&mut rng, n);
        let max_d = if n <= 1 { 0 } else { std::cmp::min((99999 / n) as i32, 200) };
        let deltas = random_deltas(&mut rng, n.saturating_sub(1), max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(100000i64, 100000 - total);
        let base = if hi < 1 { 1i32 } else { rng.gen_range_i64(1, hi) as i32 };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        emit!(indices, deltas, base, mk);
    }
}
