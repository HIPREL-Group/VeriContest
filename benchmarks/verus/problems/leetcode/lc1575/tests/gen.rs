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

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    start_idx: i32,
    finish_idx: i32,
    fuel_val: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32, i32, i32))
    requires
        1 <= deltas.len() <= 99,
        1 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
        0 <= start_idx <= deltas.len() as i32,
        0 <= finish_idx <= deltas.len() as i32,
        1 <= fuel_val <= 200,
    ensures
        2 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int, j: int| #![trigger result.0[i], result.0[j]] 0 <= i && i < j && j < result.0.len() ==> result.0[i] != result.0[j],
        0 <= result.1 < result.0.len(),
        0 <= result.2 < result.0.len(),
        1 <= result.3 <= 200,
{
    // Build strictly increasing locations by accumulating deltas from base
    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
    }

    let mut locs: Vec<i32> = Vec::new();
    locs.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            locs.len() == i + 1,
            1 <= deltas.len() <= 99,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] locs[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < locs.len() ==> 1 <= #[trigger] locs[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < locs.len() ==> locs[k] < locs[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = locs.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = locs[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            // Upper bound
            assert(next as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
            assert(next <= 1_000_000_000);
            // Lower bound
            lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
            assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
            assert(next as int >= base as int);
            assert(next >= 1);
            // Strictly greater than all previous elements
            assert forall|k: int| 0 <= k < locs.len() implies locs[k] < next by {
                assert(locs[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        locs.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < locs.len() implies locs[k] < locs[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(locs[l] == next);
                }
            };
        }
    }

    // locs.len() == deltas.len() + 1, in [2, 100]
    // Strictly increasing implies distinct
    proof {
        assert forall|i: int, j: int|
            #![trigger locs[i], locs[j]]
            0 <= i && i < j && j < locs.len() implies locs[i] != locs[j]
        by {
            assert(locs[i] < locs[j]);
        };
    }

    // Apply mutations to start/finish/fuel
    let n = locs.len();
    let last_idx = (n - 1) as i32;
    let (s, f, fu) = if mutation_kind == 1 {
        // Swap start and finish
        (finish_idx, start_idx, fuel_val)
    } else if mutation_kind == 2 {
        // Set fuel to 1
        (start_idx, finish_idx, 1i32)
    } else if mutation_kind == 3 {
        // Set fuel to 200
        (start_idx, finish_idx, 200i32)
    } else if mutation_kind == 4 {
        // Set start to 0
        (0i32, finish_idx, fuel_val)
    } else if mutation_kind == 5 {
        // Set finish to 0
        (start_idx, 0i32, fuel_val)
    } else if mutation_kind == 6 {
        // Set start to last index
        (last_idx, finish_idx, fuel_val)
    } else if mutation_kind == 7 {
        // Set finish to last index
        (start_idx, last_idx, fuel_val)
    } else if mutation_kind == 8 {
        // start = finish (same city)
        (start_idx, start_idx, fuel_val)
    } else {
        // Identity
        (start_idx, finish_idx, fuel_val)
    };

    (locs, s, f, fu)
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

extern crate serde_json;
use serde_json::json;

fn random_deltas(rng: &mut Rng, count: usize, max_delta: i64) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..count {
        deltas.push(rng.gen_range_i64(1, max_delta.max(1)) as i32);
    }
    deltas
}

fn deltas_from_sorted(vals: &[i32]) -> Vec<i32> {
    let mut deltas = Vec::new();
    for i in 1..vals.len() {
        deltas.push(vals[i] - vals[i - 1]);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1575);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |locations: Vec<i32>,
                    start: i32,
                    finish: i32,
                    fuel: i32,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    n: &mut usize| {
        if *n >= count {
            return;
        }
        let key = format!("{:?}_{}_{}_{}", locations, start, finish, fuel);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::count_routes(locations.clone(), start, finish, fuel);
        writeln!(
            out,
            "{}",
            json!({
                "input": {
                    "locations": locations,
                    "start": start,
                    "finish": finish,
                    "fuel": fuel
                },
                "output": output
            })
        )
        .unwrap();
        *n += 1;
    };

    let num_mutations: u8 = 9;

    // ---- Example inputs from description.md ----
    {
        let ex1 = vec![2, 3, 6, 8, 4];
        let d1 = deltas_from_sorted(&{
            let mut v = ex1.clone();
            v.sort();
            v
        });
        // Example 1: locations=[2,3,6,8,4], start=1, finish=3, fuel=5
        // Use sorted locations and map indices accordingly
        // sorted: [2,3,4,6,8], base=2
        for mk in 0..num_mutations {
            let (locs, s, f, fu) = generate_test_case(&d1, 2, 1, 3, 5, mk);
            emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
        }
    }
    {
        // Example 2: locations=[4,3,1], start=1, finish=0, fuel=6
        // sorted: [1,3,4], base=1, deltas=[2,1]
        let d2 = vec![2, 1];
        for mk in 0..num_mutations {
            let (locs, s, f, fu) = generate_test_case(&d2, 1, 1, 0, 6, mk);
            emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
        }
    }
    {
        // Example 3: locations=[5,2,1], start=0, finish=2, fuel=3
        // sorted: [1,2,5], base=1, deltas=[1,3]
        let d3 = vec![1, 3];
        for mk in 0..num_mutations {
            let (locs, s, f, fu) = generate_test_case(&d3, 1, 0, 2, 3, mk);
            emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
        }
    }

    // ---- Edge: minimum size (2 locations) ----
    for mk in 0..num_mutations {
        let d = vec![1];
        let (locs, s, f, fu) = generate_test_case(&d, 1, 0, 1, 1, mk);
        emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
    }

    // ---- Edge: start == finish ----
    {
        let d = vec![5, 3, 2];
        for mk in [0u8, 8] {
            let (locs, s, f, fu) = generate_test_case(&d, 1, 0, 0, 10, mk);
            emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
        }
    }

    // ---- Edge: max fuel ----
    {
        let d = vec![1, 1, 1];
        let (locs, s, f, fu) = generate_test_case(&d, 1, 0, 3, 200, 0);
        emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
    }

    // ---- Edge: fuel = 1 ----
    {
        let d = vec![1, 1, 1];
        let (locs, s, f, fu) = generate_test_case(&d, 1, 0, 1, 1, 2);
        emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
    }

    // ---- Edge: large location values ----
    {
        let d = vec![100_000_000, 100_000_000];
        let (locs, s, f, fu) = generate_test_case(&d, 700_000_000, 0, 2, 50, 0);
        emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
    }

    // ---- Random small cases (n=2..6, fuel=1..30) across size/fuel classes ----
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 3),    // tiny
        (4, 6),    // small
        (7, 15),   // medium
        (16, 30),  // large
    ];

    let fuel_classes: Vec<(i64, i64)> = vec![
        (1, 5),
        (6, 20),
        (21, 50),
        (51, 100),
        (101, 200),
    ];

    for (sz_lo, sz_hi) in &size_classes {
        for (fu_lo, fu_hi) in &fuel_classes {
            for _ in 0..2 {
                if n >= count {
                    break;
                }
                let num_locs = rng.gen_range_usize(*sz_lo, *sz_hi);
                let num_deltas = num_locs - 1;
                let max_delta = if num_deltas > 0 {
                    ((999_999_999i64) / (num_deltas as i64)).max(1).min(100_000_000)
                } else {
                    1
                };
                let deltas = random_deltas(&mut rng, num_deltas, max_delta);
                let sum: i64 = deltas.iter().map(|&d| d as i64).sum();
                let base_hi = (1_000_000_000i64 - sum).max(1);
                let base = rng.gen_range_i64(1, base_hi) as i32;
                let si = rng.gen_range_i64(0, num_deltas as i64) as i32;
                let fi = rng.gen_range_i64(0, num_deltas as i64) as i32;
                let fuel = rng.gen_range_i64(*fu_lo, *fu_hi) as i32;
                let mk = rng.gen_range_usize(0, (num_mutations as usize) - 1) as u8;
                let (locs, s, f, fu) = generate_test_case(&deltas, base, si, fi, fuel, mk);
                emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
            }
        }
    }

    // ---- Random cases with consecutive locations (gap=1) ----
    for _ in 0..5 {
        if n >= count {
            break;
        }
        let num_locs = rng.gen_range_usize(2, 10);
        let deltas = vec![1i32; num_locs - 1];
        let base = rng.gen_range_i64(1, 999_999_990) as i32;
        let si = rng.gen_range_i64(0, (num_locs - 1) as i64) as i32;
        let fi = rng.gen_range_i64(0, (num_locs - 1) as i64) as i32;
        let fuel = rng.gen_range_i64(1, 50) as i32;
        let (locs, s, f, fu) = generate_test_case(&deltas, base, si, fi, fuel, 0);
        emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
    }

    // ---- Random cases with large gaps (locations far apart, few routes) ----
    for _ in 0..5 {
        if n >= count {
            break;
        }
        let num_locs = rng.gen_range_usize(2, 5);
        let num_deltas = num_locs - 1;
        let max_delta = ((999_999_999i64) / (num_deltas as i64).max(1)).max(1);
        let deltas = random_deltas(&mut rng, num_deltas, max_delta);
        let sum: i64 = deltas.iter().map(|&d| d as i64).sum();
        let base_hi = (1_000_000_000i64 - sum).max(1);
        let base = rng.gen_range_i64(1, base_hi) as i32;
        let si = rng.gen_range_i64(0, num_deltas as i64) as i32;
        let fi = rng.gen_range_i64(0, num_deltas as i64) as i32;
        let fuel = rng.gen_range_i64(1, 10) as i32;
        let (locs, s, f, fu) = generate_test_case(&deltas, base, si, fi, fuel, 0);
        emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
    }

    // ---- Fill remaining with random cases ----
    while n < count {
        let num_locs = rng.gen_range_usize(2, 20);
        let num_deltas = num_locs - 1;
        let max_delta = if num_deltas > 0 {
            ((999_999_999i64) / (num_deltas as i64)).max(1).min(50_000_000)
        } else {
            1
        };
        let deltas = random_deltas(&mut rng, num_deltas, max_delta);
        let sum: i64 = deltas.iter().map(|&d| d as i64).sum();
        let base_hi = (1_000_000_000i64 - sum).max(1);
        let base = rng.gen_range_i64(1, base_hi) as i32;
        let si = rng.gen_range_i64(0, num_deltas as i64) as i32;
        let fi = rng.gen_range_i64(0, num_deltas as i64) as i32;
        let fuel = rng.gen_range_i64(1, 200) as i32;
        let mk = rng.gen_range_usize(0, (num_mutations as usize) - 1) as u8;
        let (locs, s, f, fu) = generate_test_case(&deltas, base, si, fi, fuel, mk);
        emit(locs, s, f, fu, &mut seen, &mut out, &mut n);
    }
}
