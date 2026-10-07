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
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        deltas.len() >= 2,
        deltas.len() + 1 <= 10000,
        1 <= base <= 1_000_000_000i32,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        result@.len() >= 3,
        result@.len() <= 10000,
        forall |i: int, j: int| 0 <= i < j < result@.len() ==>
            result@[i] != result@[j],
        forall |i: int| 0 <= i < result@.len() ==>
            1 <= #[trigger] result[i] <= 1_000_000_000i32,
{
    let mut stones: Vec<i32> = Vec::new();
    stones.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            stones.len() == idx + 1,
            deltas.len() >= 2,
            deltas.len() + 1 <= 10000,
            1 <= base <= 1_000_000_000i32,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] stones[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < stones.len() ==>
                1 <= #[trigger] stones[k] <= 1_000_000_000i32,
            forall|k: int, l: int| 0 <= k < l < stones.len() ==>
                stones[k] < stones[l],
        decreases deltas.len() - idx,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = stones[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(1 <= next <= 1_000_000_000i32) by {
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
            };

            assert forall|k: int| 0 <= k < stones.len() implies stones[k] < next by {
                assert(stones[k] as int == base as int + sum_deltas(deltas@, k));
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        stones.push(next);
        idx += 1;
    }

    // stones is strictly increasing with length deltas.len() + 1 >= 3
    // Prove distinctness from strict ordering
    proof {
        assert forall|i: int, j: int| 0 <= i < j < stones@.len()
            implies stones@[i] != stones@[j] by {
            assert(stones[i] < stones[j]);
        };
    }

    if mutation_kind == 1 && stones.len() > 3 {
        // Shrink: remove last element
        stones.pop();
        proof {
            assert forall|i: int, j: int| 0 <= i < j < stones@.len()
                implies stones@[i] != stones@[j] by {
                assert(stones[i] < stones[j]);
            };
        }
        stones
    } else {
        stones
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

fn make_deltas(rng: &mut Rng, n: usize, max_delta: i64) -> Vec<i32> {
    let mut deltas = Vec::with_capacity(n);
    for _ in 0..n {
        deltas.push(rng.gen_range_i64(1, max_delta) as i32);
    }
    deltas
}

fn make_deltas_capped(rng: &mut Rng, n: usize, base: i32, max_val: i64) -> Vec<i32> {
    // Build deltas ensuring base + sum(deltas) <= max_val
    let mut deltas = Vec::with_capacity(n);
    let mut running = base as i64;
    for i in 0..n {
        let remaining_slots = (n - i) as i64;
        let budget = max_val - running - remaining_slots; // leave at least 1 per remaining
        let max_d = if budget > 0 { budget.min(1_000_000) } else { 0 };
        let d = if max_d >= 1 { rng.gen_range_i64(1, max_d + 1) } else { 1 };
        deltas.push(d as i32);
        running += d;
    }
    deltas
}

fn sum_deltas_exec(deltas: &[i32]) -> i64 {
    deltas.iter().map(|&d| d as i64).sum()
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1040);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |stones: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", stones);
        if !seen.insert(key) { return; }
        let output = Solution::num_moves_stones_ii(stones.clone());
        writeln!(out, "{}", json!({"input": {"stones": stones}, "output": output})).unwrap();
        *emitted += 1;
    };

    // Example inputs from description (unsorted, pass directly to solution)
    // We need to generate valid inputs through the generator, but we can also
    // craft deltas that produce equivalent sorted sequences then shuffle.
    // For simplicity, build from deltas and emit.

    // Example 1: stones = [7,4,9] -> sorted [4,7,9], deltas from base=4: [3,2]
    {
        let deltas = vec![3i32, 2];
        let stones = generate_test_case(&deltas, 4, 0);
        emit(stones, &mut seen, &mut out, &mut emitted);
    }

    // Example 2: stones = [6,5,4,3,10] -> sorted [3,4,5,6,10], deltas from base=3: [1,1,1,4]
    {
        let deltas = vec![1i32, 1, 1, 4];
        let stones = generate_test_case(&deltas, 3, 0);
        emit(stones, &mut seen, &mut out, &mut emitted);
    }

    // Hand-crafted seed configurations
    let seed_configs: Vec<(Vec<i32>, i32)> = vec![
        // Consecutive stones (min moves = 0)
        (vec![1, 1], 1),
        (vec![1, 1, 1, 1], 1),
        // Large gaps
        (vec![100, 100], 1),
        // All gap on one side
        (vec![1, 1000], 1),
        (vec![1000, 1], 1),
        // Minimal size (3 stones)
        (vec![5, 5], 10),
        // Near boundary values
        (vec![1, 1], 999_999_997),
        // Small consecutive from high base
        (vec![1, 1, 1], 500_000_000),
        // Large spread
        (vec![100_000, 100_000], 1),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1];

    for (deltas, base) in &seed_configs {
        // Validate preconditions before calling
        let s = sum_deltas_exec(deltas);
        if deltas.len() >= 2
            && deltas.len() + 1 <= 10000
            && *base >= 1
            && deltas.iter().all(|&d| d >= 1)
            && (*base as i64) + s <= 1_000_000_000
        {
            for &mk in &mutation_kinds {
                let stones = generate_test_case(deltas, *base, mk);
                emit(stones, &mut seen, &mut out, &mut emitted);
            }
        }
    }

    // Size classes for diverse generation
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 4),       // tiny (3-5 stones)
        (4, 9),       // small (5-10 stones)
        (9, 49),      // medium (10-50 stones)
        (49, 499),    // large (50-500 stones)
        (499, 4999),  // very large (500-5000 stones)
        (4999, 9999), // max (5000-10000 stones)
    ];

    // Generate random test cases across size classes
    while emitted < count {
        let class_idx = emitted % size_classes.len();
        let (lo, hi) = size_classes[class_idx];
        let n_deltas = rng.gen_range_usize(lo, hi);

        // Choose base value
        let base = match emitted % 5 {
            0 => 1i32,                                       // minimum
            1 => rng.gen_range_i64(1, 100) as i32,          // small
            2 => rng.gen_range_i64(1, 1000) as i32,         // medium
            3 => rng.gen_range_i64(1, 1_000_000) as i32,    // large
            _ => rng.gen_range_i64(1, 500_000_000) as i32,  // near max
        };

        let deltas = make_deltas_capped(&mut rng, n_deltas, base, 1_000_000_000);

        // Verify preconditions
        let s = sum_deltas_exec(&deltas);
        if deltas.len() >= 2
            && deltas.len() + 1 <= 10000
            && base >= 1
            && deltas.iter().all(|&d| d >= 1)
            && (base as i64) + s <= 1_000_000_000
        {
            let mk = if emitted % 3 == 0 { 1u8 } else { 0u8 };
            let stones = generate_test_case(&deltas, base, mk);
            emit(stones, &mut seen, &mut out, &mut emitted);
        }
    }
}
