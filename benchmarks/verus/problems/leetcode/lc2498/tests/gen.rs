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
    mutation_kind: u8,
) -> (stones: Vec<i32>)
    requires
        1 <= deltas.len() <= 99_999,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        2 <= stones.len() <= 100_000,
        forall|i: int| 0 <= i < stones.len() ==> 0 <= #[trigger] stones[i] <= 1_000_000_000,
        stones[0] == 0,
        forall|i: int, j: int| 0 <= i < j < stones.len() ==> stones[i] < stones[j],
{
    let mut stones: Vec<i32> = Vec::new();
    stones.push(0i32);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            stones.len() == idx + 1,
            1 <= deltas.len() <= 99_999,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            stones[0] == 0i32,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] stones[k] as int == sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < stones.len() ==> 0 <= #[trigger] stones[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < stones.len() ==> stones[k] < stones[l],
        decreases deltas.len() - idx,
    {
        let ghost old_len = stones.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = stones[idx] + deltas[idx];

        proof {
            assert(next as int == sum_deltas(deltas@, (idx + 1) as int));
            assert(0 <= next <= 1_000_000_000) by {
                assert(next as int == sum_deltas(deltas@, (idx + 1) as int));
                assert(sum_deltas(deltas@, (idx + 1) as int)
                    <= sum_deltas(deltas@, deltas.len() as int));
                assert(sum_deltas(deltas@, (idx + 1) as int) <= 1_000_000_000);
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
            };

            assert forall|k: int| 0 <= k < stones.len() implies stones[k] < next by {
                assert(stones[k] as int == sum_deltas(deltas@, k));
                assert(next as int == sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        stones.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < stones.len() implies stones[k] < stones[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(stones[l] == next);
                }
            };
        }
    }

    // Apply mutation: modify the array while preserving all invariants.
    // Since stones[0] must be 0 and the array must be strictly increasing
    // with values in [0, 1_000_000_000], mutations are limited.
    if mutation_kind == 1 && stones.len() >= 3 {
        // Shrink: remove last element (still >= 2 elements)
        let old_len = stones.len();
        let popped = stones.pop();
        proof {
            assert(stones.len() >= 2);
            assert(stones[0] == 0i32);
            assert forall|k: int| 0 <= k < stones.len() implies 0 <= #[trigger] stones[k] <= 1_000_000_000 by {};
            assert forall|k: int, l: int| 0 <= k < l < stones.len() implies stones[k] < stones[l] by {};
        }
    } else if mutation_kind == 2 && stones.len() >= 3 {
        // Swap last two elements' gap: set second-to-last = average of its neighbors
        // This is complex; instead just return identity for this branch
    }

    stones
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_deltas(rng: &mut Rng, n: usize, max_d: i64, max_sum: i64) -> Vec<i32> {
    let mut deltas = Vec::new();
    let mut running_sum: i64 = 0;
    for _ in 0..n {
        let remaining = max_sum - running_sum;
        if remaining < 1 {
            break;
        }
        let d = rng.gen_range_i64(1, max_d.min(remaining));
        running_sum += d;
        deltas.push(d as i32);
    }
    if deltas.is_empty() {
        deltas.push(1);
    }
    deltas
}

fn sorted_to_deltas(vals: &[i32]) -> Vec<i32> {
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2498);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    macro_rules! emit {
        ($deltas:expr, $mk:expr) => {
            if emitted < count {
                let deltas_val: Vec<i32> = $deltas;
                let mk_val: u8 = $mk;
                let stones_out = generate_test_case(&deltas_val, mk_val);
                let result = Solution::max_jump(stones_out.clone());
                let line = json!({
                    "input": {"stones": stones_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    emitted += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    emit!(sorted_to_deltas(&[0, 2, 5, 6, 7]), 0);   // Example 1: output 5
    emit!(sorted_to_deltas(&[0, 3, 9]), 0);           // Example 2: output 9

    // ---- Minimal cases ----
    emit!(vec![1], 0);         // [0, 1]
    emit!(vec![1_000_000_000], 0);  // [0, 1000000000]

    // ---- Small with mutations ----
    for mk in 0u8..=2 {
        emit!(vec![1, 1, 1], mk);
        emit!(vec![1, 2, 3], mk);
        emit!(vec![100, 200, 300], mk);
        emit!(sorted_to_deltas(&[0, 1, 3, 6, 10, 15]), mk);
    }

    // ---- Size classes with diverse deltas ----
    let mut _attempts_0 = 0usize;
    while emitted < count {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let i = emitted;

        // Size class
        let n: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),           // tiny
            1 => rng.gen_range_usize(1, 20),          // small
            2 => rng.gen_range_usize(20, 200),        // medium
            3 => rng.gen_range_usize(200, 2000),      // large
            _ => rng.gen_range_usize(2000, 99_999.min(count * 100)),  // xlarge
        };

        // Delta magnitude class
        let max_d: i64 = match i % 4 {
            0 => 1,                                   // consecutive integers
            1 => rng.gen_range_i64(1, 10),            // small gaps
            2 => rng.gen_range_i64(1, 1000),          // medium gaps
            _ => rng.gen_range_i64(1, 1_000_000),     // large gaps
        };

        let max_sum: i64 = 1_000_000_000;
        let deltas = random_deltas(&mut rng, n, max_d, max_sum);

        let mk = (i % 3) as u8;
        emit!(deltas, mk);
    }

    eprintln!("Generated {} test cases", emitted);
}
