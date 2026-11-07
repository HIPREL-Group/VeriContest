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
        deltas.len() + 1 <= 5_000,
        0 <= base <= 1_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000,
    ensures
        1 <= result.len() <= 5_000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1_000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] < result[j],
{
    // Build sorted array from base + cumulative deltas
    let mut citations: Vec<i32> = Vec::new();
    citations.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            citations.len() == idx + 1,
            deltas.len() + 1 <= 5_000,
            0 <= base <= 1_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] citations[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= idx as int ==>
                citations[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < citations.len() ==> 0 <= #[trigger] citations[k] <= 1_000,
            forall|k: int, l: int| 0 <= k < l < citations.len() ==> citations[k] < citations[l],
        decreases deltas.len() - idx,
    {
        let ghost old_len = citations.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = citations[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(0 <= next <= 1_000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int) <= 1_000);
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
            };

            assert forall|k: int| 0 <= k < citations.len() implies citations[k] < next by {
                assert(citations[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        citations.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < citations.len()
                implies citations[k] < citations[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(citations[l] == next);
                }
            };
        }
    }

    // Apply mutation
    if mutation_kind == 1 && citations.len() > 1 {
        // Shrink: pop last element
        let last_idx = citations.len() - 1;
        let mut shrunk: Vec<i32> = Vec::new();
        let mut si: usize = 0;
        while si < last_idx
            invariant
                0 <= si <= last_idx,
                last_idx == citations.len() - 1,
                last_idx >= 1,
                shrunk.len() == si,
                citations.len() >= 2,
                forall|k: int| 0 <= k < citations.len() ==> 0 <= #[trigger] citations[k] <= 1_000,
                forall|k: int, l: int| 0 <= k < l < citations.len()
                    ==> citations[k] < citations[l],
                forall|k: int| 0 <= k < si as int ==> #[trigger] shrunk[k] == citations[k],
                forall|k: int| 0 <= k < shrunk.len() ==> 0 <= #[trigger] shrunk[k] <= 1_000,
                forall|k: int, l: int| 0 <= k < l < shrunk.len()
                    ==> shrunk[k] < shrunk[l],
            decreases last_idx - si,
        {
            shrunk.push(citations[si]);
            si = si + 1;
        }
        shrunk
    } else if mutation_kind == 2 && citations.len() > 1 {
        // Keep first half
        let half = citations.len() / 2;
        let take = if half >= 1 { half } else { 1 };
        let mut first_half: Vec<i32> = Vec::new();
        let mut fi: usize = 0;
        while fi < take
            invariant
                0 <= fi <= take,
                1 <= take <= citations.len(),
                first_half.len() == fi,
                forall|k: int| 0 <= k < citations.len() ==> 0 <= #[trigger] citations[k] <= 1_000,
                forall|k: int, l: int| 0 <= k < l < citations.len()
                    ==> citations[k] < citations[l],
                forall|k: int| 0 <= k < fi as int ==> #[trigger] first_half[k] == citations[k],
                forall|k: int| 0 <= k < first_half.len() ==> 0 <= #[trigger] first_half[k] <= 1_000,
                forall|k: int, l: int| 0 <= k < l < first_half.len()
                    ==> first_half[k] < first_half[l],
            decreases take - fi,
        {
            first_half.push(citations[fi]);
            fi = fi + 1;
        }
        first_half
    } else if mutation_kind == 3 {
        // Single element: just base
        let mut single: Vec<i32> = Vec::new();
        single.push(base);
        single
    } else {
        // Identity (mutation_kind == 0 or fallback)
        citations
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

/// Build deltas that sum to at most `budget`, each >= 1, length `n`.
fn random_deltas(rng: &mut Rng, n: usize, budget: i32) -> Vec<i32> {
    if n == 0 {
        return Vec::new();
    }
    let mut deltas = Vec::new();
    let mut remaining = budget;
    for i in 0..n {
        let left = n - i;
        let max_d = remaining - (left as i32 - 1); // leave at least 1 for each remaining
        let d = if max_d <= 1 {
            1
        } else {
            rng.gen_range_i64(1, max_d as i64) as i32
        };
        deltas.push(d);
        remaining -= d;
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(275);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $mk:expr) => {
            if emitted < count {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let mk_val: u8 = $mk;
                let citations = generate_test_case(&deltas_val, base_val, mk_val);
                let result = Solution::h_index(citations.clone());
                let line = json!({
                    "input": {"citations": citations},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    emitted += 1;
                }
            }
        };
    }

    // ---- LeetCode examples from description.md ----
    emit!(sorted_to_deltas(&[0, 1, 3, 5, 6]), 0, 0);
    emit!(sorted_to_deltas(&[1, 2, 100]), 1, 0);

    // ---- Edge cases ----
    // Single element
    emit!(vec![], 0, 0);
    emit!(vec![], 1, 0);
    emit!(vec![], 1000, 0);

    // Two elements
    emit!(vec![1], 0, 0);
    emit!(vec![999], 0, 0);
    emit!(vec![1], 999, 0);

    // All zeros is impossible (strictly sorted), but [0] is fine
    // All same value is impossible (strictly sorted)

    // Consecutive integers from 0
    for n in [3, 5, 10, 50, 100] {
        let max_n = std::cmp::min(n, 1001);
        let deltas: Vec<i32> = vec![1; max_n - 1];
        emit!(deltas, 0, 0);
    }

    // Consecutive integers from various bases
    for base in [0, 100, 500, 900] {
        let max_len = std::cmp::min(1001 - base as usize, 100);
        if max_len >= 2 {
            let deltas: Vec<i32> = vec![1; max_len - 1];
            emit!(deltas, base, 0);
        }
    }

    // Apply mutations to a medium-sized array
    for mk in 0u8..=3 {
        emit!(sorted_to_deltas(&[0, 1, 3, 5, 6]), 0, mk);
        emit!(vec![1; 9], 0, mk);
        emit!(vec![2; 49], 0, mk);
    }

    // ---- Random test cases with diverse sizes ----
    while emitted < count {
        // Size class
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),                               // tiny
            1 => rng.gen_range_usize(1, 10),                              // small
            2 => rng.gen_range_usize(11, 100),                            // medium
            3 => rng.gen_range_usize(101, 500),                           // large
            _ => rng.gen_range_usize(501, std::cmp::min(1001, 5000)),     // max
        };

        // Base value — boundary ~20% of time
        let base: i32 = if emitted % 5 == 0 {
            *[0i32, 0, 1, 999, 1000].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            rng.gen_range_i64(0, 1000) as i32
        };

        // Budget: how much room for deltas
        let max_sum = 1000 - base;
        if max_sum < (n as i32 - 1) || n == 0 {
            continue; // can't fit n strictly increasing values in [base, 1000]
        }

        let num_deltas = n - 1;
        let deltas = if num_deltas == 0 {
            vec![]
        } else {
            random_deltas(&mut rng, num_deltas, max_sum)
        };

        let mk = (rng.next_u64() % 4) as u8;
        emit!(deltas, base, mk);
    }

    eprintln!("Generated {} test cases", emitted);
}
