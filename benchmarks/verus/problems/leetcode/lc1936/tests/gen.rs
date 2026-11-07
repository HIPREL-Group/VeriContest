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
    dist: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        deltas.len() + 1 <= 100_000,
        1 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
        1 <= dist <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] < result.0[j],
{
    let mut rungs: Vec<i32> = Vec::new();

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(sum_deltas(deltas@, 0) == 0);
        assert(base as int <= 1_000_000_000);
    }

    rungs.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            rungs.len() == i + 1,
            deltas.len() + 1 <= 100_000,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] rungs[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= i as int ==>
                rungs[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < rungs.len() ==> 1 <= #[trigger] rungs[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < rungs.len() ==> rungs[k] < rungs[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = rungs.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = rungs[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(1 <= next <= 1_000_000_000i32) by {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) <= 1_000_000_000);
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int >= 1);
            };

            assert forall|k: int| 0 <= k < rungs.len() implies rungs[k] < next by {
                assert(rungs[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        rungs.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < rungs.len() implies rungs[k] < rungs[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(rungs[l] == next);
                }
            };
        }
    }

    let mutated_dist: i32 =
        if mutation_kind == 1 && dist > 1 {
            1
        } else if mutation_kind == 2 {
            1_000_000_000
        } else {
            dist
        };

    (rungs, mutated_dist)
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

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(1, max_d as i64) as i32);
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
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1936);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $dist:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let dist_val: i32 = $dist;
                let mk_val: u8 = $mk;
                let (rungs_out, dist_out) = generate_test_case(
                    &deltas_val, base_val, dist_val, mk_val,
                );
                let result = Solution::add_rungs(rungs_out.clone(), dist_out);
                let line = json!({
                    "input": {"rungs": rungs_out, "dist": dist_out},
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
    emit!(sorted_to_deltas(&[1, 3, 5, 10]), 1, 2, 0);
    emit!(sorted_to_deltas(&[3, 6, 8, 10]), 3, 3, 0);
    emit!(sorted_to_deltas(&[3, 4, 6, 7]), 3, 2, 0);

    // ---- Single element with all mutations ----
    for mk in 0u8..=2 {
        emit!(vec![], 1, 1, mk);
        emit!(vec![], 1, 1_000_000_000, mk);
        emit!(vec![], 1_000_000_000, 1, mk);
        emit!(vec![], 1_000_000_000, 1_000_000_000, mk);
        emit!(vec![], 500_000_000, 100, mk);
    }

    // ---- Small hand-crafted arrays ----
    for mk in 0u8..=2 {
        emit!(sorted_to_deltas(&[1, 2, 3, 4, 5]), 1, 1, mk);
        emit!(sorted_to_deltas(&[2, 4, 6, 8, 10]), 2, 2, mk);
        emit!(sorted_to_deltas(&[5, 10, 15, 20]), 5, 5, mk);
        emit!(sorted_to_deltas(&[1, 100, 200]), 1, 50, mk);
        emit!(sorted_to_deltas(&[10, 20, 30, 40, 50]), 10, 3, mk);
    }

    // ---- Size classes with random generation ----
    while count < goal {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 10000),
        };

        let max_delta = std::cmp::max(1, std::cmp::min(999_999_999i64 / n as i64, 100_000)) as i32;
        let deltas = random_deltas(&mut rng, n, max_delta);

        let delta_sum: i64 = deltas.iter().map(|&d| d as i64).sum();
        let max_base = std::cmp::min(1_000_000_000i64 - delta_sum, 1_000_000_000i64);
        if max_base < 1 {
            continue;
        }
        let base = rng.gen_range_i64(1, max_base) as i32;

        let dist = if count % 5 == 0 {
            1
        } else if count % 7 == 0 {
            1_000_000_000
        } else {
            rng.gen_range_i64(1, 1_000_000_000) as i32
        };

        let mk = (count % 3) as u8;
        emit!(deltas, base, dist, mk);
    }

    eprintln!("Generated {} test cases", count);
}
