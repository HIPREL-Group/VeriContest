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

/// Builds a Vec of unique skill values in [1, 1_000_000] from deltas,
/// and applies k-mutations for diversity.
pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= deltas.len() <= 99999,
        1 <= base,
        1 <= k <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000,
    ensures
        2 <= result.0.len() <= 100000,
        1 <= result.1 <= 1_000_000_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
{
    let mut skills: Vec<i32> = Vec::new();

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(sum_deltas(deltas@, 0) == 0int);
        assert(sum_deltas(deltas@, deltas.len() as int) >= 0);
        assert(base as int <= 1_000_000);
    }

    skills.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            skills.len() == i + 1,
            1 <= deltas.len() <= 99999,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                skills[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < skills.len() ==> 1 <= #[trigger] skills[k] <= 1_000_000,
            forall|k: int, l: int| 0 <= k < l < skills.len() ==> skills[k] < skills[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = skills.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = skills[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(1 <= next <= 1_000_000) by {
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                assert(next as int >= base as int >= 1);
                assert(next as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(next as int <= 1_000_000);
            };

            assert forall|k: int| 0 <= k < skills.len() implies skills[k] < next by {
                assert(skills[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        skills.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < skills.len() implies skills[k] < skills[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(skills[l] == next);
                }
            };
        }
    }

    // Apply k mutation
    let mutated_k: i32 =
        if mutation_kind == 1 {
            1i32                                      // minimum k
        } else if mutation_kind == 2 {
            1_000_000_000i32                          // maximum k
        } else if mutation_kind == 3 {
            (skills.len() - 1) as i32                 // k = n-1
        } else if mutation_kind == 4 {
            skills.len() as i32                       // k = n
        } else {
            k                                         // identity
        };

    // Prove uniqueness from strict monotonicity
    proof {
        assert forall |i: int, j: int| 0 <= i < j < skills.len() implies skills[i] != skills[j] by {
            assert(skills[i] < skills[j]);
        };
    }

    (skills, mutated_k)
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

    fn shuffle(&mut self, v: &mut Vec<i32>) {
        let n = v.len();
        for i in (1..n).rev() {
            let j = self.gen_range_usize(0, i);
            v.swap(i, j);
        }
    }
}

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn random_deltas(rng: &mut Rng, n: usize, max_delta: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(1, max_delta as i64) as i32);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3175);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n_emitted = 0usize;

    macro_rules! emit {
        ($skills:expr, $k:expr) => {
            if n_emitted < count {
                let skills_val: Vec<i32> = $skills;
                let k_val: i32 = $k;
                let result = Solution::find_winning_player(skills_val.clone(), k_val);
                let line = json!({
                    "input": {"skills": skills_val, "k": k_val},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    n_emitted += 1;
                }
            }
        };
    }

    macro_rules! gen_emit {
        ($deltas:expr, $base:expr, $k:expr, $mk:expr, $shuffle:expr) => {
            if n_emitted < count {
                let deltas_val: Vec<i32> = $deltas;
                let base_val: i32 = $base;
                let k_val: i32 = $k;
                let mk_val: u8 = $mk;
                let (mut skills, k_out) = generate_test_case(
                    &deltas_val, base_val, k_val, mk_val,
                );
                if $shuffle {
                    rng.shuffle(&mut skills);
                }
                emit!(skills, k_out);
            }
        };
    }

    // ---- LeetCode examples (unsorted, emitted directly) ----
    emit!(vec![4, 2, 6, 3, 9], 2);
    emit!(vec![2, 5, 4], 3);

    // ---- Small arrays (2-5 elements), all k mutations, shuffled ----
    for mk in 0u8..=4 {
        gen_emit!(vec![1], 1, 5, mk, true);
        gen_emit!(vec![1, 1], 1, 3, mk, true);
        gen_emit!(vec![1, 1, 1, 1], 1, 2, mk, true);
        gen_emit!(vec![100_000], 1, 1_000_000_000, mk, false);
    }

    // ---- Boundary values ----
    gen_emit!(vec![1], 999_999, 1, 0, false);
    gen_emit!(vec![1], 1, 1_000_000_000, 0, false);
    gen_emit!(vec![1; 9], 1, 1, 0, true);

    // ---- Random tiny arrays (2-5 elements) with all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(2, 5);
        let max_d = std::cmp::max(1, std::cmp::min(500_000, (999_999i64 / n as i64) as i32));
        let deltas = random_deltas(&mut rng, n, max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        if hi < 1 { continue; }
        let base = rng.gen_range_i64(1, hi) as i32;
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        for mk in 0u8..=4 {
            gen_emit!(deltas.clone(), base, k, mk, true);
        }
    }

    // ---- Random small arrays (6-20 elements) ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(6, 20);
        let max_d = std::cmp::max(1, std::cmp::min(100_000, (999_999i64 / n as i64) as i32));
        let deltas = random_deltas(&mut rng, n, max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        if hi < 1 { continue; }
        let base = rng.gen_range_i64(1, hi) as i32;
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.next_u64() % 5) as u8;
        gen_emit!(deltas.clone(), base, k, mk, true);
        gen_emit!(deltas.clone(), base, k, 0, false);
    }

    // ---- Random medium arrays (50-500 elements) ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(50, 500);
        let max_d = std::cmp::max(1, std::cmp::min(1000, (999_999i64 / n as i64) as i32));
        let deltas = random_deltas(&mut rng, n, max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        if hi < 1 { continue; }
        let base = rng.gen_range_i64(1, hi) as i32;
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.next_u64() % 5) as u8;
        gen_emit!(deltas.clone(), base, k, mk, true);
    }

    // ---- Random large arrays (1000-10000 elements), delta=1 ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(1000, 10000);
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        if hi < 1 { continue; }
        let base = rng.gen_range_i64(1, hi) as i32;
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.next_u64() % 5) as u8;
        gen_emit!(deltas.clone(), base, k, mk, true);
    }

    // ---- Max size array (100000 elements), delta=1 ----
    {
        let n = 100000usize;
        let deltas = vec![1i32; n - 1];
        let base = 1i32;
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        gen_emit!(deltas, base, k, 0, true);
    }

    // ---- Fill remaining with random diverse cases ----
    while n_emitted < count {
        let n = match rng.next_u64() % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 200),
            3 => rng.gen_range_usize(200, 2000),
            _ => rng.gen_range_usize(2000, 10000),
        };
        let max_d = std::cmp::max(1, std::cmp::min(100, (999_999i64 / n as i64) as i32));
        let deltas = random_deltas(&mut rng, n, max_d);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(999_999i64, 1_000_000 - total);
        if hi < 1 { continue; }
        let base = rng.gen_range_i64(1, hi) as i32;
        let k = rng.gen_range_i64(1, 1_000_000_000) as i32;
        let mk = (rng.next_u64() % 5) as u8;
        let shuffle = rng.next_u64() % 2 == 0;
        gen_emit!(deltas, base, k, mk, shuffle);
    }

    eprintln!("Generated {} test cases", n_emitted);
}
