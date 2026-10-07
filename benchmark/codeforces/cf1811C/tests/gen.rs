use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when deltas >= 0.
proof fn lemma_sum_deltas_mono(deltas: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i64,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// sum_deltas is non-negative when all deltas >= 0.
proof fn lemma_sum_deltas_nonneg(deltas: Seq<i64>, end: int)
    requires
        0 <= end <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i64,
    ensures
        sum_deltas(deltas, end) >= 0,
    decreases end,
{
    if end > 0 {
        lemma_sum_deltas_nonneg(deltas, end - 1);
    }
}

pub fn generate_test_case(
    n: usize,
    base: i64,
    deltas: Vec<i64>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i64>))
    requires
        n >= 2,
        0 <= base <= 1_000_000_000i64,
        deltas.len() == n - 2,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        result.0 >= 2,
        result.1.len() == result.0 - 1,
        forall|i: int| 0 <= i < result.0 - 1 ==> 0 <= #[trigger] result.1[i] <= 1_000_000_000,
        forall|i: int| 1 <= i < result.0 as int - 2 ==> #[trigger] result.1[i] <= result.1[i - 1] || result.1[i] <= result.1[i + 1],
{
    if mutation_kind == 1 {
        // Constant array: all elements = base
        let mut b: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n - 1
            invariant
                0 <= j <= n - 1,
                n >= 2,
                b.len() == j as int,
                0 <= base <= 1_000_000_000i64,
                forall|k: int| 0 <= k < j as int ==> #[trigger] b[k] == base,
            decreases n - 1 - j,
        {
            b.push(base);
            j = j + 1;
        }
        assert forall|i: int| 1 <= i < n as int - 2
            implies (#[trigger] b[i] <= b[i - 1] || b[i] <= b[i + 1]) by {
            assert(b[i] == base);
            assert(b[i - 1] == base);
        };
        (n, b)
    } else if mutation_kind == 2 {
        // All zeros
        let mut b: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n - 1
            invariant
                0 <= j <= n - 1,
                n >= 2,
                b.len() == j as int,
                forall|k: int| 0 <= k < j as int ==> #[trigger] b[k] == 0i64,
            decreases n - 1 - j,
        {
            b.push(0i64);
            j = j + 1;
        }
        assert forall|i: int| 1 <= i < n as int - 2
            implies (#[trigger] b[i] <= b[i - 1] || b[i] <= b[i + 1]) by {
            assert(b[i] == 0i64);
            assert(b[i - 1] == 0i64);
        };
        (n, b)
    } else {
        // Non-decreasing construction from deltas (mutation_kind == 0 or fallback)
        let mut b: Vec<i64> = Vec::new();
        b.push(base);

        let mut k: usize = 0;
        while k < deltas.len()
            invariant
                0 <= k <= deltas.len(),
                b.len() == k as int + 1,
                deltas.len() == n - 2,
                n >= 2,
                0 <= base <= 1_000_000_000i64,
                forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
                base + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
                forall|j: int| 0 <= j <= k as int
                    ==> #[trigger] b[j] as int == base as int + sum_deltas(deltas@, j),
                forall|j: int| 0 <= j < b.len() ==> 0 <= #[trigger] b[j] <= 1_000_000_000,
                forall|j: int| 0 <= j < b.len() - 1 ==> #[trigger] b[j] <= b[j + 1],
            decreases deltas.len() - k,
        {
            let ghost old_len = b.len();

            proof {
                lemma_sum_deltas_mono(deltas@, (k + 1) as int, deltas.len() as int);
                lemma_sum_deltas_nonneg(deltas@, (k + 1) as int);
            }

            let next = b[k] + deltas[k];

            proof {
                assert(next as int == base as int + sum_deltas(deltas@, (k + 1) as int));
                assert(0 <= next <= 1_000_000_000) by {
                    assert(base as int + sum_deltas(deltas@, (k + 1) as int)
                        <= base as int + sum_deltas(deltas@, deltas.len() as int));
                    assert(sum_deltas(deltas@, (k + 1) as int) >= 0);
                };
                assert(next >= b[k as int]) by {
                    assert(deltas[k as int] >= 0i64);
                };
            }

            b.push(next);
            k = k + 1;

            proof {
                assert forall|j: int| 0 <= j <= k as int
                    implies #[trigger] b[j] as int
                        == base as int + sum_deltas(deltas@, j) by {
                    if j < k as int {
                    } else {
                        assert(b[j] == next);
                    }
                };
                assert forall|j: int| 0 <= j < b.len() - 1
                    implies #[trigger] b[j] <= b[j + 1] by {
                    if j < old_len as int - 1 {
                    } else {
                        assert(j == old_len as int - 1);
                        assert(b[j + 1] == next);
                    }
                };
            }
        }

        assert(b.len() == n - 1) by {
            assert(b.len() == k as int + 1);
            assert(k == deltas.len());
        };

        assert forall|i: int| 1 <= i < n as int - 2
            implies (#[trigger] b[i] <= b[i - 1] || b[i] <= b[i + 1]) by {
            assert(b[i] <= b[i + 1]);
        };

        (n, b)
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut total = 0usize;

    use std::io::Write;
    use std::collections::HashSet;
    let mut seen = HashSet::new();

    let mut emit = |n: usize, b: Vec<i64>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, total: &mut usize| {
        if *total >= count { return; }
        let key = format!("{},{:?}", n, b);
        if !seen.insert(key) { return; }
        let result = Solution::restore_array(n, b.clone());
        writeln!(out, "{}", json!({
            "input": {"n": n, "b": b},
            "output": result
        })).unwrap();
        *total += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(usize, Vec<i64>)> = vec![
        (5, vec![3, 4, 4, 5]),
        (4, vec![2, 2, 1]),
        (5, vec![0, 0, 0, 0]),
        (6, vec![0, 3, 4, 4, 3]),
        (2, vec![10]),
        (4, vec![3, 3, 3]),
        (5, vec![4, 2, 5, 5]),
        (4, vec![2, 1, 0]),
        (3, vec![4, 4]),
        (6, vec![8, 1, 3, 5, 10]),
    ];
    for (n, b) in &examples {
        emit(*n, b.clone(), &mut seen, &mut out, &mut total);
    }

    // Boundary and special cases via generator
    let special_cases: Vec<(usize, i64, Vec<i64>)> = vec![
        (2, 0, vec![]),
        (2, 1_000_000_000, vec![]),
        (3, 0, vec![0]),
        (3, 500_000_000, vec![500_000_000]),
        (4, 0, vec![0, 0]),
        (4, 100, vec![100, 200]),
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2];
    for (n, base, deltas) in &special_cases {
        for &mk in &mutation_kinds {
            let (rn, rb) = generate_test_case(*n, *base, deltas.clone(), mk);
            emit(rn, rb, &mut seen, &mut out, &mut total);
        }
    }

    // Random generation across size classes
    let size_classes: Vec<(usize, usize)> = vec![
        (2, 3),
        (4, 10),
        (11, 50),
        (51, 200),
        (201, 1000),
    ];
    for (lo, hi) in &size_classes {
        for _ in 0..10 {
            let n = rng.gen_range_usize(*lo, *hi);
            let base = rng.gen_range_i64(0, 999_000_000);
            let num_deltas = if n > 2 { n - 2 } else { 0 };
            let budget = 1_000_000_000i64 - base;
            let max_delta = if num_deltas > 0 { budget / num_deltas as i64 } else { 0 };
            let mut deltas = Vec::new();
            for _ in 0..num_deltas {
                if max_delta > 0 {
                    deltas.push(rng.gen_range_i64(0, max_delta));
                } else {
                    deltas.push(0);
                }
            }
            let mk = rng.gen_range_usize(0, 2) as u8;
            let (rn, rb) = generate_test_case(n, base, deltas, mk);
            emit(rn, rb, &mut seen, &mut out, &mut total);
        }
    }

    // Fill remaining with random inputs
    while total < count {
        let n = match total % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let base = if total % 10 == 0 {
            match total % 5 {
                0 => 0i64,
                1 => 1i64,
                2 => 1_000_000_000i64,
                3 => 999_999_999i64,
                _ => 500_000_000i64,
            }
        } else {
            rng.gen_range_i64(0, 999_000_000)
        };
        let num_deltas = if n > 2 { n - 2 } else { 0 };
        let budget = 1_000_000_000i64 - base;
        let max_delta = if num_deltas > 0 && budget > 0 {
            budget / num_deltas as i64
        } else {
            0
        };
        let mut deltas = Vec::new();
        for _ in 0..num_deltas {
            if max_delta > 0 {
                deltas.push(rng.gen_range_i64(0, max_delta));
            } else {
                deltas.push(0);
            }
        }
        let mk = rng.gen_range_usize(0, 2) as u8;
        let (rn, rb) = generate_test_case(n, base, deltas, mk);
        emit(rn, rb, &mut seen, &mut out, &mut total);
    }
}
