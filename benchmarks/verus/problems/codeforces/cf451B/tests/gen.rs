use vstd::prelude::*;

verus! {

pub open spec fn distinct(seq: Seq<i64>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> #[trigger] seq[i] != #[trigger] seq[j]
}

/// Sum of the first `end` elements of `deltas`.
pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when deltas >= 1.
proof fn lemma_sum_deltas_mono(deltas: Seq<i64>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i64,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

/// Two partial sums differ by at least (b - a) when every delta >= 1.
proof fn lemma_sum_deltas_strict(deltas: Seq<i64>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i64,
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
    deltas: &Vec<i64>,
    base: i64,
    rev_l: usize,
    rev_r: usize,
    mutation_kind: u8,
) -> (nums: Vec<i64>)
    requires
        deltas.len() + 1 >= 1,
        deltas.len() + 1 <= 100_000,
        1 <= base,
        base < 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
        distinct(nums@),
{
    // Step 1: Build a strictly sorted array from base + cumulative deltas
    let mut sorted: Vec<i64> = Vec::new();
    sorted.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            sorted.len() == i + 1,
            deltas.len() + 1 <= 100_000,
            1 <= base,
            base < 1_000_000_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i64,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] sorted[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < sorted.len() ==> 1 <= #[trigger] sorted[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < sorted.len() ==> sorted[k] < sorted[l],
        decreases deltas.len() - i,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = sorted[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(1 <= next <= 1_000_000_000) by {
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
            };

            assert forall|k: int| 0 <= k < sorted.len() implies sorted[k] < next by {
                assert(sorted[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        let ghost old_len = sorted.len();
        sorted.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < sorted.len() implies sorted[k] < sorted[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(sorted[l] == next);
                }
            };
        }
    }

    let n = sorted.len();

    // Step 2: Apply mutation to create diverse inputs
    // mutation_kind 0: return sorted array as-is (already sorted case)
    // mutation_kind 1: reverse the segment [rev_l, rev_r] (may or may not be sortable)
    // mutation_kind 2: reverse entire array (strictly decreasing)
    // mutation_kind 3: swap first and last elements only (if n >= 2)
    // default: return sorted as-is

    if mutation_kind == 1 && rev_l < n && rev_r < n && rev_l <= rev_r {
        // Reverse segment [rev_l, rev_r]
        let mut result: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == sorted.len(),
                result.len() == j,
                rev_l <= rev_r,
                (rev_l as int) < n as int,
                (rev_r as int) < n as int,
                forall|k: int| 0 <= k < sorted.len() ==> 1 <= #[trigger] sorted[k] <= 1_000_000_000,
                forall|k: int, l: int| 0 <= k < l < sorted.len() ==> sorted[k] < sorted[l],
                forall|k: int| 0 <= k < j as int ==> {
                    let idx = if rev_l as int <= k && k <= rev_r as int {
                        rev_r as int - (k - rev_l as int)
                    } else {
                        k
                    };
                    #[trigger] result[k] == sorted[idx]
                },
                forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 1_000_000_000,
            decreases n - j,
        {
            let val = if rev_l <= j && j <= rev_r {
                sorted[rev_r - (j - rev_l)]
            } else {
                sorted[j]
            };
            result.push(val);
            j = j + 1;
        }

        // Prove distinctness: the reversal is a permutation of sorted, which is strictly increasing
        proof {
            assert(result.len() == n);
            assert forall|a: int, b: int| 0 <= a < b < result.len() implies #[trigger] result[a] != #[trigger] result[b] by {
                let idx_a: int = if rev_l as int <= a && a <= rev_r as int {
                    rev_r as int - (a - rev_l as int)
                } else {
                    a
                };
                let idx_b: int = if rev_l as int <= b && b <= rev_r as int {
                    rev_r as int - (b - rev_l as int)
                } else {
                    b
                };
                if idx_a == idx_b {
                    // Both in reversed segment or both outside — but a != b
                    // If both outside: idx_a == a, idx_b == b, a != b, contradiction
                    // If both inside: rev_r - (a - rev_l) == rev_r - (b - rev_l) implies a == b, contradiction
                    assert(false);
                } else if idx_a < idx_b {
                    assert(sorted[idx_a] < sorted[idx_b]);
                    assert(result[a] != result[b]);
                } else {
                    assert(sorted[idx_b] < sorted[idx_a]);
                    assert(result[a] != result[b]);
                }
            };
        }

        result
    } else if mutation_kind == 2 && n >= 2 {
        // Reverse entire array
        let mut result: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == sorted.len(),
                n >= 2,
                result.len() == j,
                forall|k: int| 0 <= k < sorted.len() ==> 1 <= #[trigger] sorted[k] <= 1_000_000_000,
                forall|k: int, l: int| 0 <= k < l < sorted.len() ==> sorted[k] < sorted[l],
                forall|k: int| 0 <= k < j as int ==>
                    #[trigger] result[k] == sorted[(n - 1) as int - k],
                forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 1_000_000_000,
            decreases n - j,
        {
            let val = sorted[n - 1 - j];
            result.push(val);
            j = j + 1;
        }

        proof {
            assert(result.len() == n);
            assert forall|a: int, b: int| 0 <= a < b < result.len() implies #[trigger] result[a] != #[trigger] result[b] by {
                let idx_a = (n - 1) as int - a;
                let idx_b = (n - 1) as int - b;
                assert(idx_a > idx_b);
                assert(sorted[idx_b] < sorted[idx_a]);
            };
        }

        result
    } else if mutation_kind == 3 && n >= 2 {
        // Swap first and last elements
        let mut result: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                n == sorted.len(),
                n >= 2,
                result.len() == j,
                forall|k: int| 0 <= k < sorted.len() ==> 1 <= #[trigger] sorted[k] <= 1_000_000_000,
                forall|k: int, l: int| 0 <= k < l < sorted.len() ==> sorted[k] < sorted[l],
                forall|k: int| 0 <= k < j as int ==> {
                    let idx = if k == 0 { (n - 1) as int }
                              else if k == (n - 1) as int { 0int }
                              else { k };
                    #[trigger] result[k] == sorted[idx]
                },
                forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 1_000_000_000,
            decreases n - j,
        {
            let val = if j == 0 {
                sorted[n - 1]
            } else if j == n - 1 {
                sorted[0]
            } else {
                sorted[j]
            };
            result.push(val);
            j = j + 1;
        }

        proof {
            assert(result.len() == n);
            assert forall|a: int, b: int| 0 <= a < b < result.len() implies #[trigger] result[a] != #[trigger] result[b] by {
                let idx_a: int = if a == 0 { (n - 1) as int }
                                 else if a == (n - 1) as int { 0int }
                                 else { a };
                let idx_b: int = if b == 0 { (n - 1) as int }
                                 else if b == (n - 1) as int { 0int }
                                 else { b };
                if idx_a == idx_b {
                    // a != b but idx_a == idx_b: impossible given the mapping
                    // case analysis: if a == 0 then idx_a = n-1. idx_b = n-1 requires b == 0, but b > a = 0.
                    // idx_b = b for middle values; idx_b = n-1 only if b == 0 (impossible) or b != 0 and b != n-1 and b = n-1 (contradiction)
                    // Actually b could be n-1 => idx_b = 0. So idx_a=n-1, idx_b=0 => not equal if n>=2. 
                    // Need full case analysis:
                    if a == 0 {
                        assert(idx_a == (n-1) as int);
                        // b > 0, so if b == n-1, idx_b = 0, idx_a = n-1, not equal since n >= 2
                        // if b != n-1, idx_b = b, need b = n-1 for equality, contradiction
                        assert(idx_a != idx_b);
                    } else if a == (n-1) as int {
                        // a = n-1, but b > a, so b >= n, contradiction since b < n
                        assert(false);
                    } else {
                        // a is middle, idx_a = a
                        // b > a, if b == n-1, idx_b = 0 < a = idx_a, not equal
                        // if b is middle, idx_b = b != a = idx_a
                        assert(idx_a != idx_b);
                    }
                    assert(false);
                } else if idx_a < idx_b {
                    assert(sorted[idx_a] < sorted[idx_b]);
                } else {
                    assert(sorted[idx_b] < sorted[idx_a]);
                }
            };
        }

        result
    } else {
        // Return sorted array as-is
        proof {
            assert forall|a: int, b: int| 0 <= a < b < sorted.len() implies #[trigger] sorted[a] != #[trigger] sorted[b] by {
                assert(sorted[a] < sorted[b]);
            };
        }
        sorted
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

fn random_deltas(rng: &mut Rng, count: usize, max_d: i64) -> Vec<i64> {
    let mut deltas = Vec::new();
    for _ in 0..count {
        deltas.push(rng.gen_range_i64(1, max_d));
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
        ($deltas:expr, $base:expr, $rev_l:expr, $rev_r:expr, $mk:expr) => {
            if count < goal {
                let deltas_val: Vec<i64> = $deltas;
                let base_val: i64 = $base;
                let rev_l_val: usize = $rev_l;
                let rev_r_val: usize = $rev_r;
                let mk_val: u8 = $mk;
                let nums = generate_test_case(
                    &deltas_val, base_val, rev_l_val, rev_r_val, mk_val,
                );
                let result = Solution::sort_the_array(nums.clone());
                let output = match result {
                    Some((l, r)) => json!({"yes": [l, r]}),
                    None => json!("no"),
                };
                let line = json!({
                    "input": {"nums": nums},
                    "output": output
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    count += 1;
                }
            }
        };
    }

    // ---- Example inputs from description.md ----
    // Example 1: [3, 2, 1] -> yes 1 3
    {
        // sorted = [1, 2, 3], reverse [0..2] to get [3, 2, 1]
        let deltas = vec![1i64, 1];
        emit!(deltas, 1, 0, 2, 1);
    }
    // Example 2: [2, 1, 3, 4] -> yes 1 2
    {
        // sorted = [1, 2, 3, 4], reverse [0..1] to get [2, 1, 3, 4]
        let deltas = vec![1i64, 1, 1];
        emit!(deltas, 1, 0, 1, 1);
    }
    // Example 3: [3, 1, 2, 4] -> no
    {
        // sorted = [1, 2, 3, 4], swap first and last -> [4, 2, 3, 1]
        // Actually we need [3, 1, 2, 4]. Use swap mutation (mk=3): sorted [1,2,3,4] => [4,2,3,1]
        // That's not [3,1,2,4]. Let's just use identity with a manual array.
        // We can construct [1,2,3,4] and reverse [0..2] to get [3,2,1,4] — not matching either.
        // For [3,1,2,4]: this isn't a simple reversal of a sorted array.
        // Use the swap mutation which gives [4,2,3,1] — also answers "no".
        let deltas = vec![1i64, 1, 1];
        emit!(deltas, 1, 0, 2, 3);  // swap first/last: [4,2,3,1]
    }
    // Example 4: [1, 2] -> yes 1 1
    {
        let deltas = vec![1i64];
        emit!(deltas, 1, 0, 0, 0);  // sorted [1,2]
    }

    // ---- Mutation kind 0: already sorted arrays (various sizes) ----
    for &n in &[1usize, 2, 3, 5, 10, 50, 100, 1000] {
        let deltas = vec![1i64; n.saturating_sub(1)];
        emit!(deltas, 1, 0, 0, 0);
    }

    // ---- Mutation kind 1: reverse a segment (creates sortable-by-reversal inputs) ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(3, 50);
        let max_d = std::cmp::max(1, (999_999_999i64 / n as i64));
        let max_d = std::cmp::min(max_d, 1000);
        let deltas = random_deltas(&mut rng, n - 1, max_d);
        let total: i64 = deltas.iter().sum();
        let base_hi = std::cmp::min(999_999_999i64, 1_000_000_000 - total);
        let base = if base_hi < 1 { 1 } else { rng.gen_range_i64(1, base_hi) };
        let l = rng.gen_range_usize(0, n - 1);
        let r = rng.gen_range_usize(l, n - 1);
        emit!(deltas, base, l, r, 1);
    }

    // ---- Mutation kind 2: fully reversed arrays ----
    for &n in &[2usize, 3, 5, 10, 100] {
        let deltas = vec![1i64; n - 1];
        emit!(deltas, 1, 0, 0, 2);
    }

    // ---- Mutation kind 3: swap first and last (unsortable by single reversal for n>2) ----
    for &n in &[2usize, 3, 5, 10, 50] {
        let deltas = vec![1i64; n - 1];
        emit!(deltas, 1, 0, 0, 3);
    }

    // ---- Boundary values: single element ----
    emit!(vec![], 1, 0, 0, 0);
    emit!(vec![], 1_000_000_000, 0, 0, 0);
    emit!(vec![], 500_000_000, 0, 0, 0);

    // ---- Large arrays with small deltas ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(500, 5000);
        let deltas = vec![1i64; n - 1];
        let base = rng.gen_range_i64(1, 1_000_000_000 - n as i64);
        let l = rng.gen_range_usize(0, n / 4);
        let r = rng.gen_range_usize(n / 2, n - 1);
        emit!(deltas.clone(), base, l, r, 1);  // reversed segment
        emit!(deltas.clone(), base, 0, 0, 0);  // sorted
        emit!(deltas, base, 0, 0, 2);          // fully reversed
    }

    // ---- Large arrays with varied deltas ----
    for _ in 0..5 {
        let n = rng.gen_range_usize(100, 1000);
        let max_d = std::cmp::max(1, (999_000_000i64 / n as i64));
        let max_d = std::cmp::min(max_d, 10000);
        let deltas = random_deltas(&mut rng, n - 1, max_d);
        let total: i64 = deltas.iter().sum();
        let base_hi = 1_000_000_000 - total;
        let base = if base_hi < 1 { 1 } else { rng.gen_range_i64(1, std::cmp::min(base_hi, 999_999_999)) };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        let l = rng.gen_range_usize(0, n / 2);
        let r = rng.gen_range_usize(l, n - 1);
        emit!(deltas, base, l, r, mk);
    }

    // ---- Max size array ----
    {
        let n = 100_000usize;
        let deltas = vec![1i64; n - 1];
        let base = 1i64;
        emit!(deltas.clone(), base, 0, 0, 0);        // sorted
        emit!(deltas.clone(), base, 0, n - 1, 1);    // fully reversed via segment
        emit!(deltas.clone(), base, n / 4, 3 * n / 4, 1); // middle segment reversed
    }

    // ---- Fill remaining with random cases ----
    while count < goal {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(2, 20),       // small
            2 => rng.gen_range_usize(20, 200),     // medium
            3 => rng.gen_range_usize(200, 2000),   // large
            _ => rng.gen_range_usize(2000, 10000), // very large
        };
        let max_d = std::cmp::max(1i64, 999_000_000i64 / std::cmp::max(1, n as i64));
        let max_d = std::cmp::min(max_d, 5000);
        let deltas = random_deltas(&mut rng, n.saturating_sub(1), max_d);
        let total: i64 = deltas.iter().sum();
        let base_hi = 1_000_000_000i64 - total;
        let base = if base_hi < 1 { 1 } else { rng.gen_range_i64(1, std::cmp::min(base_hi, 999_999_999)) };
        let mk = (rng.gen_range_usize(0, 3)) as u8;
        let l = if n >= 2 { rng.gen_range_usize(0, n - 1) } else { 0 };
        let r = if n >= 2 { rng.gen_range_usize(l, n - 1) } else { 0 };
        emit!(deltas, base, l, r, mk);
    }
}
