use vstd::prelude::*;

verus! {

// ---------- spec fn helpers (from spec.rs) ----------

pub open spec fn count_occurrences(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occurrences(s.drop_last(), value) +
            if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

// ---------- proof helpers ----------

proof fn lemma_count_push(s: Seq<i32>, x: i32, v: i32)
    ensures
        count_occurrences(s.push(x), v) ==
            count_occurrences(s, v) + if x == v { 1nat } else { 0nat },
{
    assert(s.push(x).drop_last() =~= s);
}

proof fn lemma_count_zero_if_absent(s: Seq<i32>, v: i32)
    requires
        forall|j: int| 0 <= j < s.len() ==> s[j] != v,
    ensures
        count_occurrences(s, v) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        assert forall|j: int| 0 <= j < s.drop_last().len()
            implies s.drop_last()[j] != v by {
            assert(s.drop_last()[j] == s[j]);
        };
        lemma_count_zero_if_absent(s.drop_last(), v);
    }
}

/// Build a sorted array with exactly one single element and all other values paired.
/// Single element is always placed at the end: base + n_pairs.
/// Pairs are base, base, base+1, base+1, ..., base+n_pairs-1, base+n_pairs-1.
pub fn generate_test_case(
    n_pairs: u32,
    base: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        n_pairs <= 49_999,
        0 <= base,
        base + n_pairs as int <= 100_000,
    ensures
        1 <= result.len() <= 100_000,
        result.len() % 2 == 1,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100_000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> #[trigger] result[i] <= #[trigger] result[j],
        exists|single: i32| {
            &&& count_occurrences(result@, single) == 1
            &&& forall|v: i32| v != single && (exists|i: int| 0 <= i < result@.len() && result@[i] == v)
                    ==> #[trigger] count_occurrences(result@, v) == 2
        },
{
    let single_val: i32 = base + n_pairs as i32;
    let mut nums: Vec<i32> = Vec::new();

    // Build pairs: [base, base, base+1, base+1, ...]
    let mut j: u32 = 0;
    while j < n_pairs
        invariant
            0 <= j <= n_pairs <= 49_999,
            0 <= base,
            base + n_pairs as int <= 100_000,
            single_val == base + n_pairs as int,
            nums.len() == 2 * j as int,
            forall|k: int| 0 <= k < nums.len() ==>
                #[trigger] nums[k] == (base + k / 2) as i32,
            forall|k: int| 0 <= k < nums.len() ==>
                0 <= #[trigger] nums[k] <= 100_000,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==>
                #[trigger] nums[k] <= #[trigger] nums[l],
            // All elements strictly less than single_val
            forall|k: int| 0 <= k < nums.len() ==> nums[k] < single_val,
            // Count tracking: single_val never appears
            count_occurrences(nums@, single_val) == 0,
            // Every value that appears has count exactly 2
            forall|v: i32| (exists|idx: int| 0 <= idx < nums@.len() && nums@[idx] == v)
                ==> #[trigger] count_occurrences(nums@, v) == 2,
        decreases n_pairs - j,
    {
        let val = base + j as i32;

        // Prove val hasn't appeared yet
        proof {
            assert forall|k: int| 0 <= k < nums.len() implies nums[k] != val by {
                assert(nums[k] == (base + k / 2) as i32);
                assert(k / 2 < j as int);
            };
            lemma_count_zero_if_absent(nums@, val);
        }

        let ghost s0 = nums@;
        nums.push(val);

        proof {
            lemma_count_push(s0, val, single_val);
            assert(val != single_val);
        }

        let ghost s1 = nums@;
        nums.push(val);

        proof {
            assert(nums@ =~= s1.push(val));
            lemma_count_push(s1, val, single_val);
            lemma_count_push(s1, val, val);
            lemma_count_push(s0, val, val);

            assert forall|v: i32| (exists|idx: int| 0 <= idx < nums@.len() && nums@[idx] == v)
                implies #[trigger] count_occurrences(nums@, v) == 2 by {
                lemma_count_push(s1, val, v);
                lemma_count_push(s0, val, v);
                if v == val {
                } else {
                    let idx = choose|idx: int| 0 <= idx < nums@.len() && nums@[idx] == v;
                    if idx < s0.len() as int {
                    } else {
                        assert(false);
                    }
                }
            };

            assert(nums.len() == 2 * j as int + 2);
            assert forall|k: int| 0 <= k < nums.len() implies
                #[trigger] nums[k] == (base + k / 2) as i32 by {
                if k < s0.len() as int {
                } else if k == s0.len() as int {
                    assert(k == 2 * j as int);
                    assert(k / 2 == j as int);
                } else {
                    assert(k == 2 * j as int + 1);
                    assert(k / 2 == j as int);
                }
            };
            assert forall|k: int| 0 <= k < nums.len() implies
                0 <= #[trigger] nums[k] <= 100_000 by {
                assert(nums[k] == (base + k / 2) as i32);
            };
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies
                #[trigger] nums[k] <= #[trigger] nums[l] by {
                assert(nums[k] == (base + k / 2) as i32);
                assert(nums[l] == (base + l / 2) as i32);
            };
            assert forall|k: int| 0 <= k < nums.len() implies nums[k] < single_val by {
                assert(nums[k] == (base + k / 2) as i32);
                assert(k / 2 <= j as int);
            };
        }

        j = j + 1;
    }

    // Push single element at end
    let ghost s_final = nums@;
    nums.push(single_val);

    proof {
        lemma_count_push(s_final, single_val, single_val);

        assert(nums.len() == 2 * n_pairs as int + 1);
        assert(nums.len() % 2 == 1);
        assert(1 <= nums.len() <= 100_000);
        assert(0 <= single_val <= 100_000);

        assert forall|i_idx: int| 0 <= i_idx < nums.len() implies
            0 <= #[trigger] nums[i_idx] <= 100_000 by {
            if i_idx < s_final.len() as int {
            } else {
                assert(nums[i_idx] == single_val);
            }
        };

        assert forall|i_idx: int, j_idx: int| 0 <= i_idx < j_idx < nums.len() implies
            #[trigger] nums[i_idx] <= #[trigger] nums[j_idx] by {
            if j_idx < s_final.len() as int {
            } else if i_idx < s_final.len() as int {
            }
        };

        assert(count_occurrences(nums@, single_val) == 1nat);

        assert forall|v: i32| v != single_val &&
            (exists|i_idx: int| 0 <= i_idx < nums@.len() && nums@[i_idx] == v)
            implies #[trigger] count_occurrences(nums@, v) == 2 by {
            lemma_count_push(s_final, single_val, v);
            let witness = choose|i_idx: int| 0 <= i_idx < nums@.len() && nums@[i_idx] == v;
            if witness >= s_final.len() as int {
                assert(false);
            }
        };
    }

    nums
}

} // verus!

// ---- Unverified runtime code ----

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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::single_non_duplicate(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *emitted += 1;
    };

    // ---- Example inputs from description.md ----
    emit(vec![1,1,2,3,3,4,4,8,8], &mut seen, &mut out, &mut emitted);
    emit(vec![3,3,7,7,10,11,11], &mut seen, &mut out, &mut emitted);

    // ---- Boundary: single element ----
    emit(generate_test_case(0, 0, 0), &mut seen, &mut out, &mut emitted);       // [0]
    emit(generate_test_case(0, 100_000, 0), &mut seen, &mut out, &mut emitted); // [100000]

    // ---- Small arrays with all mutation kinds ----
    for mk in 0u8..=5 {
        // 3 elements: single at end
        emit(generate_test_case(1, 0, mk), &mut seen, &mut out, &mut emitted);
        emit(generate_test_case(1, 50_000, mk), &mut seen, &mut out, &mut emitted);

        // 5 elements
        emit(generate_test_case(2, 0, mk), &mut seen, &mut out, &mut emitted);
        emit(generate_test_case(2, 100, mk), &mut seen, &mut out, &mut emitted);
        emit(generate_test_case(2, 99_998, mk), &mut seen, &mut out, &mut emitted);
    }

    // ---- Medium arrays ----
    for mk in 0u8..=3 {
        emit(generate_test_case(5, 10, mk), &mut seen, &mut out, &mut emitted);
        emit(generate_test_case(5, 0, mk), &mut seen, &mut out, &mut emitted);
        emit(generate_test_case(10, 0, mk), &mut seen, &mut out, &mut emitted);
        emit(generate_test_case(50, 100, mk), &mut seen, &mut out, &mut emitted);
        emit(generate_test_case(100, 0, mk), &mut seen, &mut out, &mut emitted);
    }

    // ---- Random test cases across size classes ----
    let mut _attempts = 0usize;
    while emitted < count {
        _attempts += 1; if _attempts > 10000 { break; }
        let n_pairs: u32 = match emitted % 5 {
            0 => rng.gen_range_usize(0, 2) as u32,           // tiny
            1 => rng.gen_range_usize(1, 10) as u32,          // small
            2 => rng.gen_range_usize(11, 100) as u32,        // medium
            3 => rng.gen_range_usize(101, 1000) as u32,      // large
            _ => rng.gen_range_usize(1001, 49_999) as u32,   // max
        };
        let max_base = 100_000i64 - n_pairs as i64;
        let base = rng.gen_range_i64(0, max_base) as i32;
        let mk = rng.gen_range_usize(0, 5) as u8;
        emit(generate_test_case(n_pairs, base, mk), &mut seen, &mut out, &mut emitted);
    }
}
