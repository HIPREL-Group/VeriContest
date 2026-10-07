use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when every delta >= 1.
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

/// Builds a valid `nums` array for find_peak_element from construction
/// parameters.  The array is built as a strictly increasing sequence
/// `base, base+d0, base+d0+d1, …` which trivially satisfies the
/// adjacency‐difference requirement.  Mutations tweak the result to
/// create peaks at different positions while preserving the invariant.
pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        0 <= deltas.len() <= 999,
        -1_000_000 <= base <= 1_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i] <= 1000,
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_999_000,
    ensures
        1 <= result.len() <= 1000,
        forall |i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] != result[i + 1],
{
    // ── Build strictly increasing array ──────────────────────────────
    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(base as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
        assert(base <= 1_999_000i32);
    }

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            nums.len() == i + 1,
            deltas.len() <= 999,
            -1_000_000 <= base <= 1_000_000,
            forall|k: int| 0 <= k < deltas.len() ==> 1 <= #[trigger] deltas[k] <= 1000,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_999_000,
            forall|k: int| 0 <= k <= i as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> -1_000_000 <= #[trigger] nums[k],
            forall|k: int| 0 <= k < nums.len() ==> #[trigger] nums[k] <= 1_999_000i32,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] < nums[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
            lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
        }

        let next = nums[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));

            assert(next as int <= 1_999_000) by {
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
            };

            assert(next as int >= base as int) by {
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
            };

            assert forall|k: int| 0 <= k < nums.len() implies nums[k] < next by {
                assert(nums[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        nums.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < nums.len()
                implies nums[k] < nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    // ── Apply mutation ───────────────────────────────────────────────
    if mutation_kind == 0 {
        // Identity: return strictly increasing array (peak at last index)
        proof {
            assert forall |j: int| 0 <= j < nums.len() - 1
                implies #[trigger] nums[j] != nums[j + 1] by {
                assert(nums[j] < nums[j + 1]);
            };
        }
        nums
    } else if mutation_kind == 1 && nums.len() > 1 {
        // Shrink: pop last element (still strictly increasing)
        let ghost pre_pop = nums@;
        let _dropped = nums.pop();
        proof {
            assert(nums.len() >= 1);
            assert forall |j: int| 0 <= j < nums.len() - 1
                implies #[trigger] nums[j] != nums[j + 1] by {
                assert(nums[j] == pre_pop[j]);
                assert(nums[j + 1] == pre_pop[j + 1]);
                assert(pre_pop[j] < pre_pop[j + 1]);
            };
        }
        nums
    } else if mutation_kind == 2 && nums.len() >= 2 {
        // Peak at end-1: set last element below its predecessor
        let last = nums.len() - 1;
        let prev_val = nums[last - 1];
        let new_val: i32 = prev_val - 1;
        proof {
            assert(prev_val as int >= -1_000_000);
        }
        let ghost pre_set = nums@;
        nums.set(last, new_val);
        proof {
            assert forall |j: int| 0 <= j < nums.len() - 1
                implies #[trigger] nums[j] != nums[j + 1] by {
                if j == last as int - 1 {
                    assert(nums[j] == prev_val);
                    assert(nums[j + 1] as int == prev_val as int - 1);
                } else {
                    assert(nums[j] == pre_set[j]);
                    assert(nums[j + 1] == pre_set[j + 1]);
                    assert(pre_set[j] < pre_set[j + 1]);
                }
            };
        }
        nums
    } else if mutation_kind == 3 && nums.len() >= 2 {
        // Peak at 0: set first element above its successor
        let second_val = nums[1];
        let new_val: i32 = second_val + 1;
        proof {
            assert(second_val as int <= 1_999_000);
        }
        let ghost pre_set = nums@;
        nums.set(0, new_val);
        proof {
            assert forall |j: int| 0 <= j < nums.len() - 1
                implies #[trigger] nums[j] != nums[j + 1] by {
                if j == 0 {
                    assert(nums[0] as int == second_val as int + 1);
                    assert(nums[1] == second_val);
                } else {
                    assert(nums[j] == pre_set[j]);
                    assert(nums[j + 1] == pre_set[j + 1]);
                    assert(pre_set[j] < pre_set[j + 1]);
                }
            };
        }
        nums
    } else if mutation_kind == 4 && nums.len() >= 3 {
        // Peak in middle: set mid element above its successor
        let mid = nums.len() / 2;
        let succ_val = nums[mid + 1];
        let new_val: i32 = succ_val + 1;
        proof {
            assert(succ_val as int <= 1_999_000);
        }
        let ghost pre_set = nums@;
        nums.set(mid, new_val);
        proof {
            assert forall |j: int| 0 <= j < nums.len() - 1
                implies #[trigger] nums[j] != nums[j + 1] by {
                if j == mid as int - 1 {
                    // nums[mid-1] unchanged, nums[mid] = succ_val + 1
                    // pre_set[mid-1] < pre_set[mid] < pre_set[mid+1] = succ_val
                    // so pre_set[mid-1] < succ_val, hence pre_set[mid-1] < succ_val + 1 = new_val
                    assert(nums[j] == pre_set[j]);
                    assert(nums[j + 1] as int == succ_val as int + 1);
                    assert(pre_set[j] < pre_set[mid as int]);
                    assert(pre_set[mid as int] < pre_set[mid as int + 1]);
                    assert(pre_set[mid as int + 1] == succ_val);
                } else if j == mid as int {
                    // nums[mid] = succ_val + 1, nums[mid+1] = succ_val
                    assert(nums[j] as int == succ_val as int + 1);
                    assert(nums[j + 1] == succ_val);
                } else {
                    assert(nums[j] == pre_set[j]);
                    assert(nums[j + 1] == pre_set[j + 1]);
                    assert(pre_set[j] < pre_set[j + 1]);
                }
            };
        }
        nums
    } else {
        // Fallback: identity
        proof {
            assert forall |j: int| 0 <= j < nums.len() - 1
                implies #[trigger] nums[j] != nums[j + 1] by {
                assert(nums[j] < nums[j + 1]);
            };
        }
        nums
    }
}

} // verus!

struct Solution;
include!("../code.rs");

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

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32, budget: i64) -> Vec<i32> {
    let mut deltas = Vec::new();
    let mut remaining = budget;
    for _ in 0..n {
        let max_this = (remaining - (n as i64 - deltas.len() as i64 - 1)).min(max_d as i64).max(1);
        let d = rng.gen_range_i64(1, max_this) as i32;
        deltas.push(d);
        remaining -= d as i64;
        if remaining <= 0 { break; }
    }
    deltas
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(162);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut n = 0usize;

    let mut emit = |nums: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    n: &mut usize| {
        if *n >= count { return; }
        let key = format!("{:?}", nums);
        if !seen.insert(key) { return; }
        let output = Solution::find_peak_element(nums.clone());
        writeln!(out, "{}", json!({"input": {"nums": nums}, "output": output})).unwrap();
        *n += 1;
    };

    // ── Examples from description ────────────────────────────────────
    emit(vec![1, 2, 3, 1], &mut seen, &mut out, &mut n);
    emit(vec![1, 2, 1, 3, 5, 6, 4], &mut seen, &mut out, &mut n);

    // ── Hand-crafted edge cases ──────────────────────────────────────
    emit(vec![1], &mut seen, &mut out, &mut n);
    emit(vec![2, 1], &mut seen, &mut out, &mut n);
    emit(vec![1, 2], &mut seen, &mut out, &mut n);
    emit(vec![3, 2, 1], &mut seen, &mut out, &mut n);
    emit(vec![1, 2, 3], &mut seen, &mut out, &mut n);
    emit(vec![1, 3, 2, 4, 3], &mut seen, &mut out, &mut n);
    emit(vec![5, 3, 4, 2, 1], &mut seen, &mut out, &mut n);
    emit(vec![1, 6, 5, 4, 3, 2], &mut seen, &mut out, &mut n);
    emit(vec![10, 20, 15, 2, 23, 90, 67], &mut seen, &mut out, &mut n);
    emit(vec![-2147483648, 2147483647], &mut seen, &mut out, &mut n);

    // ── Random inputs via verified generator ─────────────────────────
    let mutation_kinds: [u8; 6] = [0, 1, 2, 3, 4, 0];
    while n < count {
        // Pick a size class
        let len: usize = match n % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 50),        // medium
            3 => rng.gen_range_usize(51, 200),       // large
            _ => rng.gen_range_usize(200, 1000),     // max
        };
        let num_deltas = if len == 0 { 0 } else { len - 1 };

        let base = rng.gen_range_i64(-1_000_000, 1_000_000) as i32;
        let budget = 1_999_000i64 - base as i64;
        if budget <= 0 || num_deltas == 0 {
            let deltas: Vec<i32> = Vec::new();
            let mk = mutation_kinds[n % mutation_kinds.len()];
            let nums = generate_test_case(&deltas, base, mk);
            emit(nums, &mut seen, &mut out, &mut n);
            continue;
        }
        let max_d = ((budget / num_deltas as i64).min(1000).max(1)) as i32;
        let deltas = random_deltas(&mut rng, num_deltas, max_d, budget);
        if deltas.is_empty() && len > 1 { continue; }

        let mk = mutation_kinds[n % mutation_kinds.len()];
        let nums = generate_test_case(&deltas, base, mk);
        emit(nums, &mut seen, &mut out, &mut n);
    }
}
