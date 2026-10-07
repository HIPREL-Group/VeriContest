use vstd::prelude::*;

verus! {

// --- Spec fn helpers (from spec.rs) ---

pub open spec fn target_as_ints(target: Seq<i32>) -> Seq<int> {
    Seq::new(target.len(), |i: int| target[i] as int)
}

pub open spec fn positive_diff_sum_int(s: Seq<int>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        0
    } else {
        positive_diff_sum_int(s, end - 1)
            + if s[end - 1] > s[end - 2] { s[end - 1] - s[end - 2] } else { 0int }
    }
}

pub open spec fn algo_result_int(s: Seq<int>) -> int {
    s[0] + positive_diff_sum_int(s, s.len() as int)
}

// --- Proof lemmas ---

/// For a constant sequence (all elements == v), positive_diff_sum is 0.
proof fn lemma_constant_diff_sum(s: Seq<int>, v: int, end: int)
    requires
        end >= 0,
        end <= s.len(),
        forall|i: int| 0 <= i < s.len() ==> s[i] == v,
    ensures
        positive_diff_sum_int(s, end) == 0,
    decreases end,
{
    if end <= 1 {
    } else {
        lemma_constant_diff_sum(s, v, end - 1);
    }
}

/// For [first, c, c, ..., c] where first >= c, positive_diff_sum is 0.
proof fn lemma_spike_start_diff_sum(s: Seq<int>, first: int, c: int, end: int)
    requires
        end >= 0,
        end <= s.len(),
        s.len() >= 1,
        s[0] == first,
        first >= c,
        forall|i: int| 1 <= i < s.len() ==> s[i] == c,
    ensures
        positive_diff_sum_int(s, end) == 0,
    decreases end,
{
    if end <= 1 {
    } else {
        lemma_spike_start_diff_sum(s, first, c, end - 1);
        // For end == 2: s[1] == c <= first == s[0], diff <= 0
        // For end > 2: s[end-1] == c == s[end-2], diff == 0
    }
}

/// For [c, c, ..., c, last] (n elements, last at index n-1) where last >= c,
/// positive_diff_sum(s, n) == last - c.
proof fn lemma_spike_end_diff_sum(s: Seq<int>, c: int, last: int, n: int, end: int)
    requires
        n >= 2,
        end >= 0,
        end <= n,
        s.len() == n,
        last >= c,
        forall|i: int| 0 <= i < n - 1 ==> s[i] == c,
        s[(n - 1) as int] == last,
    ensures
        positive_diff_sum_int(s, end) == if end == n { last - c } else { 0int },
    decreases end,
{
    if end <= 1 {
    } else if end < n {
        lemma_spike_end_diff_sum(s, c, last, n, end - 1);
        // s[end-1] == c == s[end-2], diff == 0
    } else {
        // end == n
        lemma_spike_end_diff_sum(s, c, last, n, end - 1);
        // s[n-1] == last >= c == s[n-2], diff == last - c
    }
}

// --- Generator ---

pub fn generate_test_case(
    n: usize,
    val: i32,
    mutation_kind: u8,
) -> (target: Vec<i32>)
    requires
        1 <= n <= 100_000,
        1 <= val <= 100_000,
    ensures
        1 <= target.len() <= 100_000,
        forall|i: int| 0 <= i < target.len() ==> 1 <= #[trigger] target[i] <= 100_000,
        algo_result_int(target_as_ints(target@)) <= i32::MAX as int,
{
    if mutation_kind == 1 && n >= 2 {
        // Strategy: spike-start [val, 1, 1, ..., 1]
        // algo_result = val + 0 = val <= 100_000
        let mut target: Vec<i32> = Vec::new();
        target.push(val);
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                target.len() == i as int,
                1 <= n <= 100_000,
                1 <= val <= 100_000,
                target[0] == val,
                forall|j: int| 1 <= j < i ==> target[j] == 1i32,
            decreases n - i,
        {
            target.push(1i32);
            i += 1;
        }
        proof {
            let s = target_as_ints(target@);
            assert(s[0] == val as int);
            assert forall|j: int| 1 <= j < s.len() implies s[j] == 1int by {
                assert(target[j] == 1i32);
            }
            lemma_spike_start_diff_sum(s, val as int, 1int, n as int);
            // algo_result = val + 0 = val <= 100_000 <= i32::MAX
        }
        target
    } else if mutation_kind == 2 && n >= 2 {
        // Strategy: spike-end [1, 1, ..., 1, val]
        // algo_result = 1 + (val - 1) = val <= 100_000
        let mut target: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n - 1
            invariant
                0 <= i <= n - 1,
                target.len() == i as int,
                1 <= n <= 100_000,
                1 <= val <= 100_000,
                forall|j: int| 0 <= j < i ==> target[j] == 1i32,
            decreases (n - 1) - i,
        {
            target.push(1i32);
            i += 1;
        }
        target.push(val);
        proof {
            let s = target_as_ints(target@);
            assert(s.len() == n as int);
            assert forall|j: int| 0 <= j < n - 1 implies s[j] == 1int by {
                assert(target[j] == 1i32);
            }
            assert(s[(n - 1) as int] == val as int) by {
                assert(target[(n - 1) as int] == val);
            }
            lemma_spike_end_diff_sum(s, 1int, val as int, n as int, n as int);
            // algo_result = 1 + (val - 1) = val <= 100_000 <= i32::MAX
        }
        target
    } else if mutation_kind == 3 && n >= 3 {
        // Strategy: V-shape [val, 1, val] padded with 1s in the middle
        // [val, 1, 1, ..., 1, val]
        // positive diffs: 0 for middle (all 1), then val-1 at end
        // algo_result = val + 0 + (val - 1) = 2*val - 1 <= 199_999 <= i32::MAX
        let mut target: Vec<i32> = Vec::new();
        target.push(val);
        let mut i: usize = 1;
        while i < n - 1
            invariant
                1 <= i <= n - 1,
                target.len() == i as int,
                1 <= n <= 100_000,
                1 <= val <= 100_000,
                n >= 3,
                target[0] == val,
                forall|j: int| 1 <= j < i ==> target[j] == 1i32,
            decreases (n - 1) - i,
        {
            target.push(1i32);
            i += 1;
        }
        target.push(val);
        proof {
            let s = target_as_ints(target@);
            assert(s.len() == n as int);
            assert(s[0] == val as int) by { assert(target[0] == val); }
            assert forall|j: int| 1 <= j < n - 1 implies s[j] == 1int by {
                assert(target[j] == 1i32);
            }
            assert(s[(n - 1) as int] == val as int) by {
                assert(target[(n - 1) as int] == val);
            }
            // This is [val, 1, 1, ..., 1, val]
            // First: s[1] = 1 < val = s[0], no positive diff
            // Middle: s[j] = 1 = s[j-1], no positive diff for j in 2..n-2
            // Last: s[n-1] = val > 1 = s[n-2], positive diff = val - 1
            // Need a custom lemma for V-shape
            lemma_v_shape_diff_sum(s, val as int, n as int, n as int);
            // algo_result = val + (val - 1) = 2*val - 1 <= 199_999 <= i32::MAX
        }
        target
    } else {
        // Strategy 0 / fallback: constant array [val; n]
        // algo_result = val + 0 = val <= 100_000
        let mut target: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                target.len() == i as int,
                1 <= n <= 100_000,
                1 <= val <= 100_000,
                forall|j: int| 0 <= j < i ==> target[j] == val,
            decreases n - i,
        {
            target.push(val);
            i += 1;
        }
        proof {
            let s = target_as_ints(target@);
            assert forall|j: int| 0 <= j < s.len() implies s[j] == val as int by {
                assert(target[j] == val);
            }
            lemma_constant_diff_sum(s, val as int, n as int);
            // algo_result = val + 0 = val <= 100_000 <= i32::MAX
        }
        target
    }
}

/// V-shape [val, 1, 1, ..., 1, val]: positive_diff_sum = val - 1
proof fn lemma_v_shape_diff_sum(s: Seq<int>, val: int, n: int, end: int)
    requires
        n >= 3,
        end >= 0,
        end <= n,
        s.len() == n,
        val >= 1,
        s[0] == val,
        forall|i: int| 1 <= i < n - 1 ==> s[i] == 1,
        s[(n - 1) as int] == val,
    ensures
        positive_diff_sum_int(s, end) == if end == n { val - 1 } else { 0int },
    decreases end,
{
    if end <= 1 {
    } else if end == 2 {
        // s[1] == 1 <= val == s[0], diff <= 0
        lemma_v_shape_diff_sum(s, val, n, end - 1);
    } else if end < n {
        lemma_v_shape_diff_sum(s, val, n, end - 1);
        // s[end-1] == 1 (since 1 <= end-1 < n-1) == s[end-2] (also 1 or val at 0)
        // For end-1 >= 2: s[end-1] == 1 == s[end-2], diff == 0
        // For end-1 == 1: s[1] == 1 <= val == s[0], diff <= 0
    } else {
        // end == n
        lemma_v_shape_diff_sum(s, val, n, end - 1);
        // s[n-1] == val, s[n-2] == 1 (since n-2 >= 1 and n-2 < n-1), diff == val - 1
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

fn gen_wrapper(n: usize, val: i32, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(n, val, mutation_kind)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;

    let mut rng = Rng::new(seed);
    let mut written = 0usize;

    // Hardcoded example test cases from description.md
    let examples: Vec<Vec<i32>> = vec![
        vec![1, 2, 3, 2, 1],
        vec![3, 1, 1, 2],
        vec![3, 1, 5, 4, 2],
    ];
    for target in &examples {
        let result = Solution::min_number_operations(target.clone());
        writeln!(out, "{}", json!({
            "input": { "target": target },
            "output": result
        })).unwrap();
        written += 1;
    }

    // Generate random test cases
    let num_mutations: u8 = 4; // 0=constant, 1=spike-start, 2=spike-end, 3=v-shape

    while written < count {
        // Size classes for array length
        let n: usize = match written % 5 {
            0 => rng.gen_range_usize(1, 5),          // tiny
            1 => rng.gen_range_usize(1, 10),         // small
            2 => rng.gen_range_usize(11, 100),       // medium
            3 => rng.gen_range_usize(101, 1000),     // large
            _ => rng.gen_range_usize(1001, 100_000), // max
        };

        // Value with boundary mixing
        let val: i32 = if written % 5 == 0 {
            *[1i32, 100_000, 1, 2, 99_999].iter().nth(
                rng.gen_range_usize(0, 4)
            ).unwrap()
        } else {
            rng.gen_range_i64(1, 100_000) as i32
        };

        let mutation_kind: u8 = (rng.gen_range_usize(0, (num_mutations - 1) as usize)) as u8;

        let target = gen_wrapper(n, val, mutation_kind);
        let result = Solution::min_number_operations(target.clone());

        writeln!(out, "{}", json!({
            "input": { "target": target },
            "output": result
        })).unwrap();

        written += 1;
    }

    eprintln!("Wrote {} test cases to {}", written, out_path.display());
}
