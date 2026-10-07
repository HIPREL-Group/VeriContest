use vstd::prelude::*;

verus! {

pub open spec fn value_in(s: Seq<i32>, x: i32) -> bool {
    exists |i: int| 0 <= i < s.len() && s[i] == x
}

/// Build a (pushed, popped) pair from a distinct-values array.
/// mutation_kind 0: popped = same order (identity)
/// mutation_kind 1: popped = reverse order
/// else: fallback to identity
pub fn generate_test_case(
    values: &Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1000,
        forall |i: int, j: int| 0 <= i < j < values.len() ==> values[i] != values[j],
    ensures
        1 <= result.0.len() <= 1000,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
        forall |i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
        forall |x: i32| #[trigger] value_in(result.0@, x) <==> value_in(result.1@, x),
{
    let n = values.len();
    let mut pushed: Vec<i32> = Vec::new();
    let mut popped: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 1000,
            0 <= i <= n,
            pushed.len() == i,
            popped.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] pushed[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] pushed[k] <= 1000,
            forall |k: int| 0 <= k < i as int && mutation_kind == 1u8
                ==> #[trigger] popped[k] == values[n as int - 1 - k],
            forall |k: int| 0 <= k < i as int && mutation_kind != 1u8
                ==> #[trigger] popped[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] popped[k] <= 1000,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1000,
            forall |k: int, l: int| 0 <= k < l < values.len() ==> values[k] != values[l],
        decreases n - i,
    {
        pushed.push(values[i]);
        if mutation_kind == 1u8 {
            popped.push(values[n - 1 - i]);
        } else {
            popped.push(values[i]);
        }
        i = i + 1;
    }

    proof {
        // Prove pushed distinctness
        assert forall |i1: int, j1: int|
            0 <= i1 < j1 < pushed@.len()
            implies pushed@[i1] != pushed@[j1]
        by {
            assert(pushed@[i1] == values@[i1]);
            assert(pushed@[j1] == values@[j1]);
        };

        if mutation_kind == 1u8 {
            // Reverse case — popped[k] == values[n-1-k]

            // Prove popped distinctness
            assert forall |i1: int, j1: int|
                0 <= i1 < j1 < popped@.len()
                implies popped@[i1] != popped@[j1]
            by {
                let a = n as int - 1 - i1;
                let b = n as int - 1 - j1;
                assert(0 <= b < a < values@.len());
                assert(popped@[i1] == values@[a]);
                assert(popped@[j1] == values@[b]);
            };

            // value_in: forward direction
            assert forall |x: i32|
                #[trigger] value_in(pushed@, x)
                implies value_in(popped@, x)
            by {
                if value_in(pushed@, x) {
                    let idx = choose |idx: int|
                        0 <= idx < pushed@.len() && pushed@[idx] == x;
                    let rev = n as int - 1 - idx;
                    assert(0 <= rev < popped@.len());
                    assert(popped@[rev] == values@[idx]);
                    assert(pushed@[idx] == values@[idx]);
                    assert(popped@[rev] == x);
                }
            };

            // value_in: reverse direction
            assert forall |x: i32|
                value_in(popped@, x)
                implies #[trigger] value_in(pushed@, x)
            by {
                if value_in(popped@, x) {
                    let idx = choose |idx: int|
                        0 <= idx < popped@.len() && popped@[idx] == x;
                    let orig = n as int - 1 - idx;
                    assert(0 <= orig < pushed@.len());
                    assert(popped@[idx] == values@[n as int - 1 - idx]);
                    assert(pushed@[orig] == values@[orig]);
                    assert(pushed@[orig] == x);
                }
            };
        } else {
            // Identity case — popped[k] == values[k] == pushed[k]

            assert forall |i1: int, j1: int|
                0 <= i1 < j1 < popped@.len()
                implies popped@[i1] != popped@[j1]
            by {
                assert(popped@[i1] == values@[i1]);
                assert(popped@[j1] == values@[j1]);
            };

            assert forall |x: i32|
                #[trigger] value_in(pushed@, x) <==> value_in(popped@, x)
            by {
                if value_in(pushed@, x) {
                    let idx = choose |idx: int|
                        0 <= idx < pushed@.len() && pushed@[idx] == x;
                    assert(popped@[idx] == pushed@[idx]);
                    assert(popped@[idx] == x);
                }
                if value_in(popped@, x) {
                    let idx = choose |idx: int|
                        0 <= idx < popped@.len() && popped@[idx] == x;
                    assert(pushed@[idx] == popped@[idx]);
                    assert(pushed@[idx] == x);
                }
            };
        }
    }

    (pushed, popped)
}

} // verus!

// ---------------------------------------------------------------------------
// Unverified runtime below
// ---------------------------------------------------------------------------

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
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

/// Emit a test case directly (for hand-crafted inputs like LeetCode examples).
fn emit_direct(
    out: &mut std::io::BufWriter<std::fs::File>,
    seen: &mut std::collections::HashSet<String>,
    count: &mut usize,
    pushed: Vec<i32>,
    popped: Vec<i32>,
) {
    use std::io::Write;
    let key = format!("{:?}|{:?}", pushed, popped);
    if seen.insert(key) {
        let result = Solution::validate_stack_sequences(pushed.clone(), popped.clone());
        writeln!(out, "{}", json!({
            "input": {"pushed": pushed, "popped": popped},
            "output": result
        })).unwrap();
        *count += 1;
    }
}

/// Emit a test case through the verified generator.
fn emit_gen(
    out: &mut std::io::BufWriter<std::fs::File>,
    seen: &mut std::collections::HashSet<String>,
    count: &mut usize,
    values: &Vec<i32>,
    mutation_kind: u8,
) {
    use std::io::Write;
    let (pushed, popped) = generate_test_case(values, mutation_kind);
    let key = format!("{:?}|{:?}", pushed, popped);
    if seen.insert(key) {
        let result = Solution::validate_stack_sequences(pushed.clone(), popped.clone());
        writeln!(out, "{}", json!({
            "input": {"pushed": pushed, "popped": popped},
            "output": result
        })).unwrap();
        *count += 1;
    }
}

/// Generate a random array of `n` distinct values in [0, 1000].
fn random_distinct_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Fisher-Yates shuffle on [0..1001], take first n
    let mut pool: Vec<i32> = (0..=1000i32).collect();
    for i in 0..pool.len() {
        let j = rng.gen_range_usize(i, pool.len() - 1);
        pool.swap(i, j);
    }
    pool.truncate(n);
    pool
}

/// Shuffle a vector in-place to produce a random permutation.
fn shuffle(rng: &mut Rng, v: &mut Vec<i32>) {
    let n = v.len();
    for i in 0..n {
        let j = rng.gen_range_usize(i, n - 1);
        v.swap(i, j);
    }
}

fn main() {
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

    // === LeetCode examples (hand-crafted) ===
    emit_direct(&mut out, &mut seen, &mut count,
        vec![1,2,3,4,5], vec![4,5,3,2,1]);  // true
    emit_direct(&mut out, &mut seen, &mut count,
        vec![1,2,3,4,5], vec![4,3,5,1,2]);  // false

    // === Edge: single element ===
    emit_gen(&mut out, &mut seen, &mut count, &vec![0], 0);
    emit_gen(&mut out, &mut seen, &mut count, &vec![1000], 0);
    emit_gen(&mut out, &mut seen, &mut count, &vec![500], 1);

    // === Edge: two elements ===
    emit_gen(&mut out, &mut seen, &mut count, &vec![0, 1], 0);  // identity
    emit_gen(&mut out, &mut seen, &mut count, &vec![0, 1], 1);  // reverse
    emit_gen(&mut out, &mut seen, &mut count, &vec![999, 1000], 0);
    emit_gen(&mut out, &mut seen, &mut count, &vec![999, 1000], 1);

    // === Boundary values ===
    emit_gen(&mut out, &mut seen, &mut count, &vec![0, 1, 2], 0);
    emit_gen(&mut out, &mut seen, &mut count, &vec![0, 1, 2], 1);
    emit_gen(&mut out, &mut seen, &mut count, &vec![998, 999, 1000], 0);
    emit_gen(&mut out, &mut seen, &mut count, &vec![998, 999, 1000], 1);

    // === Consecutive 1..n for small n ===
    for n in [3, 5, 10, 20].iter() {
        let vals: Vec<i32> = (0..*n as i32).collect();
        emit_gen(&mut out, &mut seen, &mut count, &vals, 0);
        emit_gen(&mut out, &mut seen, &mut count, &vals, 1);
    }

    // === Random cases across size classes ===
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),      // tiny
        (4, 10),     // small
        (11, 50),    // medium-small
        (51, 200),   // medium
        (201, 500),  // large
        (501, 1000), // max
    ];

    while count < goal {
        let class_idx = rng.gen_range_usize(0, size_classes.len() - 1);
        let (lo, hi) = size_classes[class_idx];
        let n = rng.gen_range_usize(lo, hi);
        let values = random_distinct_values(&mut rng, n);
        let mk = rng.gen_range_usize(0, 1) as u8;
        emit_gen(&mut out, &mut seen, &mut count, &values, mk);

        // Also emit a hand-crafted random permutation for diversity
        if count < goal {
            let vals2 = random_distinct_values(&mut rng, n);
            let pushed = vals2.clone();
            let mut popped = vals2;
            shuffle(&mut rng, &mut popped);
            emit_direct(&mut out, &mut seen, &mut count, pushed, popped);
        }
    }

    eprintln!("Generated {} test cases", count);
}
