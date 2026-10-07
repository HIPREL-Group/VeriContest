use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: usize,
    max_val: i32,
    step: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, usize))
    requires
        1 <= n <= 50,
        1 <= k <= n,
        0 <= max_val <= 100,
        0 <= step <= 100,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100,
        forall|i: int| 0 <= i < result.0.len() - 1 ==> #[trigger] result.0[i] >= result.0[i + 1],
{
    if mutation_kind == 1 {
        // All same value
        let mut scores: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 50,
                0 <= max_val <= 100,
                scores.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] scores@[j] == max_val,
            decreases n - i,
        {
            scores.push(max_val);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < scores@.len() implies 0 <= #[trigger] scores@[j] <= 100 by {
                assert(scores@[j] == max_val);
            };
            assert forall|j: int| 0 <= j < scores@.len() - 1 implies #[trigger] scores@[j] >= scores@[j + 1] by {
                assert(scores@[j] == max_val);
                assert(scores@[j + 1] == max_val);
            };
        }
        return (scores, k);
    }

    if mutation_kind == 2 {
        // All zeros
        let mut scores: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 50,
                scores.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] scores@[j] == 0i32,
            decreases n - i,
        {
            scores.push(0i32);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < scores@.len() implies 0 <= #[trigger] scores@[j] <= 100 by {
                assert(scores@[j] == 0i32);
            };
            assert forall|j: int| 0 <= j < scores@.len() - 1 implies #[trigger] scores@[j] >= scores@[j + 1] by {
                assert(scores@[j] == 0i32);
                assert(scores@[j + 1] == 0i32);
            };
        }
        return (scores, k);
    }

    if mutation_kind == 3 {
        // max_val for first, 0 for rest (sharp drop)
        let mut scores: Vec<i32> = Vec::new();
        scores.push(max_val);
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                1 <= n <= 50,
                0 <= max_val <= 100,
                scores.len() == i,
                scores@[0] == max_val,
                forall|j: int| 1 <= j < i as int ==> #[trigger] scores@[j] == 0i32,
            decreases n - i,
        {
            scores.push(0i32);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < scores@.len() implies 0 <= #[trigger] scores@[j] <= 100 by {
                if j == 0 {
                    assert(scores@[j] == max_val);
                } else {
                    assert(scores@[j] == 0i32);
                }
            };
            assert forall|j: int| 0 <= j < scores@.len() - 1 implies #[trigger] scores@[j] >= scores@[j + 1] by {
                if j == 0 {
                    assert(scores@[j] == max_val);
                    if scores@.len() > 1 {
                        assert(scores@[j + 1] == 0i32);
                    }
                } else {
                    assert(scores@[j] == 0i32);
                    assert(scores@[j + 1] == 0i32);
                }
            };
        }
        return (scores, k);
    }

    // Default (mutation_kind == 0 or fallback): linear decay
    // scores[0] = max_val, scores[i] = max(0, scores[i-1] - step)
    let mut scores: Vec<i32> = Vec::new();
    scores.push(max_val);
    let mut i: usize = 1;
    while i < n
        invariant
            1 <= i <= n,
            1 <= n <= 50,
            0 <= max_val <= 100,
            0 <= step <= 100,
            scores.len() == i,
            forall|j: int| 0 <= j < i as int ==> 0 <= #[trigger] scores@[j] <= 100,
            forall|j: int| 0 <= j < i as int - 1 ==> #[trigger] scores@[j] >= scores@[j + 1],
        decreases n - i,
    {
        let prev = scores[i - 1];
        let val: i32 = if prev >= step { prev - step } else { 0i32 };

        assert(0 <= val <= 100) by {
            if prev >= step {
                assert(val == prev - step);
                assert(val >= 0);
                assert(val <= prev);
                assert(prev <= 100);
            } else {
                assert(val == 0i32);
            }
        }
        assert(val <= prev) by {
            if prev >= step {
                assert(val == prev - step);
            } else {
                assert(val == 0i32);
            }
        }

        scores.push(val);
        i += 1;
    }

    (scores, k)
}

}

use std::io::Write;
use std::collections::HashSet;

struct Rng(u64);
impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let r = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn fmt_json_str(s: &str) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            '\n' => out.push_str("\\n"),
            '\r' => out.push_str("\\r"),
            '\t' => out.push_str("\\t"),
            c if (c as u32) < 0x20 => out.push_str(&format!("\\u{:04x}", c as u32)),
            c => out.push(c),
        }
    }
    out.push('"');
    out
}

struct Solution;
include!("../code.rs");

fn build_input(n: usize, k: usize, scores: &[i32]) -> String {
    let mut s = format!("{} {}\n", n, k);
    let parts: Vec<String> = scores.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn make_non_increasing(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(0, 100) as i32).collect();
    v.sort();
    v.reverse();
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let mut emit = |scores: Vec<i32>, k: usize, count: &mut usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>| {
        if *count >= target { return; }
        let n = scores.len();
        if k < 1 || k > n { return; }
        let inp = build_input(n, k, &scores);
        if !seen.insert(inp.clone()) { return; }
        let ans = Solution::count_advancing(scores, k);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // examples
    emit(vec![10, 9, 8, 7, 7, 7, 5, 5], 5, &mut count, &mut seen, &mut out);
    emit(vec![0, 0, 0, 0], 2, &mut count, &mut seen, &mut out);
    // Edge cases
    emit(vec![1], 1, &mut count, &mut seen, &mut out);
    emit(vec![0], 1, &mut count, &mut seen, &mut out);
    emit(vec![100], 1, &mut count, &mut seen, &mut out);
    emit(vec![100, 100], 1, &mut count, &mut seen, &mut out);
    emit(vec![100, 100], 2, &mut count, &mut seen, &mut out);
    emit(vec![100, 0], 1, &mut count, &mut seen, &mut out);
    emit(vec![100, 0], 2, &mut count, &mut seen, &mut out);
    emit(vec![100, 50, 50, 50, 0, 0], 4, &mut count, &mut seen, &mut out);
    emit(vec![50; 50], 25, &mut count, &mut seen, &mut out);

    while count < target {
        let n = rng.gen_range_usize(1, 50);
        let k = rng.gen_range_usize(1, n);
        let scores = make_non_increasing(&mut rng, n);
        emit(scores, k, &mut count, &mut seen, &mut out);
    }
}

