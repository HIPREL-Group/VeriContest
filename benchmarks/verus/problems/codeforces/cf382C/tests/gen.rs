use vstd::prelude::*;

verus! {

pub open spec fn sorted(nums: Seq<i64>) -> bool {
    forall|i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] <= nums[i + 1]
}

pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

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

pub fn generate_test_case(
    deltas: &Vec<i64>,
    base: i64,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        deltas.len() <= 99_999,
        1 <= base <= 100_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 100_000_000,
    ensures
        1 <= result.len() <= 100_000,
        sorted(result@),
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100_000_000,
{
    if mutation_kind == 1 {
        // Single element [base]
        let mut v: Vec<i64> = Vec::new();
        v.push(base);
        v
    } else if mutation_kind == 2 {
        // Constant sequence: all elements = base, length = deltas.len() + 1
        let n = deltas.len() + 1;
        let mut v: Vec<i64> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                0 <= j <= n,
                v.len() == j,
                n == deltas.len() + 1,
                n <= 100_000,
                1 <= base <= 100_000_000,
                forall|k: int| 0 <= k < j ==> #[trigger] v[k] == base,
            decreases n - j,
        {
            v.push(base);
            j += 1;
        }
        proof {
            assert(v.len() >= 1);
            assert forall|k: int| 0 <= k < v.len()
                implies 1 <= #[trigger] v[k] <= 100_000_000 by {};
            assert(sorted(v@)) by {
                assert forall|k: int| 0 <= k < v.len() - 1
                    implies #[trigger] v[k] <= v[k + 1] by {};
            };
        }
        v
    } else if mutation_kind == 3 && deltas.len() >= 1 {
        // Two-element array [base, base + deltas[0]]
        proof {
            assert(sum_deltas(deltas@, 0) == 0int);
            assert(sum_deltas(deltas@, 1) == sum_deltas(deltas@, 0) + deltas@[0] as int);
            assert(sum_deltas(deltas@, 1) == deltas@[0] as int);
            lemma_sum_deltas_mono(deltas@, 1, deltas.len() as int);
            assert(deltas[0] as int <= sum_deltas(deltas@, deltas.len() as int));
            assert(base as int + deltas[0] as int <= 100_000_000);
        }
        let second = base + deltas[0];
        proof {
            assert(second >= base);
            assert(second >= 1);
        }
        let mut v: Vec<i64> = Vec::new();
        v.push(base);
        v.push(second);
        proof {
            assert(sorted(v@)) by {
                assert forall|k: int| 0 <= k < v.len() - 1
                    implies #[trigger] v[k] <= v[k + 1] by {
                    assert(v[0] == base);
                    assert(v[1] == second);
                    assert(base <= second);
                };
            };
        }
        v
    } else {
        // Default: build sorted array from base + cumulative deltas
        let mut nums: Vec<i64> = Vec::new();
        nums.push(base);

        let mut idx: usize = 0;
        while idx < deltas.len()
            invariant
                0 <= idx <= deltas.len(),
                nums.len() == idx as int + 1,
                deltas.len() <= 99_999,
                1 <= base <= 100_000_000,
                forall|k: int| 0 <= k < deltas.len() ==> 0 <= #[trigger] deltas[k] as int,
                base as int + sum_deltas(deltas@, deltas.len() as int) <= 100_000_000,
                forall|k: int| 0 <= k <= idx as int ==>
                    (#[trigger] nums[k]) as int == base as int + sum_deltas(deltas@, k),
                forall|k: int| 0 <= k < nums.len() ==>
                    1 <= (#[trigger] nums[k]) <= 100_000_000,
                forall|k: int| 0 <= k < nums.len() - 1 ==>
                    (#[trigger] nums[k]) <= nums[k + 1],
            decreases deltas.len() - idx,
        {
            proof {
                lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
            }

            let prev = nums[idx];
            let next = prev + deltas[idx];

            proof {
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                assert(next <= 100_000_000i64) by {
                    assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                        <= base as int + sum_deltas(deltas@, deltas.len() as int));
                };
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(next >= base);
                assert(next >= 1);
                assert(next >= prev);
            }

            let ghost old_len = nums.len();
            nums.push(next);
            idx = idx + 1;

            proof {
                assert forall|k: int| 0 <= k < nums.len() - 1
                    implies (#[trigger] nums[k]) <= nums[k + 1] by {
                    if k < old_len as int - 1 {
                    } else {
                        assert(nums[k + 1] == next);
                    }
                };
            }
        }

        proof {
            assert(sorted(nums@)) by {
                assert forall|k: int| 0 <= k < nums.len() - 1
                    implies #[trigger] nums[k] <= nums[k + 1] by {};
            };
        }
        nums
    }
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

fn build_input(nums: &[i64]) -> String {
    let mut s = format!("{}\n", nums.len());
    let parts: Vec<String> = nums.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(opt: Option<Vec<i64>>) -> String {
    match opt {
        None => "-1\n".to_string(),
        Some(ans) => {
            let mut s = format!("{}\n", ans.len());
            if !ans.is_empty() {
                let parts: Vec<String> = ans.iter().map(|x| x.to_string()).collect();
                s.push_str(&parts.join(" "));
                s.push('\n');
            }
            s
        }
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    // input nums in range [1, 1e8]
    let mut emit = |nums_in: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if nums_in.is_empty() || nums_in.len() > 100_000 { return; }
        for &n in &nums_in { if !(1 <= n && n <= 100_000_000) { return; } }
        let key = format!("{:?}", nums_in);
        if !seen.insert(key) { return; }
        let inp = build_input(&nums_in);
        let mut sorted = nums_in.clone();
        sorted.sort_unstable();
        let ans = Solution::arithmetic_progression_insertions(sorted);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // examples
    emit(vec![4, 1, 7], &mut seen, &mut out, &mut count);
    emit(vec![10], &mut seen, &mut out, &mut count);
    emit(vec![1, 3, 5, 9], &mut seen, &mut out, &mut count);
    emit(vec![4, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![2, 4], &mut seen, &mut out, &mut count);

    // Edge cases
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![1, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 2], &mut seen, &mut out, &mut count);
    emit(vec![1, 3], &mut seen, &mut out, &mut count);
    emit(vec![1, 1, 1, 1, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![100_000_000], &mut seen, &mut out, &mut count);
    emit(vec![1, 100_000_000], &mut seen, &mut out, &mut count);

    // Random APs and near-APs
    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 6 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(3, 10),
            3 => rng.gen_range_usize(10, 100),
            4 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 10_000),
        };
        // Build a random AP
        let max_diff = if n > 1 { (99_000_000 / (n as i64)).max(1) } else { 1 };
        let diff = rng.gen_range_i64(0, max_diff.min(500));
        let max_start = (100_000_000 - (n as i64) * diff).max(1);
        let start = rng.gen_range_i64(1, max_start);
        let mut nums: Vec<i64> = (0..n).map(|i| start + (i as i64) * diff).collect();
        // Sometimes perturb
        if tries % 7 == 0 && nums.len() > 0 {
            let idx = (rng.next_u64() as usize) % nums.len();
            nums[idx] = nums[idx] + 1;
            if nums[idx] > 100_000_000 { nums[idx] -= 2; }
            if nums[idx] < 1 { nums[idx] = 1; }
        }
        emit(nums, &mut seen, &mut out, &mut count);
    }
}

