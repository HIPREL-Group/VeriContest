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
    mutation_kind: u8,
) -> (a: Vec<i32>)
    requires
        deltas.len() >= 2,
        deltas.len() <= 99,
        1 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1000,
    ensures
        a.len() >= 3,
        a.len() <= 100,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a@[i] <= 1000,
        forall|i: int| 0 <= i < a.len() - 1 ==> #[trigger] a@[i] < a@[i + 1],
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    proof {
        assert(nums[0] as int == base as int + sum_deltas(deltas@, 0));
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(base as int + sum_deltas(deltas@, 0) == base as int);
        assert(1 <= nums[0] <= 1000i32) by {
            assert(nums[0] == base);
            assert(1 <= base);
            assert(base as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
            assert(base as int + sum_deltas(deltas@, deltas.len() as int) <= 1000);
        };
    }

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            nums.len() == idx + 1,
            deltas.len() >= 2,
            deltas.len() <= 99,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1000,
            forall|k: int| 0 <= k <= idx as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= idx as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000i32,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] < nums[l],
        decreases deltas.len() - idx,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = nums[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
            assert(1 <= next <= 1000i32) by {
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int) <= 1000);
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int >= 1);
            };

            assert forall|k: int| 0 <= k < nums.len() implies nums[k] < next by {
                assert(nums[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        nums.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies nums[k] < nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    assert(nums.len() == deltas.len() + 1);
    assert(nums.len() >= 3);
    assert(nums.len() <= 100);

    // Apply mutations that preserve all invariants
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() >= 4 {
        // shrink: remove second element (keep first and last)
        let mut result: Vec<i32> = Vec::new();
        result.push(nums[0]);
        let mut j: usize = 2;
        while j < nums.len()
            invariant
                2 <= j <= nums.len(),
                result.len() == j as int - 1,
                nums.len() >= 4,
                result.len() >= 1,
                forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000i32,
                forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] < nums[l],
                result[0] == nums[0],
                forall|k: int| 1 <= k < result.len() ==> #[trigger] result[k] == nums[k + 1],
                forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 1000i32,
                forall|k: int, l: int| 0 <= k < l < result.len() ==> result[k] < result[l],
            decreases nums.len() - j,
        {
            let ghost old_result_len = result.len();
            result.push(nums[j]);

            proof {
                assert forall|k: int, l: int| 0 <= k < l < result.len() implies result[k] < result[l] by {
                    if l < old_result_len as int {
                    } else {
                        assert(l == old_result_len as int);
                        assert(result[l] == nums[j as int]);
                        if k == 0 {
                            assert(result[0] == nums[0]);
                            assert(nums[0] < nums[j as int]);
                        } else {
                            assert(result[k] == nums[k + 1]);
                            assert(k + 1 < j as int);
                            assert(nums[k + 1] < nums[j as int]);
                        }
                    }
                };
            }

            j = j + 1;
        }
        assert(result.len() == nums.len() - 1);
        assert(result.len() >= 3);
        result
    } else {
        // fallback: identity
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn random_increasing(rng: &mut Rng, n: usize) -> Vec<i32> {
    // n distinct increasing values from 1..1000
    let mut chosen = Vec::with_capacity(n);
    let mut prev = 0i64;
    for i in 0..n {
        // Need to leave room for remaining (n-i-1) values
        let max_val = 1000 - (n as i64 - i as i64 - 1);
        if prev + 1 > max_val { break; }
        let v = rng.gen_range_i64(prev + 1, max_val);
        chosen.push(v as i32);
        prev = v;
    }
    if chosen.len() < n {
        // fallback: use evenly spaced
        chosen.clear();
        for i in 0..n {
            chosen.push((i + 1) as i32);
        }
    }
    chosen
}

fn main() {
    let target_count: usize = 100;
    let mut rng = Rng::new(496);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        if a.len() < 3 || a.len() > 100 { return; }
        for i in 1..a.len() {
            if a[i] <= a[i-1] { return; }
        }
        if a[0] < 1 || a[a.len()-1] > 1000 { return; }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let result = Solution::min_max_difficulty(a.clone());
        let inp = build_input(&a);
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![1, 4, 6], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3, 7, 8], &mut seen, &mut out, &mut count);

    // Edge
    emit(vec![1, 2, 3], &mut seen, &mut out, &mut count);
    emit(vec![1, 500, 1000], &mut seen, &mut out, &mut count);
    emit((1..=100).collect(), &mut seen, &mut out, &mut count);
    emit((901..=1000).collect(), &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 1000], &mut seen, &mut out, &mut count);
    emit(vec![1, 999, 1000], &mut seen, &mut out, &mut count);

    while count < target_count {
        let n = rng.gen_range_usize(3, 100);
        let a = random_increasing(&mut rng, n);
        emit(a, &mut seen, &mut out, &mut count);
    }
}

