use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
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
    mutation_kind: u8,
) -> (x: Vec<i64>)
    requires
        deltas.len() >= 1,
        deltas.len() + 1 <= 100_000,
        -1_000_000_000 <= base <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
    ensures
        2 <= x.len() <= 100_000,
        forall |i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
        forall |i: int| 0 <= i < x.len() ==> -1_000_000_000 <= #[trigger] x[i] <= 1_000_000_000,
{
    let mut nums: Vec<i64> = Vec::new();
    nums.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            nums.len() == i + 1,
            deltas.len() >= 1,
            deltas.len() + 1 <= 100_000,
            -1_000_000_000 <= base <= 1_000_000_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i64,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] nums[k] == (base as int + sum_deltas(deltas@, k)) as i64,
            forall|k: int| 0 <= k <= i as int ==>
                nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> -1_000_000_000 <= #[trigger] nums[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] < nums[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = nums.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = nums[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(-1_000_000_000 <= next <= 1_000_000_000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) <= 1_000_000_000);
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
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
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies nums[k] < nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    nums
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

fn build_input(x: &[i64]) -> String {
    let mut s = format!("{}\n", x.len());
    let parts: Vec<String> = x.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: &[(i64, i64)]) -> String {
    let mut s = String::new();
    for (a, b) in ans {
        s.push_str(&format!("{} {}\n", a, b));
    }
    s
}

fn make_sorted(rng: &mut Rng, n: usize, max_d: i64) -> Vec<i64> {
    let mut max_d = max_d.max(1);
    let cap = 2_000_000_000i64 / (n as i64).max(1);
    if max_d > cap { max_d = cap.max(1); }
    let mut deltas = Vec::with_capacity(n.saturating_sub(1));
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(1, max_d));
    }
    let total: i64 = deltas.iter().sum();
    let lo: i64 = -1_000_000_000;
    let hi: i64 = 1_000_000_000 - total;
    let hi = hi.max(lo);
    let base = if lo == hi { lo } else { rng.gen_range_i64(lo, hi) };
    let mut x = Vec::with_capacity(n);
    x.push(base);
    for d in &deltas { x.push(*x.last().unwrap() + d); }
    x
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(567);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |x: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| -> bool {
        if *count >= target { return false; }
        if x.len() < 2 || x.len() > 100_000 { return false; }
        for w in x.windows(2) { if w[0] >= w[1] { return false; } }
        for &v in &x { if v < -1_000_000_000 || v > 1_000_000_000 { return false; } }
        let key = format!("{:?}", x);
        if !seen.insert(key) { return false; }
        let inp = build_input(&x);
        let ans = Solution::compute_min_max_distances(x.clone());
        let outs = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
        true
    };

    emit(vec![-5, -2, 2, 7], &mut seen, &mut out, &mut count);
    emit(vec![-1, 1], &mut seen, &mut out, &mut count);
    emit(vec![0, 1], &mut seen, &mut out, &mut count);
    emit(vec![-1_000_000_000, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![-1_000_000_000, -999_999_999], &mut seen, &mut out, &mut count);
    emit(vec![999_999_999, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![-1, 0, 1], &mut seen, &mut out, &mut count);
    emit(vec![1, 2, 3], &mut seen, &mut out, &mut count);
    emit((0i64..10).collect::<Vec<_>>(), &mut seen, &mut out, &mut count);
    emit(vec![-10, -5, 0, 5, 10], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(2, 200);
        let max_d = match rng.gen_range_usize(0, 4) {
            0 => 2,
            1 => 10,
            2 => 1000,
            3 => 1_000_000,
            _ => 1_000_000_000,
        };
        let x = make_sorted(&mut rng, n, max_d);
        emit(x, &mut seen, &mut out, &mut count);
    }
}

