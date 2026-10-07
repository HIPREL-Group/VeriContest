use vstd::prelude::*;

verus! {

pub open spec fn sum_gaps(gaps: Seq<i64>, k: int) -> int
    decreases k,
{
    if k <= 0 {
        0int
    } else if k > gaps.len() {
        0int
    } else {
        sum_gaps(gaps, k - 1) + gaps[k - 1] as int
    }
}

pub proof fn lemma_sum_gaps_bound(gaps: Seq<i64>, k: int)
    requires
        0 <= k <= gaps.len(),
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= (#[trigger] gaps[i]) as int <= 2_000_000_000,
    ensures
        0 <= sum_gaps(gaps, k),
        sum_gaps(gaps, k) <= k * 2_000_000_000,
    decreases k,
{
    if k <= 0 {
    } else {
        lemma_sum_gaps_bound(gaps, k - 1);
    }
}

pub fn generate_test_case(
    start: i64,
    gaps: &Vec<i64>,
) -> (x: Vec<i64>)
    requires
        1 <= gaps.len() <= 99_999,
        -1_000_000_000 <= start <= 1_000_000_000,
        forall|i: int| 0 <= i < gaps.len() ==> 1 <= (#[trigger] gaps[i]) as int <= 2_000_000_000,
        start as int + (gaps.len() as int) * 2_000_000_000 <= 1_000_000_000,
    ensures
        2 <= x.len() <= 100_000,
        x.len() == gaps.len() + 1,
        forall|i: int, j: int| 0 <= i < j < x.len() ==> #[trigger] x[i] < #[trigger] x[j],
        forall|i: int| 0 <= i < x.len() ==> -1_000_000_000 <= #[trigger] x[i] <= 1_000_000_000,
{
    let n = gaps.len() + 1;
    let mut x: Vec<i64> = Vec::new();
    x.push(start);

    let mut k: usize = 0;
    while k < gaps.len()
        invariant
            0 <= k <= gaps.len(),
            1 <= gaps.len() <= 99_999,
            -1_000_000_000 <= start <= 1_000_000_000,
            forall|i: int| 0 <= i < gaps.len() ==> 1 <= (#[trigger] gaps[i]) as int <= 2_000_000_000,
            start as int + (gaps.len() as int) * 2_000_000_000 <= 1_000_000_000,
            x.len() == k + 1,
            x[0] == start,
            forall|i: int| 0 <= i <= k as int ==> x[i] as int == start as int + sum_gaps(gaps@, i),
            forall|i: int, j: int| 0 <= i < j <= k as int ==> #[trigger] x[i] < #[trigger] x[j],
            forall|i: int| 0 <= i <= k as int ==> -1_000_000_000 <= #[trigger] x[i] <= 1_000_000_000,
        decreases gaps.len() - k,
    {
        proof {
            lemma_sum_gaps_bound(gaps@, k as int + 1);
            assert(sum_gaps(gaps@, k as int + 1) == sum_gaps(gaps@, k as int) + gaps[k as int] as int);
            assert((k as int + 1) * 2_000_000_000 <= (gaps.len() as int) * 2_000_000_000) by {
                assert(k as int + 1 <= gaps.len() as int);
            }
        }
        let prev = x[k];
        let new_val: i64 = prev + gaps[k];
        x.push(new_val);

        proof {
            assert(x[k as int + 1] as int == prev as int + gaps[k as int] as int);
            assert(prev as int == start as int + sum_gaps(gaps@, k as int));
            assert(x[k as int + 1] as int == start as int + sum_gaps(gaps@, k as int + 1));

            assert forall|i: int| 0 <= i <= (k as int + 1) implies x[i] as int == start as int + sum_gaps(gaps@, i) by {
                if i <= k as int {
                } else {
                }
            }

            assert forall|i: int, j: int| 0 <= i < j <= (k as int + 1) implies #[trigger] x[i] < #[trigger] x[j] by {
                if j <= k as int {
                } else {
                    assert(j == k as int + 1);
                    assert(x[i] as int == start as int + sum_gaps(gaps@, i));
                    assert(x[j] as int == start as int + sum_gaps(gaps@, j));
                    // Show sum_gaps(gaps@, i) < sum_gaps(gaps@, j)
                    lemma_sum_strictly_increasing(gaps@, i, j);
                }
            }

            assert forall|i: int| 0 <= i <= (k as int + 1) implies -1_000_000_000 <= #[trigger] x[i] <= 1_000_000_000 by {
                lemma_sum_gaps_bound(gaps@, i);
                assert(x[i] as int == start as int + sum_gaps(gaps@, i));
                assert(sum_gaps(gaps@, i) >= 0);
                assert(sum_gaps(gaps@, i) <= i * 2_000_000_000);
                assert(i * 2_000_000_000 <= (gaps.len() as int) * 2_000_000_000);
            }
        }

        k = k + 1;
    }

    proof {
        assert(x.len() == gaps.len() + 1);
        assert(x.len() >= 2);
    }

    x
}

pub proof fn lemma_sum_strictly_increasing(gaps: Seq<i64>, i: int, j: int)
    requires
        0 <= i < j <= gaps.len(),
        forall|k: int| 0 <= k < gaps.len() ==> 1 <= (#[trigger] gaps[k]) as int <= 2_000_000_000,
    ensures
        sum_gaps(gaps, i) < sum_gaps(gaps, j),
    decreases j - i,
{
    if j == i + 1 {
        assert(sum_gaps(gaps, j) == sum_gaps(gaps, i) + gaps[j - 1] as int);
        assert(gaps[j - 1] as int >= 1);
    } else {
        lemma_sum_strictly_increasing(gaps, i, j - 1);
        assert(sum_gaps(gaps, j) == sum_gaps(gaps, j - 1) + gaps[j - 1] as int);
        assert(gaps[j - 1] as int >= 1);
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

fn make_sorted_with_pattern(rng: &mut Rng, n: usize, mode: usize) -> Vec<i64> {
    // Returns a sorted vec of n distinct integers in [-1e9, 1e9].
    let lo: i64 = -1_000_000_000;
    let hi: i64 = 1_000_000_000;
    let span: i64 = hi - lo;
    let max_d_uniform: i64 = (span / (n as i64).max(1)).max(1);
    let mut deltas: Vec<i64> = Vec::with_capacity(n.saturating_sub(1));

    match mode {
        0 => {
            // all gaps = 1, packed
            for _ in 0..n.saturating_sub(1) { deltas.push(1); }
        }
        1 => {
            // max uniform spread
            for _ in 0..n.saturating_sub(1) { deltas.push(max_d_uniform); }
        }
        2 => {
            // mixed small/large
            for i in 0..n.saturating_sub(1) {
                deltas.push(if i % 2 == 0 { 1 } else { max_d_uniform });
            }
        }
        3 => {
            // increasing
            for i in 0..n.saturating_sub(1) {
                let g = (i as i64 + 1).min(max_d_uniform).max(1);
                deltas.push(g);
            }
        }
        4 => {
            // decreasing
            for i in 0..n.saturating_sub(1) {
                let g = ((n as i64) - (i as i64)).min(max_d_uniform).max(1);
                deltas.push(g);
            }
        }
        5 => {
            // one big gap in middle
            for i in 0..n.saturating_sub(1) {
                let g = if i == n.saturating_sub(1) / 2 { max_d_uniform } else { 1 };
                deltas.push(g);
            }
        }
        6 => {
            // small random
            for _ in 0..n.saturating_sub(1) {
                deltas.push(rng.gen_range_i64(1, 10.min(max_d_uniform).max(1)));
            }
        }
        7 => {
            // large random
            for _ in 0..n.saturating_sub(1) {
                deltas.push(rng.gen_range_i64(1, max_d_uniform));
            }
        }
        _ => {
            for _ in 0..n.saturating_sub(1) {
                deltas.push(rng.gen_range_i64(1, max_d_uniform));
            }
        }
    }

    // Pick base
    let total: i64 = deltas.iter().sum();
    let lo_base = -1_000_000_000i64;
    let hi_base = (1_000_000_000i64 - total).max(lo_base);
    let base = if lo_base == hi_base { lo_base } else { rng.gen_range_i64(lo_base, hi_base) };
    let mut x = Vec::with_capacity(n);
    x.push(base);
    for d in &deltas { x.push(*x.last().unwrap() + d); }
    x
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(56701);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
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

    // Boundary cases
    emit(vec![-1_000_000_000, -999_999_999], &mut seen, &mut out, &mut count);
    emit(vec![-1_000_000_000, -999_999_998], &mut seen, &mut out, &mut count);
    emit(vec![-1_000_000_000, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![999_999_999, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![-1_000_000_000, 0, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(vec![-1, 0, 1], &mut seen, &mut out, &mut count);
    // Symmetric cases
    emit(vec![-100, 100], &mut seen, &mut out, &mut count);
    emit(vec![-100, 0, 100], &mut seen, &mut out, &mut count);
    emit(vec![-100, -50, 50, 100], &mut seen, &mut out, &mut count);

    // Various sizes & patterns; aggressive coverage
    for &n in &[2usize, 3, 4, 5, 10, 100, 1000, 10_000, 50_000, 100_000] {
        for mode in 0..8usize {
            let x = make_sorted_with_pattern(&mut rng, n, mode);
            emit(x, &mut seen, &mut out, &mut count);
        }
    }

    // Many random patterns
    while count < target {
        let n = match rng.gen_range_usize(0, 6) {
            0 => 2,
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 100),
            3 => rng.gen_range_usize(100, 1000),
            4 => rng.gen_range_usize(1000, 10_000),
            _ => rng.gen_range_usize(10_000, 100_000),
        };
        let mode = rng.gen_range_usize(0, 8);
        let x = make_sorted_with_pattern(&mut rng, n, mode);
        emit(x, &mut seen, &mut out, &mut count);
    }
}

