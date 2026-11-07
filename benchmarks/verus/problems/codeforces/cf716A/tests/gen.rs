use vstd::prelude::*;

verus! {

/// Sum of the first `end` elements of `deltas`, viewed as mathematical ints.
pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

/// sum_deltas is monotonically non-decreasing when all deltas >= 1.
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
    c: i64,
    mutation_kind: u8,
) -> (result: (usize, i64, Vec<i64>))
    requires
        deltas.len() + 1 <= 100_000,
        1 <= base,
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        1 <= c <= 1_000_000_000,
    ensures
        1 <= result.0 <= 100_000,
        result.0 == result.2.len(),
        1 <= result.1 <= 1_000_000_000,
        forall|u: int| 0 <= u < result.0 as int - 1 ==> #[trigger] result.2[u] < result.2[u + 1],
        forall|u: int| 0 <= u < result.0 as int ==> 1 <= #[trigger] result.2[u] <= 1_000_000_000,
{
    let n: usize = (deltas.len() + 1) as usize;

    // Build strictly increasing t from base and deltas
    let mut t: Vec<i64> = Vec::new();

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(sum_deltas(deltas@, 0) == 0);
        assert(base as int + 0 <= 1_000_000_000);
        assert(1 <= base <= 1_000_000_000);
    }

    t.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            t.len() == i + 1,
            deltas.len() + 1 <= 100_000,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i64,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] t[k] == (base as int + sum_deltas(deltas@, k)) as i64,
            forall|k: int| 0 <= k <= i as int ==>
                t[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < t.len() ==> 1 <= #[trigger] t[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < t.len() ==> t[k] < t[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = t.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = t[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            assert(1 <= next <= 1_000_000_000) by {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) <= 1_000_000_000);
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
                assert(sum_deltas(deltas@, (i + 1) as int) >= 0);
                assert(next as int >= base as int);
                assert(next as int >= 1);
            };

            assert forall|k: int| 0 <= k < t.len() implies t[k] < next by {
                assert(t[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        t.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < t.len() implies t[k] < t[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(t[l] == next);
                }
            };
        }
    }

    // Apply mutations to c
    let mut out_c = c;

    if mutation_kind == 1 {
        out_c = 1;                  // minimum c
    } else if mutation_kind == 2 {
        out_c = 1_000_000_000;      // maximum c
    } else if mutation_kind == 3 && c < 1_000_000_000 {
        out_c = c + 1;              // nudge c up
    } else if mutation_kind == 4 && c > 1 {
        out_c = c - 1;              // nudge c down
    } else if mutation_kind == 5 {
        out_c = 500_000_000;        // midpoint
    }

    (n, out_c, t)
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

fn build_input(n: usize, c: i64, t: &[i64]) -> String {
    let mut s = format!("{} {}\n", n, c);
    let parts: Vec<String> = t.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn make_strict_inc(rng: &mut Rng, n: usize, max_v: i64, max_gap: i64) -> Vec<i64> {
    let mut v: Vec<i64> = Vec::with_capacity(n);
    let mut cur: i64 = rng.gen_range_i64(1, (max_v - n as i64 * max_gap.max(1)).max(1).min(max_v));
    v.push(cur.max(1));
    for _ in 1..n {
        let gap = rng.gen_range_i64(1, max_gap.max(1));
        cur += gap;
        if cur > max_v { cur = max_v; }
        v.push(cur);
    }
    // Ensure strict increase
    for i in 1..v.len() {
        if v[i] <= v[i - 1] { v[i] = v[i - 1] + 1; }
    }
    // Cap at max_v
    if v[v.len() - 1] > max_v {
        // shift down
        let excess = v[v.len() - 1] - max_v;
        for x in &mut v {
            *x -= excess;
        }
    }
    if v[0] < 1 {
        // shift up
        let need = 1 - v[0];
        for x in &mut v { *x += need; }
    }
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(716);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |c: i64, t: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if t.is_empty() || t.len() > 100_000 { return; }
        if c < 1 || c > 1_000_000_000 { return; }
        for w in t.windows(2) { if w[0] >= w[1] { return; } }
        for &v in &t { if v < 1 || v > 1_000_000_000 { return; } }
        let key = format!("{}|{:?}", c, t);
        if !seen.insert(key) { return; }
        let inp = build_input(t.len(), c, &t);
        let ans = Solution::remaining_words(t.len(), c, t.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(5, vec![1, 3, 8, 14, 19, 20], &mut seen, &mut out, &mut count);
    emit(1, vec![1, 3, 5, 7, 9, 10], &mut seen, &mut out, &mut count);

    // Edges
    emit(1, vec![1], &mut seen, &mut out, &mut count);
    emit(1_000_000_000, vec![1, 1_000_000_000], &mut seen, &mut out, &mut count);
    emit(1, vec![1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(1, vec![1, 3, 5, 7], &mut seen, &mut out, &mut count);
    emit(2, vec![1, 3, 5, 7], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let c = rng.gen_range_i64(1, 100);
        let t = make_strict_inc(&mut rng, n, 1_000_000_000, 50);
        emit(c, t, &mut seen, &mut out, &mut count);
    }
}

