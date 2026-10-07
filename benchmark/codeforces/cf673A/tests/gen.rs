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
) -> (result: Vec<i32>)
    requires
        deltas.len() + 1 <= 90,
        1 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 90,
    ensures
        1 <= result.len() && result.len() <= 90,
        forall|k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] && result[k] <= 90,
        forall|a: int, b: int|
            0 <= a < b < result.len() ==> #[trigger] result[a] < #[trigger] result[b],
{
    let mut t: Vec<i32> = Vec::new();

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(sum_deltas(deltas@, 0) == 0);
        assert(base as int <= 90);
    }

    t.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            t.len() == i + 1,
            deltas.len() + 1 <= 90,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 90,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] t[k] == (base as int + sum_deltas(deltas@, k)) as i32,
            forall|k: int| 0 <= k <= i as int ==>
                t[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < t.len() ==> 1 <= #[trigger] t[k] && t[k] <= 90,
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
            assert(1 <= next && next <= 90) by {
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(base as int + sum_deltas(deltas@, (i + 1) as int) <= 90);
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

    t
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

fn build_input(t: &[i32]) -> String {
    let mut s = format!("{}\n", t.len());
    let parts: Vec<String> = t.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn make_random_strict(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut all: Vec<i32> = (1..=90).collect();
    // Fisher-Yates partial shuffle
    let len = all.len();
    for i in 0..n.min(len) {
        let j = i + (rng.next_u64() as usize) % (len - i);
        all.swap(i, j);
    }
    let mut chosen: Vec<i32> = all.into_iter().take(n).collect();
    chosen.sort();
    chosen
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(673);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |t: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if t.is_empty() || t.len() > 90 { return; }
        for w in t.windows(2) { if w[0] >= w[1] { return; } }
        for &v in &t { if v < 1 || v > 90 { return; } }
        let key = format!("{:?}", t);
        if !seen.insert(key) { return; }
        let inp = build_input(&t);
        let ans = Solution::watch_minutes(t.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit(vec![7, 20, 88], &mut seen, &mut out, &mut count);
    emit(vec![16, 20, 30, 40, 50, 60, 70, 80, 90], &mut seen, &mut out, &mut count);
    emit(vec![15, 20, 30, 40, 50, 60, 70, 80, 90], &mut seen, &mut out, &mut count);

    // Edges
    emit(vec![1], &mut seen, &mut out, &mut count);
    emit(vec![15], &mut seen, &mut out, &mut count);
    emit(vec![16], &mut seen, &mut out, &mut count);
    emit(vec![90], &mut seen, &mut out, &mut count);
    emit((1..=90).collect(), &mut seen, &mut out, &mut count);
    emit(vec![1, 90], &mut seen, &mut out, &mut count);
    emit(vec![1, 16, 31], &mut seen, &mut out, &mut count);
    emit(vec![1, 17], &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 90);
        let t = make_random_strict(&mut rng, n);
        emit(t, &mut seen, &mut out, &mut count);
    }
}

