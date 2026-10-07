use vstd::prelude::*;

verus! {

pub open spec fn sum_deltas(deltas: Seq<i64>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

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
    s_deltas: Vec<i64>,
    s_base: i64,
    gap: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        0 <= s_deltas.len() <= 199_999,
        0 <= s_base,
        1 <= gap,
        forall |k: int| 0 <= k < s_deltas.len() ==> 1 <= #[trigger] s_deltas[k],
        s_base as int + sum_deltas(s_deltas@, s_deltas.len() as int) + gap as int <= 1_000_000_000,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 200_000,
        forall |k: int| 0 <= k < result.0.len() ==> 0 <= #[trigger] result.0[k] <= 1_000_000_000,
        forall |k: int| 0 <= k < result.1.len() ==> 0 <= #[trigger] result.1[k] <= 1_000_000_000,
        forall |k: int| 0 <= k < result.0.len() ==> result.0[k] < result.1[k],
        forall |k: int| 0 <= k < result.0.len() - 1 ==> #[trigger] result.0[k] < result.0[k + 1],
        forall |k: int| 0 <= k < result.1.len() - 1 ==> #[trigger] result.1[k] < result.1[k + 1],
{
    let g: i64 = if mutation_kind == 1 && gap > 1 { 1i64 } else { gap };

    proof {
        lemma_sum_deltas_mono(s_deltas@, 0, s_deltas.len() as int);
    }

    if mutation_kind == 2 {
        // Single-element arrays
        let mut sv: Vec<i64> = Vec::new();
        let mut fv: Vec<i64> = Vec::new();
        sv.push(s_base);
        fv.push(s_base + gap);
        proof {
            assert(sv.len() == 1);
            assert(fv.len() == 1);
            assert(s_base as int + gap as int <= 1_000_000_000);
            assert(s_base < s_base + gap);
        }
        return (sv, fv);
    }

    let mut s: Vec<i64> = Vec::new();
    let mut f: Vec<i64> = Vec::new();

    s.push(s_base);
    f.push(s_base + g);

    let mut i: usize = 0;
    while i < s_deltas.len()
        invariant
            0 <= i <= s_deltas.len(),
            s.len() == i as int + 1,
            f.len() == i as int + 1,
            s_deltas.len() <= 199_999,
            0 <= s_base,
            1 <= g <= gap,
            forall |k: int| 0 <= k < s_deltas.len() ==> 1 <= #[trigger] s_deltas[k],
            s_base as int + sum_deltas(s_deltas@, s_deltas.len() as int) + gap as int <= 1_000_000_000,
            forall |k: int| 0 <= k <= i as int ==>
                #[trigger] s[k] as int == s_base as int + sum_deltas(s_deltas@, k),
            forall |k: int| 0 <= k <= i as int ==>
                #[trigger] f[k] as int == s[k] as int + g as int,
            forall |k: int| 0 <= k < s.len() ==> 0 <= #[trigger] s[k] <= 1_000_000_000i64,
            forall |k: int| 0 <= k < f.len() ==> 0 <= #[trigger] f[k] <= 1_000_000_000i64,
            forall |k: int, l: int| 0 <= k < l < s.len() ==> #[trigger] s[k] < #[trigger] s[l],
            forall |k: int, l: int| 0 <= k < l < f.len() ==> #[trigger] f[k] < #[trigger] f[l],
            forall |k: int| 0 <= k < s.len() ==> #[trigger] s[k] < #[trigger] f[k],
        decreases s_deltas.len() - i,
    {
        let ghost old_len = s.len();

        proof {
            lemma_sum_deltas_mono(s_deltas@, (i + 1) as int, s_deltas.len() as int);
        }

        let next_s = s[i] + s_deltas[i];
        let next_f = next_s + g;

        proof {
            assert(next_s as int == s_base as int + sum_deltas(s_deltas@, (i + 1) as int));

            // next_s upper bound
            assert(sum_deltas(s_deltas@, (i + 1) as int)
                <= sum_deltas(s_deltas@, s_deltas.len() as int));
            assert(next_s as int <= s_base as int + sum_deltas(s_deltas@, s_deltas.len() as int));
            assert(next_s as int <= 1_000_000_000 - gap as int);

            // next_s lower bound
            lemma_sum_deltas_mono(s_deltas@, 0, (i + 1) as int);
            assert(sum_deltas(s_deltas@, (i + 1) as int) >= 0);
            assert(next_s >= 0i64);

            // next_f bounds
            assert(next_f as int == next_s as int + g as int);
            assert(next_f as int <= next_s as int + gap as int);
            assert(next_f as int <= 1_000_000_000);
            assert(next_f >= 0i64);

            // next_s > all current s elements
            assert forall |k: int| 0 <= k < s.len() implies s[k] < next_s by {
                assert(s[k] as int == s_base as int + sum_deltas(s_deltas@, k));
                lemma_sum_deltas_strict(s_deltas@, k, (i + 1) as int);
            };

            // next_f > all current f elements
            assert forall |k: int| 0 <= k < f.len() implies f[k] < next_f by {
                assert(f[k] as int == s[k] as int + g as int);
                assert(next_f as int == next_s as int + g as int);
                assert(s[k] < next_s);
            };
        }

        s.push(next_s);
        f.push(next_f);

        proof {
            assert forall |k: int, l: int| 0 <= k < l < s.len() implies s[k] < s[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(s[l] == next_s);
                }
            };
            assert forall |k: int, l: int| 0 <= k < l < f.len() implies f[k] < f[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(f[l] == next_f);
                }
            };
        }

        i = i + 1;
    }

    (s, f)
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
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as u128;
        (lo as i128 + (v % r) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let x = self.next_u64();
        let v = ((x >> 32) ^ x) as usize;
        lo + v % (hi - lo + 1)
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

fn build_input(cases: &[(Vec<i64>, Vec<i64>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (sv, fv) in cases {
        s.push_str(&format!("{}\n", sv.len()));
        let p1: Vec<String> = sv.iter().map(|v| v.to_string()).collect();
        s.push_str(&p1.join(" "));
        s.push('\n');
        let p2: Vec<String> = fv.iter().map(|v| v.to_string()).collect();
        s.push_str(&p2.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[Vec<i64>]) -> String {
    let mut s = String::new();
    for d in answers {
        let parts: Vec<String> = d.iter().map(|v| v.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_valid(rng: &mut Rng, n: usize, max_t: i64) -> (Vec<i64>, Vec<i64>) {
    // Generate n strictly increasing s, then n strictly increasing f with s[i] < f[i].
    // We need s[0] < s[1] < ... < s[n-1], f[0] < f[1] < ... < f[n-1], s[i] < f[i].
    let mut s_vec: Vec<i64> = Vec::with_capacity(n);
    let mut last = 0i64;
    for _ in 0..n {
        let nv = last + 1 + rng.gen_range_i64(0, max_t / (n as i64 + 1));
        s_vec.push(nv);
        last = nv;
    }
    // Now generate f. We need f[i] > s[i] and f[i] > f[i-1].
    let mut f_vec: Vec<i64> = Vec::with_capacity(n);
    let mut last_f: i64 = 0;
    for i in 0..n {
        let lo = std::cmp::max(s_vec[i] + 1, last_f + 1);
        let hi = std::cmp::min(max_t, lo + max_t / (n as i64 + 1));
        let nv = if hi > lo { rng.gen_range_i64(lo, hi) } else { lo };
        f_vec.push(nv);
        last_f = nv;
    }
    (s_vec, f_vec)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let emit = |cases: &[(Vec<i64>, Vec<i64>)], seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let inp = build_input(cases);
        if !seen.insert(inp.clone()) { return; }
        let answers: Vec<Vec<i64>> = cases.iter().map(|(s, f)| Solution::restore_durations(s.clone(), f.clone())).collect();
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    let exs: Vec<(Vec<i64>, Vec<i64>)> = vec![
        (vec![0, 3, 7], vec![2, 10, 11]),
        (vec![10, 15], vec![11, 16]),
        (vec![12, 16, 90, 195, 1456, 1569, 3001, 5237, 19275], vec![13, 199, 200, 260, 9100, 10000, 10914, 91066, 5735533]),
        (vec![0], vec![1_000_000_000]),
    ];
    emit(&exs, &mut seen, &mut out, &mut count);
    for ex in &exs { emit(&[ex.clone()], &mut seen, &mut out, &mut count); }

    while count < target {
        let t: usize = if count < 5 { 1 } else { rng.gen_range_usize(1, 10) };
        let mut cases: Vec<(Vec<i64>, Vec<i64>)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 30);
            cases.push(build_valid(&mut rng, n, 1000));
        }
        emit(&cases, &mut seen, &mut out, &mut count);
    }
}

