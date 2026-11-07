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
    f: i64,
    a: i64,
    b: i64,
    mutation_kind: u8,
) -> (result: (Vec<i64>, i64, i64, i64))
    requires
        deltas.len() + 1 <= 200_000,
        1 <= base,
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        1 <= f <= 1_000_000_000,
        1 <= a <= 1_000_000_000,
        1 <= b <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 200_000,
        1 <= result.1 <= 1_000_000_000,
        1 <= result.2 <= 1_000_000_000,
        1 <= result.3 <= 1_000_000_000,
        forall|j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 1_000_000_000,
        forall|j: int| 1 <= j < result.0.len() ==> #[trigger] result.0[j - 1] < result.0[j],
{
    // Build strictly increasing m from base and deltas
    let mut m: Vec<i64> = Vec::new();

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(sum_deltas(deltas@, 0) == 0);
        assert(base as int + 0 <= 1_000_000_000);
        assert(1 <= base <= 1_000_000_000);
    }

    m.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            m.len() == i + 1,
            deltas.len() + 1 <= 200_000,
            1 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i64,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] m[k] == (base as int + sum_deltas(deltas@, k)) as i64,
            forall|k: int| 0 <= k <= i as int ==>
                m[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < m.len() ==> 1 <= #[trigger] m[k] <= 1_000_000_000,
            forall|k: int, l: int| 0 <= k < l < m.len() ==> m[k] < m[l],
        decreases deltas.len() - i,
    {
        let ghost old_len = m.len();

        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = m[i] + deltas[i];

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

            assert forall|k: int| 0 <= k < m.len() implies m[k] < next by {
                assert(m[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        m.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < m.len() implies m[k] < m[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(m[l] == next);
                }
            };
        }
    }

    // Apply mutations to f, a, b
    let mut out_f = f;
    let mut out_a = a;
    let mut out_b = b;

    if mutation_kind == 1 {
        out_f = 1;         // minimum charge
    } else if mutation_kind == 2 {
        out_f = 1_000_000_000; // maximum charge
    } else if mutation_kind == 3 && a < 1_000_000_000 {
        out_a = a + 1;     // nudge a up
    } else if mutation_kind == 4 && a > 1 {
        out_a = a - 1;     // nudge a down
    } else if mutation_kind == 5 && b < 1_000_000_000 {
        out_b = b + 1;     // nudge b up
    } else if mutation_kind == 6 && b > 1 {
        out_b = b - 1;     // nudge b down
    } else if mutation_kind == 7 {
        out_a = out_b;     // a == b edge case
    } else if mutation_kind == 8 {
        out_a = 1;         // minimum a
        out_b = 1_000_000_000; // maximum b
    } else if mutation_kind == 9 {
        out_a = 1_000_000_000; // maximum a
        out_b = 1;         // minimum b
    }

    (m, out_f, out_a, out_b)
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

// Each case: (f, a, b, m)
type Case = (i64, i64, i64, Vec<i64>);

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (f, a, b, m) in cases {
        s.push_str(&format!("{} {} {} {}\n", m.len(), f, a, b));
        let p: Vec<String> = m.iter().map(|x| x.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[bool]) -> String {
    let mut s = String::new();
    for &a in answers { s.push_str(if a {"YES\n"} else {"NO\n"}); }
    s
}

fn solve(c: &Case) -> bool {
    Solution::can_send_all_messages(c.3.clone(), c.0, c.1, c.2)
}

fn random_case(rng: &mut Rng, max_n: usize) -> Case {
    let n = rng.gen_range_usize(1, max_n);
    let f = rng.gen_range_i64(1, 1_000_000_000);
    let a = rng.gen_range_i64(1, 1_000_000_000);
    let b = rng.gen_range_i64(1, 1_000_000_000);
    // Generate strictly increasing m values
    let mut m: Vec<i64> = Vec::with_capacity(n);
    let mut last = 0i64;
    for _ in 0..n {
        let next_m = (last + rng.gen_range_i64(1, 100)).min(1_000_000_000);
        m.push(next_m);
        last = next_m;
        if last >= 1_000_000_000 { break; }
    }
    let n = m.len();
    if n == 0 { return (f, a, b, vec![1]); }
    (f, a, b, m)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1921);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Some hand-crafted examples
    let example: Vec<Case> = vec![
        (3, 1, 5, vec![3]),                  // f=3, a=1, b=5, m=[3]: gap=3, keep=3, b=5, step=3 -> spent=3, 3<3? false -> NO
        (5, 1, 5, vec![3]),                  // YES (4<5)
        (5, 1, 1, vec![1, 2, 3, 4, 5]),
        (10, 2, 3, vec![1, 5, 8]),
        (1_000_000_000, 1, 1, vec![1, 2, 3]),
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<bool> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    let edges: Vec<Case> = vec![
        (1, 1, 1, vec![1]),
        (1_000_000_000, 1_000_000_000, 1_000_000_000, vec![1]),
        (1_000_000_000, 1, 1, vec![1_000_000_000]),
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Case> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let c = random_case(&mut rng, 50);
            if total_n + c.3.len() > 200_000 { break; }
            total_n += c.3.len();
            cases.push(c);
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<bool> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

