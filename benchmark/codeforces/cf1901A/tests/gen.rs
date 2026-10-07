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
    x: i64,
    deltas: Vec<i64>,
    mutation_kind: u8,
) -> (result: (i64, Vec<i64>))
    requires
        2 <= x <= 100,
        1 <= deltas.len() <= 50,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        sum_deltas(deltas@, deltas.len() as int) < x as int,
    ensures
        1 <= result.1.len() <= 50,
        2 <= result.0 <= 100,
        forall|j: int|
            0 <= j < result.1.len() as int - 1 ==> (#[trigger] result.1[j] as int) < (result.1[j + 1] as int),
        forall|j: int|
            0 <= j < result.1.len() as int ==> 0 < #[trigger] result.1[j] as int && (result.1[j] as int) < result.0 as int,
{
    // Build strictly increasing array from cumulative sums of deltas
    let mut a: Vec<i64> = Vec::new();

    proof {
        // sum_deltas(deltas@, 1) == deltas[0]
        assert(sum_deltas(deltas@, 1) == sum_deltas(deltas@, 0) + deltas@[0] as int);
        assert(sum_deltas(deltas@, 0) == 0int);
        assert(sum_deltas(deltas@, 1) == deltas@[0] as int);
        lemma_sum_deltas_mono(deltas@, 1, deltas.len() as int);
    }

    a.push(deltas[0]);

    let mut i: usize = 1;
    while i < deltas.len()
        invariant
            1 <= i <= deltas.len(),
            a.len() == i,
            deltas.len() <= 50,
            2 <= x <= 100,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i64,
            sum_deltas(deltas@, deltas.len() as int) < x as int,
            forall|k: int| 0 <= k < i as int ==>
                (#[trigger] a[k]) as int == sum_deltas(deltas@, (k + 1) as int),
            forall|k: int, l: int| 0 <= k < l < a.len() ==> a[k] < a[l],
            forall|k: int| 0 <= k < a.len() ==> 0 < (#[trigger] a[k]) as int,
            forall|k: int| 0 <= k < a.len() ==> (a[k] as int) < x as int,
        decreases deltas.len() - i,
    {
        let prev = a[i - 1];

        proof {
            assert(prev as int == sum_deltas(deltas@, i as int));
            // Prove next value = sum_deltas up to i+1
            assert(sum_deltas(deltas@, (i + 1) as int)
                == sum_deltas(deltas@, i as int) + deltas@[i as int] as int);

            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
            // So sum_deltas(i+1) <= sum_deltas(n) < x <= 100
            // And prev >= 0, deltas[i] >= 1
            // prev + deltas[i] = sum_deltas(i+1) < x <= 100
            // Both prev and deltas[i] are < 100, so no overflow in i64
        }

        let next = prev + deltas[i];

        proof {
            assert(next as int == sum_deltas(deltas@, (i + 1) as int));
            assert((next as int) < (x as int));

            lemma_sum_deltas_strict(deltas@, 0, (i + 1) as int);
            assert(next as int >= (i + 1) as int);
            assert(next as int > 0);

            assert forall|k: int| 0 <= k < a.len() implies a[k] < next by {
                assert(a[k] as int == sum_deltas(deltas@, (k + 1) as int));
                lemma_sum_deltas_strict(deltas@, (k + 1) as int, (i + 1) as int);
            };
        }

        a.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < a.len() implies a[k] < a[l] by {
                if l < (a.len() - 1) as int {
                } else {
                    assert(a[l] == next);
                }
            };
        }
    }

    // Apply mutations
    if mutation_kind == 1 {
        // minimize x: set to last element + 1
        let last_idx = a.len() - 1;
        let last_val = a[last_idx];
        let new_x = last_val + 1;
        proof {
            assert(last_val as int == sum_deltas(deltas@, deltas.len() as int));
            lemma_sum_deltas_strict(deltas@, 0, deltas.len() as int);
            assert(last_val as int >= deltas.len() as int);
            assert(last_val >= 1);
            assert(new_x >= 2);
            assert(new_x as int <= x as int);
            assert(new_x <= 100);
            assert forall|j: int| 0 <= j < a.len() implies
                (a[j] as int) < new_x as int by {
                if j < last_idx as int {
                } else {
                    assert(a[j] == last_val);
                }
            };
        }
        (new_x, a)
    } else if mutation_kind == 2 && a.len() > 1 {
        // shrink: pop last element
        let mut v = a;
        v.pop();
        proof {
            assert(v.len() >= 1);
        }
        (x, v)
    } else if mutation_kind == 3 {
        // maximize x
        proof {
            assert forall|j: int| 0 <= j < a.len() implies
                (a[j] as int) < 100int by {
                assert((a[j] as int) < x as int);
            };
        }
        (100i64, a)
    } else {
        // identity
        (x, a)
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

type Case = (i64, Vec<i64>); // (x, a)

fn build_input(cases: &[Case]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (x, a) in cases {
        s.push_str(&format!("{} {}\n", a.len(), x));
        let p: Vec<String> = a.iter().map(|v| v.to_string()).collect();
        s.push_str(&p.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn solve(c: &Case) -> i64 {
    Solution::min_tank_liters(c.0, c.1.clone())
}

fn random_case(rng: &mut Rng) -> Case {
    let x = rng.gen_range_i64(2, 100);
    let max_n = (x - 1).min(50);
    if max_n < 1 { return (x, vec![1]); }
    let n = rng.gen_range_i64(1, max_n) as usize;
    // Pick n distinct values in 1..x-1
    let mut chosen: Vec<i64> = Vec::with_capacity(n);
    let mut available: Vec<i64> = (1..x).collect();
    for _ in 0..n {
        let idx = (rng.next_u64() as usize) % available.len();
        chosen.push(available.swap_remove(idx));
    }
    chosen.sort();
    (x, chosen)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1901);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Case> = vec![
        (7, vec![1, 2, 5]),
        (6, vec![1, 2, 5]),
        (10, vec![7]),
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i64> = example.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edges
    let edges: Vec<Case> = vec![
        (2, vec![1]),
        (100, vec![1]),
        (100, vec![99]),
        (100, vec![50]),
        (100, (1..=50).collect()),
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 30 { rng.gen_range_usize(2, 8) } else { rng.gen_range_usize(5, 30) };
        let mut cases: Vec<Case> = Vec::new();
        for _ in 0..t {
            cases.push(random_case(&mut rng));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i64> = cases.iter().map(|c| solve(c)).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

