use vstd::prelude::*;

verus! {

pub open spec fn spec_sum_upto(s: Seq<i64>, n: int) -> int
    decreases n,
{
    if n <= 0 { 0 } else { spec_sum_upto(s, n - 1) + s[n - 1] }
}

pub fn input_sum(a: &Vec<i64>) -> (result: i64)
    requires
        1 <= a.len() <= 200000,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 1000000000,
    ensures
        result == spec_sum_upto(a@, a.len() as int),
        a.len() <= result <= a.len() * 1000000000,
{
    let mut i = 0usize;
    let mut sum = 0i64;
    while i < a.len()
        invariant
            1 <= a.len() <= 200000,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000000000,
            0 <= i <= a.len(),
            i <= sum <= i * 1000000000,
            sum == spec_sum_upto(a@, i as int),
        decreases a.len() - i,
    {
        sum += a[i];
        i += 1;
    }
    sum
}

pub fn generate_test_case(raw: Vec<i64>, k: i64) -> (result: (usize, i64, Vec<i64>))
    ensures
        1 <= result.0 <= 200000,
        result.0 == result.2.len(),
        sorted(result.2@, result.0 as int),
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= 1000000000,
        1 <= result.1 <= 1000000000,
        result.1 <= spec_sum_upto(result.2@, result.0 as int),
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 200000 { 200000usize } else { raw.len() };
    let mut a: Vec<i64> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 200000, 0 <= i <= n, a.len() == i,
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 1000000000,
            forall|j: int| 0 <= j < a.len() - 1 ==> #[trigger] a[j] <= a[j + 1],
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 1 };
        let mut v = if v < 1 { 1 } else if v > 1000000000 { 1000000000 } else { v };
        if i > 0 && v < a[i - 1] { v = a[i - 1]; }
        a.push(v);
        i += 1;
    }
    let sum = input_sum(&a);
    let k = if k < 1 { 1 } else if k > 1000000000 { 1000000000 } else { k };
    let k = if k > sum { sum } else { k };
    (n, k, a)
}


pub open spec fn sorted(s: Seq<i64>, n: int) -> bool {
    n <= s.len() && forall|i: int| 0 <= i < n - 1 ==> #[trigger] s[i] <= s[i + 1]
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

pub fn generate_candidate(
    deltas: &Vec<i64>,
    base: i64,
    k: i64,
    mutation_kind: u8,
) -> (result: (usize, i64, Vec<i64>))
    requires
        deltas.len() + 1 >= 1,
        deltas.len() + 1 <= 200_000,
        1 <= base <= 1_000_000_000,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
        1 <= k <= 1_000_000_000,
    ensures
        1 <= result.0 <= 200_000,
        result.0 == result.2.len(),
        sorted(result.2@, result.0 as int),
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] && result.2[i] <= 1_000_000_000,
        1 <= result.1 <= 1_000_000_000,
{
    let n: usize = deltas.len() + 1;

    let mut a: Vec<i64> = Vec::new();
    a.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            a.len() == idx + 1,
            n == deltas.len() + 1,
            1 <= n <= 200_000,
            1 <= base <= 1_000_000_000,
            forall|j: int| 0 <= j < deltas.len() ==> 0 <= #[trigger] deltas[j],
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 1_000_000_000,
            forall|j: int| 0 <= j <= idx as int ==>
                #[trigger] a[j] as int == base as int + sum_deltas(deltas@, j),
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] && a[j] <= 1_000_000_000,
            forall|j: int| 0 <= j < a.len() - 1 ==> #[trigger] a[j] <= a[j + 1],
        decreases deltas.len() - idx,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = a[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));

            assert(1 <= next) by {
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
            };

            assert(next <= 1_000_000_000) by {
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
            };

            assert(a[idx as int] <= next) by {
                assert(a[idx as int] as int == base as int + sum_deltas(deltas@, idx as int));
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_mono(deltas@, idx as int, (idx + 1) as int);
            };
        }

        let ghost old_len = a.len();
        a.push(next);
        idx = idx + 1;

        proof {
            assert forall|j: int| 0 <= j < a.len() - 1 implies #[trigger] a[j] <= a[j + 1] by {
                if j < old_len as int - 1 {
                } else {
                    assert(j == old_len as int - 1);
                    assert(a[j] <= next);
                }
            };
        }
    }

    assert(a.len() == n);

    proof {
        assert(sorted(a@, n as int)) by {
            assert(n as int <= a@.len());
            assert forall|i: int| 0 <= i < n as int - 1 implies #[trigger] a@[i] <= a@[i + 1] by {};
        };
    }

    let mutated_k: i64 =
        if mutation_kind == 1 {
            1i64
        } else if mutation_kind == 2 {
            1_000_000_000i64
        } else if mutation_kind == 3 && k < 1_000_000_000 {
            k + 1
        } else if mutation_kind == 4 && k > 1 {
            k - 1
        } else {
            k
        };

    (n, mutated_k, a)
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
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
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

fn solve(a: Vec<i64>, k: i64) -> i64 {
    let n = a.len();
    let mut sa = a.clone();
    sa.sort();
    Solution::min_lemonade_presses(n, k, sa)
}

fn build_input(cases: &[(Vec<i64>, i64)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, k) in cases {
        s.push_str(&format!("{} {}\n", a.len(), k));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i64]) -> String {
    let mut s = String::new();
    for ans in answers {
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    let example: Vec<(Vec<i64>, i64)> = vec![
        (vec![1], 1),
        (vec![1, 2], 2),
        (vec![2, 1, 3], 4),
        (vec![1, 1, 3, 8, 8, 9, 12, 13, 27, 27], 50),
        (vec![1_000_000_000, 500_000_000], 1_000_000_000),
    ];
    {
        let answers: Vec<i64> = example.iter().map(|(a, k)| solve(a.clone(), *k)).collect();
        let example: Vec<_> = example.iter().map(|c| {
            let (_, k, a) = generate_test_case(c.0.clone(), c.1);
            (a, k)
        }).collect();
        let inp = build_input(&example);
        let outp = build_output(&answers);
        let key = format!("{:?}", example);
        if seen.insert(key) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    while count < target {
        let t: usize = if count < 10 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 20) };
        let mut cases: Vec<(Vec<i64>, i64)> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(1, 30);
            let max_a = if count < 30 { 20 } else { 1_000_000 };
            let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_a)).collect();
            let total: i64 = a.iter().sum();
            let k = rng.gen_range_i64(1, total);
            cases.push((a, k));
        }
        let key = format!("{:?}", cases);
        if !seen.insert(key) { continue; }
        let answers: Vec<i64> = cases.iter().map(|(a, k)| solve(a.clone(), *k)).collect();
        let cases: Vec<_> = cases.iter().map(|c| {
            let (_, k, a) = generate_test_case(c.0.clone(), c.1);
            (a, k)
        }).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
