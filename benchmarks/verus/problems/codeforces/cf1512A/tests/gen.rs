use vstd::prelude::*;

verus! {

pub open spec fn is_spy(a: Seq<i64>, i: int) -> bool {
    &&& 0 <= i < a.len()
    &&& forall|j: int| 0 <= j < a.len() && j != i ==> a[j] != a[i]
    &&& forall|j: int, k: int| 0 <= j < a.len() && 0 <= k < a.len() && j != i && k != i ==> a[j] == a[k]
}

pub fn generate_test_case(
    n: usize,
    common_val: i64,
    spy_val: i64,
    spy_pos: usize,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        3 <= n <= 100,
        spy_pos < n,
        common_val != spy_val,
    ensures
        3 <= result.len() <= 100,
        exists|i: int| is_spy(result@, i),
{
    let eff_n: usize;
    let eff_spy_pos: usize;
    let eff_common: i64;
    let eff_spy: i64;

    if mutation_kind == 0 {
        // identity
        eff_n = n; eff_spy_pos = spy_pos; eff_common = common_val; eff_spy = spy_val;
    } else if mutation_kind == 1 {
        // spy at start
        eff_n = n; eff_spy_pos = 0; eff_common = common_val; eff_spy = spy_val;
    } else if mutation_kind == 2 {
        // spy at end
        eff_n = n; eff_spy_pos = n - 1; eff_common = common_val; eff_spy = spy_val;
    } else if mutation_kind == 3 {
        // swap common and spy values
        eff_n = n; eff_spy_pos = spy_pos; eff_common = spy_val; eff_spy = common_val;
    } else if mutation_kind == 4 {
        // min length, spy at position 0
        eff_n = 3; eff_spy_pos = 0; eff_common = common_val; eff_spy = spy_val;
    } else if mutation_kind == 5 {
        // min length, spy at end
        eff_n = 3; eff_spy_pos = 2; eff_common = common_val; eff_spy = spy_val;
    } else if mutation_kind == 6 {
        // forced values: common=1, spy=2
        eff_n = n; eff_spy_pos = spy_pos; eff_common = 1; eff_spy = 2;
    } else if mutation_kind == 7 {
        // forced values: common=100, spy=1
        eff_n = n; eff_spy_pos = spy_pos; eff_common = 100; eff_spy = 1;
    } else if mutation_kind == 8 {
        // spy at position 1
        eff_n = n; eff_spy_pos = 1; eff_common = common_val; eff_spy = spy_val;
    } else if mutation_kind == 9 {
        // max length, spy at middle
        eff_n = 100; eff_spy_pos = 50; eff_common = common_val; eff_spy = spy_val;
    } else {
        // fallback: identity
        eff_n = n; eff_spy_pos = spy_pos; eff_common = common_val; eff_spy = spy_val;
    }

    // Build the array
    let mut a: Vec<i64> = Vec::new();
    let mut idx: usize = 0;
    while idx < eff_n
        invariant
            a.len() == idx,
            idx <= eff_n,
            3 <= eff_n <= 100,
            eff_spy_pos < eff_n,
            eff_common != eff_spy,
            forall|j: int| 0 <= j < idx as int && j != eff_spy_pos as int ==> a@[j] == eff_common,
            eff_spy_pos < idx ==> a@[eff_spy_pos as int] == eff_spy,
        decreases eff_n - idx,
    {
        if idx == eff_spy_pos {
            a.push(eff_spy);
        } else {
            a.push(eff_common);
        }
        idx += 1;
    }

    proof {
        // Witness: eff_spy_pos is the spy index
        assert forall|j: int| 0 <= j < a@.len() && j != eff_spy_pos as int implies a@[j] != a@[eff_spy_pos as int] by {
            assert(a@[j] == eff_common);
            assert(a@[eff_spy_pos as int] == eff_spy);
        };
        assert forall|j: int, k: int| 0 <= j < a@.len() && 0 <= k < a@.len() && j != eff_spy_pos as int && k != eff_spy_pos as int implies a@[j] == a@[k] by {
            assert(a@[j] == eff_common);
            assert(a@[k] == eff_common);
        };
        assert(is_spy(a@, eff_spy_pos as int));
    }

    a
}

}

use std::io::Write;

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

fn build_input(cases: &[Vec<i64>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[usize]) -> String {
    let mut s = String::new();
    for &a in answers {
        s.push_str(&format!("{}\n", a));
    }
    s
}

fn make_spy(rng: &mut Rng, n: usize, base: i64, spy: i64, idx: usize) -> Vec<i64> {
    let _ = rng;
    let mut a = vec![base; n];
    a[idx] = spy;
    a
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    // Examples
    {
        let cases: Vec<Vec<i64>> = vec![
            vec![11, 13, 11, 11],
            vec![1, 4, 4, 4, 4],
            vec![3, 3, 3, 3, 10, 3, 3, 3, 3, 3],
            vec![20, 20, 10],
        ];
        let answers: Vec<usize> = cases.iter().map(|a| Solution::spy_index(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    }

    let mut count = 1usize;

    // edges
    let edges: Vec<Vec<i64>> = vec![
        vec![1, 1, 100],
        vec![100, 1, 1],
        vec![1, 100, 1],
        vec![5, 5, 5, 5, 5, 5, 5, 5, 5, 1],
        vec![1; 100], // 99 1s and one 2 hidden somewhere
    ];
    for mut e in edges {
        if count >= target { break; }
        if e.iter().all(|&v| v == 1) { e[50] = 2; }
        let cases: Vec<Vec<i64>> = vec![e];
        let answers: Vec<usize> = cases.iter().map(|a| Solution::spy_index(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { 1 } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<Vec<i64>> = Vec::new();
        for _ in 0..t {
            let n = rng.gen_range_usize(3, 100);
            let base = rng.gen_range_i64(1, 100);
            let mut spy = rng.gen_range_i64(1, 100);
            if spy == base { spy = if base == 100 { 1 } else { base + 1 }; }
            let idx = rng.gen_range_usize(0, n - 1);
            let a = make_spy(&mut rng, n, base, spy, idx);
            cases.push(a);
        }
        let answers: Vec<usize> = cases.iter().map(|a| Solution::spy_index(a.clone())).collect();
        let inp = build_input(&cases);
        let outp = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

