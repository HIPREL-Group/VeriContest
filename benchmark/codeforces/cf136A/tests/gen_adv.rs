use vstd::prelude::*;

verus! {

pub open spec fn value_occurs(p: Seq<i32>, n: int, v: int) -> bool {
    exists|i: int| 0 <= i < n && p[i] == v
}

pub open spec fn is_permutation_1_to_n(p: Seq<i32>, n: int) -> bool {
    p.len() == n
        && 1 <= n <= 100
        && forall|i: int| 0 <= i < n ==> 1 <= #[trigger] p[i] <= n
        && forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j]
        && forall|v: int| 1 <= v <= n ==> #[trigger] value_occurs(p, n, v)
}

// Build permutation from a "base" (identity) composed with swaps represented by
// an auxiliary array `perm` where perm[i] gives the 1-indexed value at position i.
// The caller provides perm directly, we just verify it's a permutation.

pub fn generate_test_case(
    n: usize,
    perm: &Vec<i32>,
) -> (result: Vec<i32>)
    requires
        1 <= n <= 100,
        perm.len() == n,
        forall|i: int| 0 <= i < n as int ==> 1 <= #[trigger] perm[i] <= n as int,
        forall|i: int, j: int| 0 <= i < j < n as int ==> perm[i] != perm[j],
        forall|v: int| 1 <= v <= n as int ==> #[trigger] value_occurs(perm@, n as int, v),
    ensures
        result.len() == n,
        is_permutation_1_to_n(result@, n as int),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            1 <= n <= 100,
            perm.len() == n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] result[k] == perm[k],
            forall|k: int| 0 <= k < n as int ==> 1 <= #[trigger] perm[k] <= n as int,
        decreases n - i,
    {
        result.push(perm[i]);
        i = i + 1;
    }

    proof {
        assert(result.len() == n);
        assert forall|k: int| 0 <= k < n as int implies 1 <= #[trigger] result@[k] <= n as int by {
            assert(result@[k] == perm@[k]);
        }
        assert forall|a: int, b: int| 0 <= a < b < n as int implies result@[a] != result@[b] by {
            assert(result@[a] == perm@[a]);
            assert(result@[b] == perm@[b]);
        }
        assert forall|v: int| 1 <= v <= n as int implies #[trigger] value_occurs(result@, n as int, v) by {
            assert(value_occurs(perm@, n as int, v));
            let idx = choose|ii: int| 0 <= ii < n as int && perm@[ii] == v;
            assert(0 <= idx < n as int);
            assert(result@[idx] == perm@[idx]);
            assert(result@[idx] == v);
        }
    }

    result
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

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut p: Vec<i32> = (1..=(n as i32)).collect();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        p.swap(i, j);
    }
    p
}

fn build_input(p: &[i32]) -> String {
    let mut s = format!("{}\n", p.len());
    let parts: Vec<String> = p.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(r: &[i32]) -> String {
    let parts: Vec<String> = r.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join(" ");
    s.push('\n');
    s
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(31337);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);

    let mut emit = |p: Vec<i32>, out: &mut std::io::BufWriter<std::fs::File>| {
        let n = p.len();
        let r = Solution::inverse_presents(p.clone(), n);
        let inp = build_input(&p);
        let outp = build_output(&r);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
    };

    // boundary
    emit(vec![1], &mut out);
    emit(vec![1, 2], &mut out);
    emit(vec![2, 1], &mut out);
    emit((1..=100).collect(), &mut out);
    emit((1..=100).rev().collect(), &mut out);
    // single-cycle
    {
        let n = 100usize;
        let mut p = vec![0i32; n];
        for i in 0..n { p[i] = ((i + 1) % n + 1) as i32; }
        emit(p, &mut out);
    }
    // pairs (i->i+1, i+1->i)
    {
        for n in [4usize, 10, 50, 100] {
            let mut p = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 { p.push((i + 2) as i32); }
                else { p.push((i) as i32); }
            }
            emit(p, &mut out);
        }
    }

    let mut count = 10usize;
    while count < target {
        let n = match count % 5 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(50, 100),
            3 => 100,
            _ => rng.gen_range_usize(1, 100),
        };
        let p = random_perm(&mut rng, n);
        emit(p, &mut out);
        count += 1;
    }
}

