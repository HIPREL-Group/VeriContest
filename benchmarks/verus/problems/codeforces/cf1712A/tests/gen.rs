use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: usize,
    fill_val_raw: usize,
    mutation_kind: u8,
) -> (result: (Vec<i32>, usize, usize))
    requires
        1 <= k <= n <= 100,
        1 <= fill_val_raw <= 100,
    ensures
        result.0.len() == result.1,
        1 <= result.2 <= result.1 <= 100,
        forall|i: int| 0 <= i < result.1 ==> 1 <= #[trigger] result.0[i] && result.0[i] <= result.1 as int,
{
    let fill_val: usize = if fill_val_raw <= n { fill_val_raw } else { n };

    if mutation_kind == 1 {
        // All 1s
        let mut p: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                idx <= n,
                1 <= n <= 100,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] p[j] == 1i32,
            decreases n - idx,
        {
            p.push(1i32);
            idx += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < n as int implies 1 <= #[trigger] p[j] && p[j] <= n as int by {
                assert(p[j] == 1i32);
            };
        }
        return (p, n, k);
    }

    if mutation_kind == 2 {
        // All n
        let nval = n as i32;
        let mut p: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                idx <= n,
                1 <= n <= 100,
                nval == n as int,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] p[j] == nval,
            decreases n - idx,
        {
            p.push(nval);
            idx += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < n as int implies 1 <= #[trigger] p[j] && p[j] <= n as int by {
                assert(p[j] == nval);
            };
        }
        return (p, n, k);
    }

    if mutation_kind == 3 {
        // Sequential: 1, 2, ..., n
        let mut p: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                idx <= n,
                1 <= n <= 100,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] p[j] == (j + 1) as i32,
            decreases n - idx,
        {
            p.push((idx + 1) as i32);
            idx += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < n as int implies 1 <= #[trigger] p[j] && p[j] <= n as int by {
                assert(p[j] == (j + 1) as i32);
            };
        }
        return (p, n, k);
    }

    if mutation_kind == 4 {
        // Reverse: n, n-1, ..., 1
        let mut p: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                idx <= n,
                1 <= n <= 100,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] p[j] == (n as int - j) as i32,
            decreases n - idx,
        {
            p.push((n - idx) as i32);
            idx += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < n as int implies 1 <= #[trigger] p[j] && p[j] <= n as int by {
                assert(p[j] == (n as int - j) as i32);
            };
        }
        return (p, n, k);
    }

    if mutation_kind == 5 {
        // All k (k <= n, so k is a valid value)
        let kval = k as i32;
        let mut p: Vec<i32> = Vec::new();
        let mut idx: usize = 0;
        while idx < n
            invariant
                idx <= n,
                1 <= k <= n <= 100,
                kval == k as int,
                p.len() == idx,
                forall|j: int| 0 <= j < idx as int ==> #[trigger] p[j] == kval,
            decreases n - idx,
        {
            p.push(kval);
            idx += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < n as int implies 1 <= #[trigger] p[j] && p[j] <= n as int by {
                assert(p[j] == kval);
            };
        }
        return (p, n, k);
    }

    // Default (mutation_kind == 0 or fallback): all fill_val (clamped to [1, n])
    let fv = fill_val as i32;
    let mut p: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            idx <= n,
            1 <= n <= 100,
            1 <= fill_val <= n,
            fv == fill_val as int,
            p.len() == idx,
            forall|j: int| 0 <= j < idx as int ==> #[trigger] p[j] == fv,
        decreases n - idx,
    {
        p.push(fv);
        idx += 1;
    }
    proof {
        assert forall|j: int| 0 <= j < n as int implies 1 <= #[trigger] p[j] && p[j] <= n as int by {
            assert(p[j] == fv);
        };
    }
    (p, n, k)
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

// (n, k, p)
type TC = (usize, usize, Vec<i32>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, k, p) in cases {
        s.push_str(&format!("{} {}\n", n, k));
        let parts: Vec<String> = p.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (n, k, p) in cases {
        let ans = Solution::min_swaps_minimize_prefix_sum(p.clone(), *n, *k);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=n as i32).collect();
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1712);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (3, 1, vec![2, 3, 1]),
        (3, 3, vec![1, 2, 3]),
        (4, 2, vec![3, 4, 1, 2]),
        (1, 1, vec![1]),
        (5, 5, vec![5, 4, 3, 2, 1]),
        (5, 1, vec![5, 4, 3, 2, 1]),
        (10, 5, vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1]),
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let n = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 20),
                2 => rng.gen_range_usize(20, 100),
                _ => rng.gen_range_usize(1, 100),
            };
            let k = rng.gen_range_usize(1, n);
            let p = random_perm(&mut rng, n);
            cases.push((n, k, p));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

