use vstd::prelude::*;

verus! {

/// Build an identity permutation [1, 2, ..., n] then apply a mutation.
pub fn generate_test_case(
    n: usize,
    swap_i: usize,
    swap_j: usize,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        2 <= n <= 100_000,
        swap_i < n,
        swap_j < n,
    ensures
        2 <= result.len() <= 100_000,
        forall|j: int|
            0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= result.len() as int,
{
    // Build identity permutation [1, 2, ..., n]
    let mut p: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            p.len() == i,
            2 <= n <= 100_000,
            forall|k: int| 0 <= k < i ==> #[trigger] p[k] == (k + 1) as i32,
        decreases n - i,
    {
        p.push((i + 1) as i32);
        i += 1;
    }

    assert(p.len() == n);
    assert forall|j: int| 0 <= j < p.len() implies 1 <= #[trigger] p[j] <= p.len() as int by {
        assert(p[j] == (j + 1) as i32);
    }

    if mutation_kind == 0 {
        // identity
        p
    } else if mutation_kind == 1 && swap_i != swap_j {
        // swap two elements
        let vi = p[swap_i];
        let vj = p[swap_j];
        let ghost old_p = p@;
        p.set(swap_i, vj);
        p.set(swap_j, vi);
        assert(p.len() == n);
        assert forall|j: int| 0 <= j < p.len() implies 1 <= #[trigger] p[j] <= p.len() as int by {
            if j == swap_i as int {
                assert(p[j] == vj);
                assert(vj == old_p[swap_j as int]);
                assert(1 <= old_p[swap_j as int] <= n as int);
            } else if j == swap_j as int {
                assert(p[j] == vi);
                assert(vi == old_p[swap_i as int]);
                assert(1 <= old_p[swap_i as int] <= n as int);
            } else {
                assert(p[j] == old_p[j]);
                assert(1 <= old_p[j] <= n as int);
            }
        }
        p
    } else if mutation_kind == 2 {
        // reverse the permutation
        let mut q: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                q.len() == k,
                p.len() == n,
                2 <= n <= 100_000,
                forall|j: int| 0 <= j < p.len() ==> 1 <= #[trigger] p[j] <= p.len() as int,
                forall|j: int| 0 <= j < k ==> #[trigger] q[j] == p[(n - 1 - j) as int],
            decreases n - k,
        {
            q.push(p[n - 1 - k]);
            k += 1;
        }
        assert(q.len() == n);
        assert forall|j: int| 0 <= j < q.len() implies 1 <= #[trigger] q[j] <= q.len() as int by {
            assert(q[j] == p[(n - 1 - j) as int]);
            assert(1 <= p[(n - 1 - j) as int] <= n as int);
        }
        q
    } else if mutation_kind == 3 {
        // shift left by 1: [p[1], p[2], ..., p[n-1], p[0]]
        let mut q: Vec<i32> = Vec::new();
        let mut k: usize = 1;
        while k < n
            invariant
                1 <= k <= n,
                q.len() == k - 1,
                p.len() == n,
                2 <= n <= 100_000,
                forall|j: int| 0 <= j < p.len() ==> 1 <= #[trigger] p[j] <= p.len() as int,
                forall|j: int| 0 <= j < q.len() ==> #[trigger] q[j] == p[(j + 1) as int],
            decreases n - k,
        {
            q.push(p[k]);
            k += 1;
        }
        q.push(p[0]);
        assert(q.len() == n);
        assert forall|j: int| 0 <= j < q.len() implies 1 <= #[trigger] q[j] <= q.len() as int by {
            if j < n as int - 1 {
                assert(q[j] == p[(j + 1) as int]);
                assert(1 <= p[(j + 1) as int] <= n as int);
            } else {
                assert(q[j] == p[0]);
                assert(1 <= p[0] <= n as int);
            }
        }
        q
    } else if mutation_kind == 4 {
        // set all elements to 1 (edge case for fixed-point counting)
        let mut q: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                q.len() == k,
                2 <= n <= 100_000,
                forall|j: int| 0 <= j < k ==> #[trigger] q[j] == 1i32,
            decreases n - k,
        {
            q.push(1i32);
            k += 1;
        }
        assert(q.len() == n);
        assert forall|j: int| 0 <= j < q.len() implies 1 <= #[trigger] q[j] <= q.len() as int by {
            assert(q[j] == 1i32);
        }
        q
    } else if mutation_kind == 5 {
        // set element at swap_i to n (max value)
        let ghost old_p = p@;
        p.set(swap_i, n as i32);
        assert(p.len() == n);
        assert forall|j: int| 0 <= j < p.len() implies 1 <= #[trigger] p[j] <= p.len() as int by {
            if j == swap_i as int {
                assert(p[j] == n as i32);
            } else {
                assert(p[j] == old_p[j]);
                assert(1 <= old_p[j] <= n as int);
            }
        }
        p
    } else if mutation_kind == 6 {
        // set element at swap_i to 1 (min value)
        let ghost old_p = p@;
        p.set(swap_i, 1i32);
        assert(p.len() == n);
        assert forall|j: int| 0 <= j < p.len() implies 1 <= #[trigger] p[j] <= p.len() as int by {
            if j == swap_i as int {
                assert(p[j] == 1i32);
            } else {
                assert(p[j] == old_p[j]);
                assert(1 <= old_p[j] <= n as int);
            }
        }
        p
    } else {
        // fallback — identity
        p
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

fn build_input(cases: &[Vec<i32>]) -> String {
    let mut s = format!("{}\n", cases.len());
    for p in cases {
        s.push_str(&format!("{}\n", p.len()));
        let parts: Vec<String> = p.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(answers: &[i32]) -> String {
    let mut s = String::new();
    for a in answers { s.push_str(&format!("{}\n", a)); }
    s
}

fn random_perm(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = (1..=n as i32).collect();
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        v.swap(i, j);
    }
    v
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1855);
    let mut seen: HashSet<String> = HashSet::new();

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Example
    let example: Vec<Vec<i32>> = vec![
        vec![2, 1],
        vec![1, 2, 3],
        vec![1, 2, 5, 4, 3],
        vec![1, 2, 4, 3],
        vec![10, 2, 1, 3, 6, 5, 4, 7, 9, 8],
    ];
    {
        let inp = build_input(&example);
        let answers: Vec<i32> = example.iter().map(|p| Solution::min_swaps(p.clone())).collect();
        let outs = build_output(&answers);
        if seen.insert(inp.clone()) {
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
            count += 1;
        }
    }

    // Edge cases
    let edges: Vec<Vec<i32>> = vec![
        vec![2, 1],
        vec![1, 2],
        (1..=10).collect(),  // Identity n=10
        (1..=10).rev().collect(), // Reversed n=10
        vec![2, 1, 4, 3, 6, 5, 8, 7, 10, 9],
    ];
    for ec in &edges {
        if count >= target { break; }
        let cases = vec![ec.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|p| Solution::min_swaps(p.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Bundled multi-test
    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(2, 6) } else { rng.gen_range_usize(3, 15) };
        let mut cases: Vec<Vec<i32>> = Vec::new();
        let mut total_n = 0usize;
        for _ in 0..t {
            let n = rng.gen_range_usize(2, 100);
            if total_n + n > 100_000 { break; }
            total_n += n;
            cases.push(random_perm(&mut rng, n));
        }
        if cases.is_empty() { continue; }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let answers: Vec<i32> = cases.iter().map(|p| Solution::min_swaps(p.clone())).collect();
        let outs = build_output(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

