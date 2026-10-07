use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr: Vec<i64>,
    queries: Vec<(i32, i32)>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<(i32, i32)>))
    requires
        1 <= arr.len() <= 100_000,
        1 <= queries.len() <= 100_000,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1_000_000_000,
        forall|q: int| {
            &&&
            0 <= q < queries.len() ==> {
                let (l1, r1) = #[trigger] queries[q];
                1 <= l1 && l1 <= r1 && (r1 as int) <= arr.len()
            }
        },
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|q: int| {
            &&&
            0 <= q < result.1.len() ==> {
                let (l1, r1) = #[trigger] result.1[q];
                1 <= l1 && l1 <= r1 && (r1 as int) <= result.0.len()
            }
        },
{
    if mutation_kind == 0 {
        // identity
        (arr, queries)
    } else if mutation_kind == 1 {
        // set first arr element to 1 (min boundary)
        let mut d = arr;
        d.set(0, 1);
        (d, queries)
    } else if mutation_kind == 2 {
        // set first arr element to 1_000_000_000 (max boundary)
        let mut d = arr;
        d.set(0, 1_000_000_000);
        (d, queries)
    } else if mutation_kind == 3 && arr[0] < 1_000_000_000 {
        // nudge first arr element up
        let mut d = arr;
        d.set(0, d[0] + 1);
        (d, queries)
    } else if mutation_kind == 4 && arr[0] > 1 {
        // nudge first arr element down
        let mut d = arr;
        d.set(0, d[0] - 1);
        (d, queries)
    } else if mutation_kind == 5 {
        // set all arr elements to 1 (constant array - trivially a ladder)
        let n = arr.len();
        let mut d = arr;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == n,
                1 <= n <= 100_000,
                forall|j: int| 0 <= j < i ==> d[j] == 1i64,
                forall|j: int| i as int <= j < d.len() as int ==> 1 <= #[trigger] d[j] <= 1_000_000_000,
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, queries)
    } else if mutation_kind == 6 {
        // set first query to (1, 1) - single element query
        let mut d = queries;
        d.set(0, (1i32, 1i32));
        (arr, d)
    } else if mutation_kind == 7 && (arr.len() as i32) > 0 && arr.len() <= i32::MAX as usize {
        // set first query to full range
        let n = arr.len() as i32;
        let mut d = queries;
        d.set(0, (1i32, n));
        (arr, d)
    } else {
        // fallback identity
        (arr, queries)
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

fn build_input(arr: &[i64], queries: &[(i32, i32)]) -> String {
    let n = arr.len();
    let m = queries.len();
    let mut s = format!("{} {}\n", n, m);
    let parts: Vec<String> = arr.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    for &(l, r) in queries {
        s.push_str(&format!("{} {}\n", l, r));
    }
    s
}

fn build_output(ans: &[bool]) -> String {
    let mut s = String::new();
    for &a in ans {
        s.push_str(if a { "Yes\n" } else { "No\n" });
    }
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(279);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    {
        let arr = vec![1i64, 2, 1, 2, 1, 2, 1, 2];
        let queries = vec![(1i32, 2), (2, 3), (1, 3), (2, 4), (1, 4), (3, 4)];
        let inp = build_input(&arr, &queries);
        if seen.insert(inp.clone()) {
            let ans = Solution::query_ladders(arr, queries);
            let outp = build_output(&ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }
    {
        let arr = vec![5i64];
        let queries = vec![(1i32, 1)];
        let inp = build_input(&arr, &queries);
        if seen.insert(inp.clone()) {
            let ans = Solution::query_ladders(arr, queries);
            let outp = build_output(&ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 10000),
        };
        let m = match tries % 4 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 20),
            2 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, n.min(1000).max(1)),
        };
        let max_v = match tries % 3 {
            0 => 100i64,
            1 => 10_000i64,
            _ => 1_000_000_000i64,
        };
        let arr: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect();
        let mut queries = Vec::with_capacity(m);
        for _ in 0..m {
            let l = rng.gen_range_usize(1, n);
            let r = rng.gen_range_usize(l, n);
            queries.push((l as i32, r as i32));
        }
        let inp = build_input(&arr, &queries);
        if !seen.insert(inp.clone()) { continue; }
        let ans = Solution::query_ladders(arr, queries);
        let outp = build_output(&ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

