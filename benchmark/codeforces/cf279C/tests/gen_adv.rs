use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr_in: &Vec<i64>,
    queries_in: &Vec<(i32, i32)>,
) -> (res: (Vec<i64>, Vec<(i32, i32)>))
    requires
        1 <= arr_in.len() <= 100_000,
        1 <= queries_in.len() <= 100_000,
        forall|i: int| 0 <= i < arr_in.len() ==> 1 <= #[trigger] arr_in[i] <= 1_000_000_000,
        forall|q: int| 0 <= q < queries_in.len() ==> {
            let (l1, r1) = #[trigger] queries_in[q];
            1 <= l1 && l1 <= r1 && (r1 as int) <= arr_in.len()
        },
    ensures
        1 <= res.0.len() <= 100_000,
        1 <= res.1.len() <= 100_000,
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 1_000_000_000,
        forall|q: int| 0 <= q < res.1.len() ==> {
            let (l1, r1) = #[trigger] res.1[q];
            1 <= l1 && l1 <= r1 && (r1 as int) <= res.0.len()
        },
{
    let mut arr: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < arr_in.len()
        invariant
            0 <= i <= arr_in.len(),
            arr.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] arr[k] == arr_in[k],
            forall|k: int| 0 <= k < arr_in.len() ==> 1 <= #[trigger] arr_in[k] <= 1_000_000_000,
        decreases arr_in.len() - i,
    {
        arr.push(arr_in[i]);
        i = i + 1;
    }

    let mut queries: Vec<(i32, i32)> = Vec::new();
    let mut j: usize = 0;
    while j < queries_in.len()
        invariant
            0 <= j <= queries_in.len(),
            queries.len() == j,
            forall|k: int| 0 <= k < j as int ==> #[trigger] queries[k] == queries_in[k],
            forall|q: int| 0 <= q < queries_in.len() ==> {
                let (l1, r1) = #[trigger] queries_in[q];
                1 <= l1 && l1 <= r1 && (r1 as int) <= arr_in.len()
            },
            arr.len() == arr_in.len(),
        decreases queries_in.len() - j,
    {
        queries.push(queries_in[j]);
        j = j + 1;
    }

    (arr, queries)
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
    let target: usize = 200;
    let mut rng = Rng::new(0x279CC);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 6 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 30),
            2 => rng.gen_range_usize(30, 200),
            3 => rng.gen_range_usize(200, 1000),
            4 => rng.gen_range_usize(1000, 10000),
            _ => rng.gen_range_usize(10000, 100000),
        };
        let m = match tries % 4 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 30),
            2 => rng.gen_range_usize(1, 1000),
            _ => rng.gen_range_usize(1, n.min(1000).max(1)),
        };
        let max_v = match tries % 3 {
            0 => 1_000_000_000i64,
            1 => 100i64,
            _ => 10_000i64,
        };
        let arr: Vec<i64> = match tries % 5 {
            0 => (0..n).map(|_| rng.gen_range_i64(1, max_v)).collect(),
            1 => (0..n).map(|i| (i as i64 + 1).min(max_v)).collect(), // increasing
            2 => (0..n).map(|i| (n as i64 - i as i64).min(max_v).max(1)).collect(), // decreasing
            3 => vec![1; n], // constant
            _ => (0..n).map(|i| if i % 2 == 0 { 1 } else { 2 }).collect(), // zigzag
        };
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

