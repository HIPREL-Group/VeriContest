use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a: Vec<i64>,
    queries: Vec<(usize, usize)>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<(usize, usize)>))
    requires
        2 <= a.len() <= 200000,
        forall|i: int| 0 <= i < a.len() as int ==> 1 <= #[trigger] a[i] <= 1000000,
        forall|k: int| 0 <= k < queries.len() as int ==> 1 <= #[trigger] queries[k].0 < queries[k].1 <= a.len(),
    ensures
        2 <= result.0.len() <= 200000,
        forall|i: int| 0 <= i < result.0.len() as int ==> 1 <= #[trigger] result.0[i] <= 1000000,
        forall|k: int| 0 <= k < result.1.len() as int ==> 1 <= #[trigger] result.1[k].0 < result.1[k].1 <= result.0.len(),
{
    if mutation_kind == 0 {
        // identity
        (a, queries)
    } else if mutation_kind == 1 {
        // set all elements to a[0] (all-equal array)
        let val = a[0];
        let mut arr = a;
        let mut idx: usize = 0;
        while idx < arr.len()
            invariant
                arr.len() == a.len(),
                2 <= arr.len() <= 200000,
                0 <= idx <= arr.len(),
                1 <= val <= 1000000,
                forall|j: int| 0 <= j < arr.len() as int ==> 1 <= #[trigger] arr[j] <= 1000000,
            decreases arr.len() - idx,
        {
            arr.set(idx, val);
            idx += 1;
        }
        (arr, queries)
    } else if mutation_kind == 2 {
        // set all elements to 1 (minimum value)
        let mut arr = a;
        let mut idx: usize = 0;
        while idx < arr.len()
            invariant
                arr.len() == a.len(),
                2 <= arr.len() <= 200000,
                0 <= idx <= arr.len(),
                forall|j: int| 0 <= j < arr.len() as int ==> 1 <= #[trigger] arr[j] <= 1000000,
            decreases arr.len() - idx,
        {
            arr.set(idx, 1i64);
            idx += 1;
        }
        (arr, queries)
    } else if mutation_kind == 3 {
        // set all elements to 1000000 (maximum value)
        let mut arr = a;
        let mut idx: usize = 0;
        while idx < arr.len()
            invariant
                arr.len() == a.len(),
                2 <= arr.len() <= 200000,
                0 <= idx <= arr.len(),
                forall|j: int| 0 <= j < arr.len() as int ==> 1 <= #[trigger] arr[j] <= 1000000,
            decreases arr.len() - idx,
        {
            arr.set(idx, 1000000i64);
            idx += 1;
        }
        (arr, queries)
    } else if mutation_kind == 4 {
        // ensure a[0] != a[1] (guarantees a found pair for queries spanning index 1)
        let mut arr = a;
        if arr[0] == arr[1] {
            if arr[0] == 1i64 {
                arr.set(0, 2i64);
            } else {
                arr.set(0, 1i64);
            }
        }
        (arr, queries)
    } else if mutation_kind == 5 && a[0] < 1000000 {
        // nudge first element up
        let val = a[0] + 1;
        let mut arr = a;
        arr.set(0, val);
        (arr, queries)
    } else if mutation_kind == 6 && a[0] > 1 {
        // nudge first element down
        let val = a[0] - 1;
        let mut arr = a;
        arr.set(0, val);
        (arr, queries)
    } else {
        // fallback: identity
        (a, queries)
    }
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
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
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

fn build_case(a: &[i64], queries: &[(usize, usize)]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s.push_str(&format!("{}\n", queries.len()));
    for &(l, r) in queries {
        s.push_str(&format!("{} {}\n", l, r));
    }
    s
}

fn build_input_multi(cases: &[(Vec<i64>, Vec<(usize, usize)>)]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (a, q) in cases {
        s.push_str(&build_case(a, q));
    }
    s
}

fn build_output_multi(answers: &[Vec<(i32, i32)>]) -> String {
    let mut s = String::new();
    for (i, ans) in answers.iter().enumerate() {
        for &(x, y) in ans {
            s.push_str(&format!("{} {}\n", x, y));
        }
        if i + 1 < answers.len() {
            s.push('\n');
        }
    }
    s
}

fn make_array(rng: &mut Rng, mode: usize, n: usize) -> Vec<i64> {
    let mut a: Vec<i64> = Vec::with_capacity(n);
    match mode {
        0 => {
            let v = rng.gen_range_i64(1, 1_000_000);
            for _ in 0..n { a.push(v); }
        }
        1 => {
            let v1 = rng.gen_range_i64(1, 500_000);
            let v2 = rng.gen_range_i64(500_001, 1_000_000);
            for i in 0..n { a.push(if i % 2 == 0 { v1 } else { v2 }); }
        }
        2 => {
            for _ in 0..n { a.push(rng.gen_range_i64(1, 3)); }
        }
        3 => {
            for _ in 0..n { a.push(rng.gen_range_i64(1, 1_000_000)); }
        }
        4 => {
            let v = rng.gen_range_i64(1, 999_999);
            for _ in 0..n { a.push(v); }
            let pos = rng.gen_range_usize(0, n - 1);
            a[pos] = v + 1;
        }
        _ => {
            for i in 0..n { a.push(1 + (i as i64 % 1_000_000)); }
        }
    }
    a
}

fn make_queries(rng: &mut Rng, n: usize, q: usize) -> Vec<(usize, usize)> {
    let mut qs: Vec<(usize, usize)> = Vec::with_capacity(q);
    for k in 0..q {
        let (l, r) = match k % 5 {
            0 => (1usize, n),
            1 => {
                let l = rng.gen_range_usize(1, n - 1);
                (l, l + 1)
            }
            2 => {
                let l = rng.gen_range_usize(1, n - 1);
                (l, n)
            }
            3 => {
                let r = rng.gen_range_usize(2, n);
                (1usize, r)
            }
            _ => {
                let l = rng.gen_range_usize(1, n - 1);
                let r = rng.gen_range_usize(l + 1, n);
                (l, r)
            }
        };
        qs.push((l, r));
    }
    qs
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    while count < target {
        let t: usize = if count < 5 { 1 }
                       else if count < 30 { rng.gen_range_usize(2, 5) }
                       else if count < 60 { rng.gen_range_usize(3, 10) }
                       else { rng.gen_range_usize(5, 20) };

        let mut cases: Vec<(Vec<i64>, Vec<(usize, usize)>)> = Vec::new();
        let mut answers: Vec<Vec<(i32, i32)>> = Vec::new();

        for _ in 0..t {
            let n: usize = match rng.next_u64() % 5 {
                0 => rng.gen_range_usize(2, 5),
                1 => rng.gen_range_usize(2, 10),
                2 => rng.gen_range_usize(11, 50),
                3 => rng.gen_range_usize(20, 200),
                _ => rng.gen_range_usize(50, 500),
            };
            let mode = (rng.next_u64() % 6) as usize;
            let a = make_array(&mut rng, mode, n);
            let max_q = 30.min(n);
            let q: usize = match rng.next_u64() % 4 {
                0 => 1,
                1 => rng.gen_range_usize(1, 5.min(max_q)),
                2 => rng.gen_range_usize(1, 15.min(max_q)),
                _ => rng.gen_range_usize(1, max_q),
            };
            let queries = make_queries(&mut rng, n, q);

            let key = format!("{:?}|{:?}", a, queries);
            if !seen.insert(key) { continue; }

            let ans = Solution::find_different_ones(a.clone(), queries.clone());
            cases.push((a, queries));
            answers.push(ans);
        }

        if cases.is_empty() { continue; }
        let inp = build_input_multi(&cases);
        let outp = build_output_multi(&answers);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

