use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, k: i32, vals: Vec<i64>, mutation_kind: u8) -> (result: (usize, i32, Vec<i64>))
    requires
        1 <= n <= 2000,
        vals.len() == n,
        1 <= (k as int) <= 5,
        forall|i: int| 0 <= i < n as int ==> 0 <= (#[trigger] vals[i] as int) <= 5,
    ensures
        1 <= result.0 <= 2000,
        result.0 == result.2.len(),
        1 <= (result.1 as int) <= 5,
        forall|i: int|
            0 <= i < result.0 as int ==> 0 <= (#[trigger] result.2[i] as int) <= 5,
{
    if mutation_kind == 0 {
        // identity
        (n, k, vals)
    } else if mutation_kind == 1 {
        // set all elements to 0
        let mut y = vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 2000,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 0),
                forall|j: int| i <= j < n as int ==> 0 <= (#[trigger] y[j] as int) <= 5,
            decreases n - i,
        {
            y.set(i, 0i64);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) <= 5 by {}
        (n, k, y)
    } else if mutation_kind == 2 {
        // set all elements to 5
        let mut y = vals;
        let mut i: usize = 0;
        while i < n
            invariant
                1 <= n <= 2000,
                y.len() == n,
                0 <= i <= n,
                forall|j: int| 0 <= j < i ==> (#[trigger] y[j] == 5),
                forall|j: int| i <= j < n as int ==> 0 <= (#[trigger] y[j] as int) <= 5,
            decreases n - i,
        {
            y.set(i, 5i64);
            i += 1;
        }
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) <= 5 by {}
        (n, k, y)
    } else if mutation_kind == 3 && vals.len() >= 1 {
        // flip first element to 5 - val
        let mut y = vals;
        let old = y[0];
        let new_val = 5i64 - old;
        y.set(0, new_val);
        assert(0 <= new_val <= 5);
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) <= 5 by {
            assert(0 <= y[0] as int <= 5);
        }
        (n, k, y)
    } else if mutation_kind == 4 && vals.len() >= 1 {
        // flip last element to 5 - val
        let mut y = vals;
        let last = y.len() - 1;
        let old = y[last];
        let new_val = 5i64 - old;
        y.set(last, new_val);
        assert(0 <= new_val <= 5);
        assert forall|j: int| 0 <= j < y.len() implies 0 <= (#[trigger] y[j] as int) <= 5 by {}
        (n, k, y)
    } else if mutation_kind == 5 {
        // nudge k: set k to 1
        (n, 1i32, vals)
    } else if mutation_kind == 6 {
        // nudge k: set k to 5
        (n, 5i32, vals)
    } else {
        // fallback: identity
        (n, k, vals)
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

fn build_input(n: usize, k: i32, y: &[i64]) -> String {
    let mut s = format!("{} {}\n", n, k);
    let parts: Vec<String> = y.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: usize, k: i32, y: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| -> bool {
        if *count >= target { return false; }
        if !(1 <= n && n <= 2000 && 1 <= k && k <= 5 && y.len() == n) { return false; }
        for &v in &y { if !(0 <= v && v <= 5) { return false; } }
        let key = format!("{} {} {:?}", n, k, y);
        if !seen.insert(key) { return false; }
        let inp = build_input(n, k, &y);
        let ans = Solution::max_teams(n, k, y.clone());
        let outs = format!("{}\n", ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
        true
    };

    emit(5, 2, vec![0, 4, 5, 1, 0], &mut seen, &mut out, &mut count);
    emit(6, 4, vec![0, 1, 2, 3, 4, 5], &mut seen, &mut out, &mut count);
    emit(6, 5, vec![0, 0, 0, 0, 0, 0], &mut seen, &mut out, &mut count);

    'outer: for n_b in [1usize, 2, 3, 4, 6, 100, 1000, 2000].iter() {
        for k_b in 1..=5i32 {
            for fill_val in 0..=5i64 {
                let y = vec![fill_val; *n_b];
                emit(*n_b, k_b, y, &mut seen, &mut out, &mut count);
                if count >= target { break 'outer; }
            }
        }
    }

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let k = rng.gen_range_i64(1, 5) as i32;
        let y: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(0, 5)).collect();
        emit(n, k, y, &mut seen, &mut out, &mut count);
    }
}

