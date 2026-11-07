use vstd::prelude::*;

verus! {

fn unique_levels(raw: Vec<i32>, n: i32) -> (result: Vec<i32>)
    requires 1 <= n <= 100,
    ensures result.len() <= n,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= n,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > n as usize { n as usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant i <= end <= raw.len(), end <= n, 1 <= n <= 100, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= n,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > n { n } else { v };
        let mut j = 0usize;
        let mut found = false;
        while j < result.len()
            invariant j <= result.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] result[k] != v,
            decreases result.len() - j,
        {
            if result[j] == v { found = true; }
            j += 1;
        }
        if !found { result.push(v); }
        i += 1;
    }
    result
}
pub fn generate_test_case(n: i32, x: Vec<i32>, y: Vec<i32>) -> (result: (i32, Vec<i32>, Vec<i32>))
    ensures 1 <= result.0 <= 100,
        result.1.len() <= result.0, result.2.len() <= result.0,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0,
        forall|i: int| 0 <= i < result.2.len() ==> 1 <= #[trigger] result.2[i] <= result.0,
        forall|i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
        forall|i: int, j: int| 0 <= i < j < result.2.len() ==> result.2[i] != result.2[j],
{
    let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
    (n, unique_levels(x, n), unique_levels(y, n))
}


pub fn generate_candidate(
    n: i32,
    x_levels: Vec<i32>,
    y_levels: Vec<i32>,
) -> (res: (i32, Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100,
        forall|i: int| 0 <= i < x_levels.len() ==> 1 <= #[trigger] x_levels[i] && x_levels[i] <= n,
        forall|i: int| 0 <= i < y_levels.len() ==> 1 <= #[trigger] y_levels[i] && y_levels[i] <= n,
    ensures
        1 <= res.0 <= 100,
        forall|i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] && res.1[i] <= res.0,
        forall|i: int| 0 <= i < res.2.len() ==> 1 <= #[trigger] res.2[i] && res.2[i] <= res.0,
{
    (n, x_levels, y_levels)
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

fn build_input(n: i32, x: &[i32], y: &[i32]) -> String {
    let mut s = format!("{}\n", n);
    s.push_str(&format!("{}", x.len()));
    for &v in x { s.push_str(&format!(" {}", v)); }
    s.push('\n');
    s.push_str(&format!("{}", y.len()));
    for &v in y { s.push_str(&format!(" {}", v)); }
    s.push('\n');
    s
}

fn build_output(ans: bool) -> String {
    if ans {
        "I become the guy.\n".to_string()
    } else {
        "Oh, my keyboard!\n".to_string()
    }
}

fn main() {
    let target_count: usize = 200;
    let mut rng = Rng::new(46901);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen: HashSet<String> = HashSet::new();
    let mut count = 0usize;

    let mut emit = |n: i32, x: Vec<i32>, y: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count { return; }
        let key = format!("{}_{:?}_{:?}", n, x, y);
        if !seen.insert(key) { return; }
        let result = Solution::can_be_the_guy(n, x.clone(), y.clone());
        let (n, x, y) = generate_test_case(n, x, y);
        let inp = build_input(n, &x, &y);
        let outp = build_output(result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Adversarial: max n with various coverage scenarios
    emit(100, (1..=100).collect(), (1..=100).collect(), &mut seen, &mut out, &mut count);
    emit(100, (1..=99).collect(), (1..=99).collect(), &mut seen, &mut out, &mut count);
    emit(100, (1..=50).collect(), (51..=100).collect(), &mut seen, &mut out, &mut count);
    emit(100, vec![100], (1..=99).collect(), &mut seen, &mut out, &mut count);
    emit(100, vec![1], (2..=100).collect(), &mut seen, &mut out, &mut count);
    emit(100, vec![50], vec![50], &mut seen, &mut out, &mut count);
    emit(100, vec![], vec![], &mut seen, &mut out, &mut count);
    emit(100, (1..=100).filter(|i| i % 2 == 0).collect(), (1..=100).filter(|i| i % 2 == 1).collect(), &mut seen, &mut out, &mut count);
    emit(100, (1..=100).filter(|i| i % 2 == 0).collect(), (1..=100).filter(|i| i % 2 == 0).collect(), &mut seen, &mut out, &mut count);

    // Same with smaller n
    for n in [1i32, 2, 5, 10, 25, 50, 75, 100].iter() {
        let n = *n;
        emit(n, (1..=n).collect(), vec![], &mut seen, &mut out, &mut count);
        emit(n, vec![], (1..=n).collect(), &mut seen, &mut out, &mut count);
        if n > 1 {
            emit(n, vec![n], (1..=n-1).collect(), &mut seen, &mut out, &mut count);
            emit(n, (1..=n-1).collect(), vec![n], &mut seen, &mut out, &mut count);
        }
    }

    // Random with bias toward valid/invalid
    while count < target_count {
        let n = rng.gen_range_i64(1, 100) as i32;
        let p = rng.gen_range_usize(0, n as usize);
        let q = rng.gen_range_usize(0, n as usize);
        let mut x: Vec<i32> = Vec::new();
        for _ in 0..p {
            x.push(rng.gen_range_i64(1, n as i64) as i32);
        }
        let mut y: Vec<i32> = Vec::new();
        for _ in 0..q {
            y.push(rng.gen_range_i64(1, n as i64) as i32);
        }
        emit(n, x, y, &mut seen, &mut out, &mut count);
    }
}
