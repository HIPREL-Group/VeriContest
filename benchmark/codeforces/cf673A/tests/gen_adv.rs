use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    t_vec: &Vec<i32>,
    i_param: usize,
    acc_param: i32,
) -> (result: (Vec<i32>, usize, i32))
    requires
        1 <= t_vec.len() <= 90,
        forall|k: int| 0 <= k < t_vec.len() ==> 1 <= #[trigger] t_vec[k] <= 90,
        forall|a: int, b: int| 0 <= a < b < t_vec.len() ==> #[trigger] t_vec[a] < #[trigger] t_vec[b],
        i_param <= t_vec.len() - 1,
    ensures
        ({
            let (t, i, acc) = result;
            &&& 1 <= t.len() <= 90
            &&& (forall|k: int| 0 <= k < t.len() ==> 1 <= #[trigger] t[k] <= 90)
            &&& (forall|a: int, b: int| 0 <= a < b < t.len() ==> #[trigger] t[a] < #[trigger] t[b])
            &&& i <= t.len() - 1
        }),
{
    let mut out: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < t_vec.len()
        invariant
            idx <= t_vec.len(),
            out.len() == idx,
            forall|k: int| 0 <= k < idx as int ==> #[trigger] out[k] == t_vec[k],
        decreases t_vec.len() - idx,
    {
        out.push(t_vec[idx]);
        idx += 1;
    }
    assert(out.len() == t_vec.len());
    assert(forall|k: int| 0 <= k < out.len() ==> #[trigger] out[k] == t_vec[k]);
    (out, i_param, acc_param)
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

fn build_input(t: &[i32]) -> String {
    let mut s = format!("{}\n", t.len());
    let parts: Vec<String> = t.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn make_random_strict(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut all: Vec<i32> = (1..=90).collect();
    let len = all.len();
    for i in 0..n.min(len) {
        let j = i + (rng.next_u64() as usize) % (len - i);
        all.swap(i, j);
    }
    let mut chosen: Vec<i32> = all.into_iter().take(n).collect();
    chosen.sort();
    chosen
}

fn main() {
    let target: usize = 200;
    let mut rng = Rng::new(67301);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |t: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if t.is_empty() || t.len() > 90 { return; }
        for w in t.windows(2) { if w[0] >= w[1] { return; } }
        for &v in &t { if v < 1 || v > 90 { return; } }
        let key = format!("{:?}", t);
        if !seen.insert(key) { return; }
        let inp = build_input(&t);
        let ans = Solution::watch_minutes(t.clone());
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // All single-element t in [1..90]
    for v in 1..=90i32 { emit(vec![v], &mut seen, &mut out, &mut count); }
    // [1..n] for various n
    for n in 1..=90usize {
        let v: Vec<i32> = (1..=n as i32).collect();
        emit(v, &mut seen, &mut out, &mut count);
    }
    // Boundary near 15-gap
    for s in 1..=90i32 {
        emit(vec![s], &mut seen, &mut out, &mut count);
        if count >= target { break; }
    }
    for shift in 0..16i32 {
        let v: Vec<i32> = (1..=90).filter(|x| (x - 1 - shift) % 16 == 0).collect();
        if !v.is_empty() { emit(v, &mut seen, &mut out, &mut count); }
    }

    while count < target {
        let n = rng.gen_range_usize(1, 90);
        let t = make_random_strict(&mut rng, n);
        emit(t, &mut seen, &mut out, &mut count);
    }
}

