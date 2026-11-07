use vstd::prelude::*;

verus! {

pub fn generate_test_case(s: Vec<i32>, mutation_kind: u8) -> (ret: (usize, Vec<i32>))
    requires
        1 <= s.len() <= 100000,
        forall|j: int| 0 <= j && j < s.len() ==> s[j] == 0 || s[j] == 1,
    ensures
        ret.0 == ret.1.len(),
        ret.0 > 0,
        ret.0 <= 100000,
        forall|j: int| 0 <= j && j < ret.0 ==> ret.1@[j] == 0 || ret.1@[j] == 1,
{
    let d: Vec<i32> = if mutation_kind == 0 {
        // identity
        s
    } else if mutation_kind == 1 {
        // set last element to 0
        let mut d = s;
        let last = d.len() - 1;
        d.set(last, 0);
        d
    } else if mutation_kind == 2 {
        // set last element to 1
        let mut d = s;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 3 {
        // set all elements to 0
        let mut d = s;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == s.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == s[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        d
    } else if mutation_kind == 4 {
        // set all elements to 1
        let mut d = s;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == s.len(),
                1 <= d.len() <= 100000,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == s[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 5 && s.len() < 100000 {
        // grow by one element (push 0)
        let mut d = s;
        d.push(0);
        d
    } else if mutation_kind == 6 && s.len() > 1 {
        // shrink by one element (pop)
        let mut d = s;
        d.pop();
        d
    } else if mutation_kind == 7 {
        // flip first element
        let mut d = s;
        if d[0] == 0 {
            d.set(0, 1);
        } else {
            d.set(0, 0);
        }
        d
    } else {
        // fallback: identity
        s
    };
    let n = d.len();
    (n, d)
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

fn build_input(s: &str) -> String { format!("{}\n{}\n", s.len(), s) }
fn build_output(ans: i32) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(935);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |s: String, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if s.is_empty() || s.len() > 100_000 { return; }
        for c in s.chars() { if c != 'U' && c != 'R' { return; } }
        if !seen.insert(s.clone()) { return; }
        let inp = build_input(&s);
        let moves: Vec<i32> = s.chars().map(|c| if c == 'R' { 1 } else { 0 }).collect();
        let ans = Solution::fafa_and_gates(s.len(), moves);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // Examples
    emit("U".into(), &mut seen, &mut out, &mut count);
    emit("RURUUR".into(), &mut seen, &mut out, &mut count);
    emit("URRRUUU".into(), &mut seen, &mut out, &mut count);

    // Edges
    emit("R".into(), &mut seen, &mut out, &mut count);
    emit("UR".into(), &mut seen, &mut out, &mut count);
    emit("RU".into(), &mut seen, &mut out, &mut count);
    emit("RRRR".into(), &mut seen, &mut out, &mut count);
    emit("UUUU".into(), &mut seen, &mut out, &mut count);
    emit("RURURURU".into(), &mut seen, &mut out, &mut count);
    emit("URURURUR".into(), &mut seen, &mut out, &mut count);
    emit("RRUU".into(), &mut seen, &mut out, &mut count);
    emit("UURR".into(), &mut seen, &mut out, &mut count);

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let p = match rng.gen_range_usize(0, 4) {
            0 => 2,
            1 => 4,
            2 => 5,
            _ => 7,
        };
        let s: String = (0..n).map(|_| if rng.gen_range_usize(0, 9) < p { 'R' } else { 'U' }).collect();
        emit(s, &mut seen, &mut out, &mut count);
    }
}

