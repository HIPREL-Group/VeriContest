use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_events: Vec<i32>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i32>))
    requires
        1 <= raw_events.len() <= 100000,
        forall|i: int| 0 <= i < raw_events.len() ==> #[trigger] raw_events[i] as int == -1 || (1 <= raw_events[i] as int <= 10),
    ensures
        1 <= result.0 <= 100000,
        result.1.len() == result.0,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] as int == -1 || (1 <= result.1[i] as int <= 10),
{
    let n = raw_events.len();
    if mutation_kind == 0 {
        (n, raw_events)
    } else if mutation_kind == 1 {
        // all crimes
        let mut e = raw_events;
        let mut i: usize = 0;
        while i < e.len()
            invariant
                0 <= i <= e.len(),
                e.len() == n,
                1 <= n <= 100000,
                forall|j: int| 0 <= j < i ==> e[j] == -1i32,
                forall|j: int| i <= j < e.len() ==> #[trigger] e[j] as int == -1 || (1 <= e[j] as int <= 10),
            decreases e.len() - i,
        {
            e.set(i, -1i32);
            i += 1;
        }
        (n, e)
    } else if mutation_kind == 2 {
        // all hires of 10
        let mut e = raw_events;
        let mut i: usize = 0;
        while i < e.len()
            invariant
                0 <= i <= e.len(),
                e.len() == n,
                1 <= n <= 100000,
                forall|j: int| 0 <= j < i ==> e[j] == 10i32,
                forall|j: int| i <= j < e.len() ==> #[trigger] e[j] as int == -1 || (1 <= e[j] as int <= 10),
            decreases e.len() - i,
        {
            e.set(i, 10i32);
            i += 1;
        }
        (n, e)
    } else if mutation_kind == 3 && raw_events.len() > 1 {
        let mut e = raw_events;
        e.pop();
        let new_n = e.len();
        (new_n, e)
    } else {
        (n, raw_events)
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

fn build_input(n: usize, events: &[i32]) -> String {
    let parts: Vec<String> = events.iter().map(|x| x.to_string()).collect();
    format!("{}\n{}\n", n, parts.join(" "))
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(427);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |n: usize, events: &Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if n < 1 || n > 100000 || events.len() != n { return; }
        let inp = build_input(n, events);
        if !seen.insert(inp.clone()) { return; }
        let result = Solution::count_untreated(n, events.clone());
        let outp = format!("{}\n", result);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // examples
    emit(3, &vec![-1, -1, 1], &mut seen, &mut out, &mut count);
    emit(8, &vec![1, -1, 1, -1, -1, 1, 1, 1], &mut seen, &mut out, &mut count);
    emit(11, &vec![-1, -1, 2, -1, -1, -1, -1, -1, -1, -1, -1], &mut seen, &mut out, &mut count);

    // small variations
    for ev in &[
        vec![-1i32], vec![1], vec![10], vec![-1, 1], vec![1, -1],
        vec![-1, -1], vec![5, 5], vec![1, 1, 1, -1], vec![-1, -1, -1, 5],
    ] {
        emit(ev.len(), ev, &mut seen, &mut out, &mut count);
    }

    while count < target {
        let n = rng.gen_range_usize(1, 200);
        let events: Vec<i32> = (0..n).map(|_| {
            let r = rng.next_u64() % 11;
            if r == 0 { -1 } else { r as i32 }
        }).collect();
        emit(n, &events, &mut seen, &mut out, &mut count);
    }
}
