use vstd::prelude::*;

verus! {

pub fn generate_test_case(queue: Vec<i32>, t: u32, mutation_kind: u8) -> (result: (Vec<i32>, u32))
    requires
        1 <= queue.len() <= 50,
        t <= 50,
        forall|i: int| 0 <= i < queue.len() ==> #[trigger] queue[i] == 0 || queue[i] == 1,
    ensures
        1 <= result.0.len() <= 50,
        result.1 <= 50,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] == 0 || result.0[i] == 1,
{
    if mutation_kind == 0 {
        // identity
        (queue, t)
    } else if mutation_kind == 1 {
        // set first element to 0
        let mut d = queue;
        d.set(0, 0);
        (d, t)
    } else if mutation_kind == 2 {
        // set first element to 1
        let mut d = queue;
        d.set(0, 1);
        (d, t)
    } else if mutation_kind == 3 && queue.len() >= 2 {
        // swap first two elements
        let mut d = queue;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        (d, t)
    } else if mutation_kind == 4 {
        // set all elements to 0
        let mut d = queue;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == queue.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 0,
                forall|j: int| i <= j < d.len() ==> d[j] == queue[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, t)
    } else if mutation_kind == 5 {
        // set all elements to 1
        let mut d = queue;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == queue.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 1,
                forall|j: int| i <= j < d.len() ==> d[j] == queue[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        (d, t)
    } else if mutation_kind == 6 && queue.len() < 50 {
        // grow by one element (push 0)
        let mut d = queue;
        d.push(0);
        (d, t)
    } else if mutation_kind == 7 && queue.len() > 1 {
        // shrink by one element (pop)
        let mut d = queue;
        d.pop();
        (d, t)
    } else if mutation_kind == 8 {
        // set t to 0
        (queue, 0u32)
    } else if mutation_kind == 9 {
        // set t to 50
        (queue, 50u32)
    } else {
        // fallback: identity
        (queue, t)
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

fn build_input(s: &str, t: u32) -> String {
    format!("{} {}\n{}\n", s.len(), t, s)
}

fn build_output(queue: &[i32]) -> String {
    let mut s = String::new();
    for &v in queue {
        s.push(if v == 1 { 'B' } else { 'G' });
    }
    s.push('\n');
    s
}

fn solve(s: &str, t: u32) -> Vec<i32> {
    let q: Vec<i32> = s.bytes().map(|b| if b == b'B' { 1 } else { 0 }).collect();
    Solution::queue_after_seconds(q, t)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(266);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<(&str, u32)> = vec![
        ("BGGBG", 1),
        ("BGGBG", 2),
        ("B", 1),
        ("G", 1),
        ("BG", 1),
        ("GB", 1),
    ];
    for (s, t) in &examples {
        if count >= target { break; }
        let inp = build_input(s, *t);
        if !seen.insert(inp.clone()) { continue; }
        let q = solve(s, *t);
        let outp = build_output(&q);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let chars = ['B', 'G'];
    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(10, 25),
            3 => rng.gen_range_usize(25, 40),
            _ => rng.gen_range_usize(40, 50),
        };
        let t = rng.gen_range_usize(1, 50) as u32;
        let s: String = (0..n).map(|_| chars[(rng.next_u64() as usize) % 2]).collect();
        let inp = build_input(&s, t);
        if !seen.insert(inp.clone()) { continue; }
        let q = solve(&s, t);
        let outp = build_output(&q);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}

