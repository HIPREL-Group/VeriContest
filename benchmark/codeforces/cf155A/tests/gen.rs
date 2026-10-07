use vstd::prelude::*;

verus! {

pub fn generate_test_case(points: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, usize))
    requires
        1 <= points.len() <= 1000,
        forall|i: int| 0 <= i < points.len() as int ==> 0 <= #[trigger] points[i] as int <= 10000,
    ensures
        1 <= result.1 <= 1000,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.0.len() as int ==> 0 <= #[trigger] result.0[i] as int <= 10000,
{
    if mutation_kind == 0 {
        // identity
        let n = points.len();
        (points, n)
    } else if mutation_kind == 1 {
        // set last element to 0 (boundary low)
        let mut p = points;
        let last = p.len() - 1;
        p.set(last, 0);
        let n = p.len();
        (p, n)
    } else if mutation_kind == 2 {
        // set last element to 10000 (boundary high)
        let mut p = points;
        let last = p.len() - 1;
        p.set(last, 10000);
        let n = p.len();
        (p, n)
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut p = points;
        p.set(0, 0);
        let n = p.len();
        (p, n)
    } else if mutation_kind == 4 {
        // set first element to 10000
        let mut p = points;
        p.set(0, 10000);
        let n = p.len();
        (p, n)
    } else if mutation_kind == 5 && points.len() < 1000 {
        // grow by one element (push 0)
        let mut p = points;
        p.push(0);
        let n = p.len();
        (p, n)
    } else if mutation_kind == 6 && points.len() > 1 {
        // shrink by one element (pop)
        let mut p = points;
        p.pop();
        let n = p.len();
        (p, n)
    } else if mutation_kind == 7 {
        // nudge last element up (if < 10000)
        let mut p = points;
        let last = p.len() - 1;
        if p[last] < 10000 {
            p.set(last, p[last] + 1);
        }
        let n = p.len();
        (p, n)
    } else if mutation_kind == 8 {
        // nudge last element down (if > 0)
        let mut p = points;
        let last = p.len() - 1;
        if p[last] > 0 {
            p.set(last, p[last] - 1);
        }
        let n = p.len();
        (p, n)
    } else if mutation_kind == 9 {
        // set all elements to 0
        let mut p = points;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == points.len(),
                1 <= p.len() <= 1000,
                forall|j: int| 0 <= j < i ==> p[j] == 0i32,
                forall|j: int| i <= j < p.len() as int ==> p[j] == points[j],
            decreases p.len() - i,
        {
            p.set(i, 0);
            i += 1;
        }
        let n = p.len();
        (p, n)
    } else if mutation_kind == 10 {
        // set all elements to 10000
        let mut p = points;
        let mut i: usize = 0;
        while i < p.len()
            invariant
                0 <= i <= p.len(),
                p.len() == points.len(),
                1 <= p.len() <= 1000,
                forall|j: int| 0 <= j < i ==> p[j] == 10000i32,
                forall|j: int| i <= j < p.len() as int ==> p[j] == points[j],
            decreases p.len() - i,
        {
            p.set(i, 10000);
            i += 1;
        }
        let n = p.len();
        (p, n)
    } else {
        // fallback: identity
        let n = points.len();
        (points, n)
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

fn mutate(points: Vec<i32>, mutation_kind: u8) -> (Vec<i32>, usize) {
    if mutation_kind == 0 {
        let n = points.len(); (points, n)
    } else if mutation_kind == 1 {
        let mut p = points; let last = p.len() - 1; p[last] = 0;
        let n = p.len(); (p, n)
    } else if mutation_kind == 2 {
        let mut p = points; let last = p.len() - 1; p[last] = 10000;
        let n = p.len(); (p, n)
    } else if mutation_kind == 3 {
        let mut p = points; p[0] = 0;
        let n = p.len(); (p, n)
    } else if mutation_kind == 4 {
        let mut p = points; p[0] = 10000;
        let n = p.len(); (p, n)
    } else if mutation_kind == 5 && points.len() < 1000 {
        let mut p = points; p.push(0);
        let n = p.len(); (p, n)
    } else if mutation_kind == 6 && points.len() > 1 {
        let mut p = points; p.pop();
        let n = p.len(); (p, n)
    } else if mutation_kind == 7 {
        let mut p = points; let last = p.len() - 1;
        if p[last] < 10000 { p[last] = p[last] + 1; }
        let n = p.len(); (p, n)
    } else if mutation_kind == 8 {
        let mut p = points; let last = p.len() - 1;
        if p[last] > 0 { p[last] = p[last] - 1; }
        let n = p.len(); (p, n)
    } else if mutation_kind == 9 {
        let n = points.len(); (vec![0; n], n)
    } else if mutation_kind == 10 {
        let n = points.len(); (vec![10000; n], n)
    } else {
        let n = points.len(); (points, n)
    }
}

fn make_points(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut pts = Vec::new();
    for _ in 0..n {
        pts.push(rng.gen_range_i64(0, 10000) as i32);
    }
    pts
}

fn build_input(n: usize, points: &[i32]) -> String {
    let mut s = format!("{}\n", n);
    let parts: Vec<String> = points.iter().map(|v| v.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(ans: usize) -> String { format!("{}\n", ans) }

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(42);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;
    let mut seen: HashSet<String> = HashSet::new();

    let mut emit = |pts: Vec<i32>, n: usize, count: &mut usize, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>| {
        if *count >= target { return; }
        let inp = build_input(n, &pts);
        if !seen.insert(inp.clone()) { return; }
        let ans = Solution::count_amazing_performances(pts.clone(), n);
        let outs = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    // examples
    let p1 = vec![100, 50, 200, 150, 200];
    emit(p1.clone(), p1.len(), &mut count, &mut seen, &mut out);
    let p2 = vec![4664, 6496, 5814, 7010, 5762, 5736, 6944, 4850, 3698, 7242];
    emit(p2.clone(), p2.len(), &mut count, &mut seen, &mut out);

    let num_mutations: u8 = 11;
    let mut generated: usize = 0;
    while count < target {
        let n: usize = match generated % 5 {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let points = make_points(&mut rng, n);
        let mk = (generated % num_mutations as usize) as u8;
        let (pts, n_out) = mutate(points, mk);
        emit(pts, n_out, &mut count, &mut seen, &mut out);
        generated += 1;
    }
}

