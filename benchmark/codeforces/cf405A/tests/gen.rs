use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: Vec<i32>, mutation_kind: u8) -> (result: (Vec<i32>, usize))
    requires
        1 <= a.len() <= 100,
        forall|k: int| 0 <= k < a.len() ==> 1 <= #[trigger] a[k] <= 100,
    ensures
        1 <= result.1 <= 100,
        result.0.len() == result.1,
        forall|i: int| 0 <= i < result.1 as int ==> 1 <= #[trigger] result.0[i] as int <= 100,
{
    let n = a.len();
    if mutation_kind == 0 {
        // identity
        (a, n)
    } else if mutation_kind == 1 {
        // set last element to 1
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 1);
        (r, n)
    } else if mutation_kind == 2 {
        // set last element to 100
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, 100);
        (r, n)
    } else if mutation_kind == 3 && a[a.len() - 1] < 100 {
        // nudge last element up
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] + 1);
        (r, n)
    } else if mutation_kind == 4 && a[a.len() - 1] > 1 {
        // nudge last element down
        let mut r = a;
        let last = r.len() - 1;
        r.set(last, r[last] - 1);
        (r, n)
    } else if mutation_kind == 5 && a.len() < 100 {
        // grow by one element
        let mut r = a;
        r.push(1);
        let new_n = r.len();
        (r, new_n)
    } else if mutation_kind == 6 && a.len() > 1 {
        // shrink by one element
        let mut r = a;
        r.pop();
        let new_n = r.len();
        (r, new_n)
    } else if mutation_kind == 7 {
        // set all elements to 1
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == n,
                1 <= r.len() <= 100,
                forall|j: int| 0 <= j < i ==> r[j] == 1i32,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 1);
            i += 1;
        }
        (r, n)
    } else if mutation_kind == 8 {
        // set all elements to 100
        let mut r = a;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == n,
                1 <= r.len() <= 100,
                forall|j: int| 0 <= j < i ==> r[j] == 100i32,
                forall|j: int| i <= j < r.len() ==> r[j] == a[j],
            decreases r.len() - i,
        {
            r.set(i, 100);
            i += 1;
        }
        (r, n)
    } else if mutation_kind == 9 && a.len() >= 2 {
        // swap first and last elements
        let mut r = a;
        let last = r.len() - 1;
        let tmp = r[0];
        r.set(0, r[last]);
        r.set(last, tmp);
        (r, n)
    } else {
        // fallback: identity
        (a, n)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let r = (hi as i64 - lo as i64 + 1) as u64;
        (lo as i64 + (self.next_u64() % r) as i64) as i32
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

fn build_input(a: &[i32]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(res: &[i32]) -> String {
    let parts: Vec<String> = res.iter().map(|x| x.to_string()).collect();
    let mut s = parts.join(" ");
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

    let mut emit = |a: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        if a.is_empty() || a.len() > 100 { return; }
        for &x in &a { if !(1 <= x && x <= 100) { return; } }
        let key = format!("{:?}", a);
        if !seen.insert(key) { return; }
        let inp = build_input(&a);
        let n = a.len();
        let r = Solution::gravity_flip(a.clone(), n);
        let outs = build_output(&r);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        *count += 1;
    };

    emit(vec![3, 2, 1, 2], &mut seen, &mut out, &mut count);
    emit(vec![2, 3, 8], &mut seen, &mut out, &mut count);

    let seeds: Vec<Vec<i32>> = vec![
        vec![1], vec![100],
        vec![1, 1], vec![100, 100], vec![1, 100], vec![100, 1],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![100; 100], vec![1; 100],
        vec![1, 100, 1, 100, 1],
    ];
    for s in &seeds {
        emit(s.clone(), &mut seen, &mut out, &mut count);
    }

    let mut tries = 0usize;
    while count < target {
        tries += 1;
        if tries > 100000 { break; }
        let n = match tries % 5 {
            0 => 1,
            1 => rng.gen_range_usize(2, 5),
            2 => rng.gen_range_usize(5, 20),
            3 => rng.gen_range_usize(20, 50),
            _ => rng.gen_range_usize(50, 100),
        };
        let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
        emit(a, &mut seen, &mut out, &mut count);
    }
}

