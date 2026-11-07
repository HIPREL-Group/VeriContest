use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_left: Vec<u8>,
    raw_right: Vec<u8>,
    mutation_kind: u8,
) -> (result: (Vec<u8>, Vec<u8>, usize))
    requires
        2 <= raw_left.len() <= 10000,
        raw_right.len() == raw_left.len(),
        forall|i: int| 0 <= i < raw_left.len() ==> #[trigger] raw_left[i] <= 1u8,
        forall|i: int| 0 <= i < raw_right.len() ==> #[trigger] raw_right[i] <= 1u8,
    ensures
        2 <= result.2 <= 10000,
        result.0.len() == result.2,
        result.1.len() == result.2,
        forall|i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] <= 1u8,
        forall|i: int| 0 <= i < result.1.len() ==> #[trigger] result.1[i] <= 1u8,
{
    let n = raw_left.len();
    if mutation_kind == 0 {
        (raw_left, raw_right, n)
    } else if mutation_kind == 1 {
        let mut l = raw_left;
        let mut i: usize = 0;
        while i < l.len()
            invariant
                0 <= i <= l.len(),
                l.len() == n,
                2 <= n <= 10000,
                forall|j: int| 0 <= j < i ==> l[j] == 0u8,
                forall|j: int| i <= j < l.len() ==> #[trigger] l[j] <= 1u8,
            decreases l.len() - i,
        {
            l.set(i, 0u8);
            i += 1;
        }
        (l, raw_right, n)
    } else if mutation_kind == 2 {
        let mut r = raw_right;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == n,
                2 <= n <= 10000,
                forall|j: int| 0 <= j < i ==> r[j] == 1u8,
                forall|j: int| i <= j < r.len() ==> #[trigger] r[j] <= 1u8,
            decreases r.len() - i,
        {
            r.set(i, 1u8);
            i += 1;
        }
        (raw_left, r, n)
    } else if mutation_kind == 3 {
        let mut l = raw_left;
        let mut r = raw_right;
        let mut i: usize = 0;
        while i < l.len()
            invariant
                0 <= i <= l.len(),
                l.len() == n,
                r.len() == n,
                2 <= n <= 10000,
                forall|j: int| 0 <= j < i ==> l[j] == 1u8,
                forall|j: int| 0 <= j < i ==> r[j] == 0u8,
                forall|j: int| i <= j < l.len() ==> #[trigger] l[j] <= 1u8,
                forall|j: int| i <= j < r.len() ==> #[trigger] r[j] <= 1u8,
            decreases l.len() - i,
        {
            l.set(i, 1u8);
            r.set(i, 0u8);
            i += 1;
        }
        (l, r, n)
    } else if mutation_kind == 4 && raw_left.len() > 2 {
        let mut l = raw_left;
        let mut r = raw_right;
        l.pop();
        r.pop();
        let new_n = l.len();
        (l, r, new_n)
    } else {
        (raw_left, raw_right, n)
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

fn build_input(left: &Vec<u8>, right: &Vec<u8>) -> String {
    let n = left.len();
    let mut s = format!("{}\n", n);
    for i in 0..n {
        s.push_str(&format!("{} {}\n", left[i], right[i]));
    }
    s
}

fn build_output(ans: usize) -> String {
    format!("{}\n", ans)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(248);
    let mut seen: HashSet<String> = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let mut emit = |left: Vec<u8>, right: Vec<u8>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target { return; }
        let n = left.len();
        if n < 2 || n > 10000 { return; }
        let inp = build_input(&left, &right);
        if !seen.insert(inp.clone()) { return; }
        let ans = Solution::min_seconds(left.clone(), right.clone(), n);
        let outp = build_output(ans);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        *count += 1;
    };

    // Sample test
    emit(vec![0u8, 1, 0, 1, 0], vec![1u8, 0, 1, 1, 1], &mut seen, &mut out, &mut count);

    // Boundaries
    for n in [2usize, 3, 4, 5, 10] {
        emit(vec![0u8; n], vec![0u8; n], &mut seen, &mut out, &mut count);
        emit(vec![1u8; n], vec![1u8; n], &mut seen, &mut out, &mut count);
        emit(vec![0u8; n], vec![1u8; n], &mut seen, &mut out, &mut count);
        emit(vec![1u8; n], vec![0u8; n], &mut seen, &mut out, &mut count);
    }

    // Random tests
    let mut tries = 0usize;
    while count < target && tries < target * 200 {
        tries += 1;
        let n = match tries % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 100),
            3 => rng.gen_range_usize(100, 1000),
            _ => rng.gen_range_usize(1000, 10000),
        };
        let left: Vec<u8> = (0..n).map(|_| (rng.next_u64() % 2) as u8).collect();
        let right: Vec<u8> = (0..n).map(|_| (rng.next_u64() % 2) as u8).collect();
        emit(left, right, &mut seen, &mut out, &mut count);
    }
}
