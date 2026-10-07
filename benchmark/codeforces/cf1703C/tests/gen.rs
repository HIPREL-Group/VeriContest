use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fd: i32,
    n: usize,
    bits: u16,
    mutation_kind: u8,
) -> (result: (i32, Vec<i32>))
    requires
        0 <= fd <= 9,
        n <= 10,
    ensures
        0 <= result.0 <= 9,
        result.1.len() <= 10,
        forall|j: int|
            0 <= j < result.1.len() ==> #[trigger] result.1[j] == 1 || result.1[j] == -1,
{
    if mutation_kind == 1 {
        // All moves are U (1)
        let mut deltas: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n <= 10,
                deltas.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] deltas[j] == 1i32,
            decreases n - i,
        {
            deltas.push(1i32);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < deltas.len() implies
                #[trigger] deltas[j] == 1 || deltas[j] == -1
            by {
                assert(deltas[j] == 1i32);
            }
        }
        return (fd, deltas);
    }

    if mutation_kind == 2 {
        // All moves are D (-1)
        let mut deltas: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                n <= 10,
                deltas.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] deltas[j] == -1i32,
            decreases n - i,
        {
            deltas.push(-1i32);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < deltas.len() implies
                #[trigger] deltas[j] == 1 || deltas[j] == -1
            by {
                assert(deltas[j] == -1i32);
            }
        }
        return (fd, deltas);
    }

    if mutation_kind == 3 {
        // Empty moves
        let deltas: Vec<i32> = Vec::new();
        return (fd, deltas);
    }

    if mutation_kind == 4 {
        // fd = 0
        let mut deltas: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut b = bits;
        while i < n
            invariant
                0 <= i <= n,
                n <= 10,
                deltas.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] deltas[j] == 1i32 || deltas[j] == -1i32,
            decreases n - i,
        {
            if b % 2 == 0 {
                deltas.push(1i32);
            } else {
                deltas.push(-1i32);
            }
            b = b / 2;
            i += 1;
        }
        return (0i32, deltas);
    }

    if mutation_kind == 5 {
        // fd = 9
        let mut deltas: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        let mut b = bits;
        while i < n
            invariant
                0 <= i <= n,
                n <= 10,
                deltas.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] deltas[j] == 1i32 || deltas[j] == -1i32,
            decreases n - i,
        {
            if b % 2 == 0 {
                deltas.push(1i32);
            } else {
                deltas.push(-1i32);
            }
            b = b / 2;
            i += 1;
        }
        return (9i32, deltas);
    }

    // Default: build deltas from bits
    let mut deltas: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let mut b = bits;
    while i < n
        invariant
            0 <= i <= n,
            n <= 10,
            deltas.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] deltas[j] == 1i32 || deltas[j] == -1i32,
        decreases n - i,
    {
        if b % 2 == 0 {
            deltas.push(1i32);
        } else {
            deltas.push(-1i32);
        }
        b = b / 2;
        i += 1;
    }
    (fd, deltas)
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

// Each test case: n, vec a (len n), vec moves_str (len n) — moves_str[i] is "BBUDU" string of length b_i
type TC = (usize, Vec<i32>, Vec<String>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, a, moves) in cases {
        s.push_str(&format!("{}\n", n));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
        for m in moves {
            s.push_str(&format!("{} {}\n", m.len(), m));
        }
    }
    s
}

fn build_output_for_case(n: usize, a: &[i32], moves: &[String]) -> String {
    let mut parts: Vec<String> = Vec::with_capacity(n);
    for i in 0..n {
        let mvs: Vec<i32> = moves[i].as_bytes().iter().map(|&b| if b == b'U' { 1i32 } else { -1i32 }).collect();
        let init = Solution::recover_digit(a[i], mvs);
        parts.push(init.to_string());
    }
    let mut s = parts.join(" ");
    s.push('\n');
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (n, a, moves) in cases {
        s.push_str(&build_output_for_case(*n, a, moves));
    }
    s
}

fn random_case(rng: &mut Rng, max_n: usize) -> TC {
    let n = rng.gen_range_usize(1, max_n);
    let a: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(0, 9)).collect();
    let moves: Vec<String> = (0..n).map(|_| {
        let len = rng.gen_range_usize(1, 10);
        let mut s = String::with_capacity(len);
        for _ in 0..len {
            if rng.next_u64() % 2 == 0 { s.push('U'); } else { s.push('D'); }
        }
        s
    }).collect();
    (n, a, moves)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1703);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Examples
    let examples: Vec<TC> = vec![
        (3, vec![1, 2, 3], vec!["DDD".to_string(), "UU".to_string(), "DD".to_string()]),
        (1, vec![0], vec!["U".to_string()]),
        (1, vec![5], vec!["DDDDDDDDDD".to_string()]),
        (2, vec![0, 9], vec!["U".to_string(), "D".to_string()]),
        (5, vec![1, 2, 3, 4, 5], vec!["U".to_string(), "UU".to_string(), "DDD".to_string(), "UUUU".to_string(), "DDDDD".to_string()]),
    ];

    for ex in &examples {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    while count < target {
        let t: usize = if count < 20 { rng.gen_range_usize(1, 3) } else { rng.gen_range_usize(2, 20) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            cases.push(random_case(&mut rng, 30));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

