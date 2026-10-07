use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elems: Vec<i32>,
    seed_c: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= elems.len() <= 100,
        forall|i: int| 0 <= i < elems.len() ==> 1 <= #[trigger] elems[i] <= 100,
        1 <= seed_c <= 100,
    ensures
        1 <= result.0.len() <= 100,
        1 <= result.1 <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0@[i] <= 100,
{
    if mutation_kind == 0 {
        // identity
        (elems, seed_c)
    } else if mutation_kind == 1 && elems.len() < 100 {
        // grow: append element with value 1
        let mut d = elems;
        d.push(1);
        (d, seed_c)
    } else if mutation_kind == 2 && elems.len() > 1 {
        // shrink: remove last element
        let mut d = elems;
        d.pop();
        (d, seed_c)
    } else if mutation_kind == 3 {
        // set first element to 1 (min boundary)
        let mut d = elems;
        d.set(0, 1);
        (d, seed_c)
    } else if mutation_kind == 4 {
        // set first element to 100 (max boundary)
        let mut d = elems;
        d.set(0, 100);
        (d, seed_c)
    } else if mutation_kind == 5 {
        // set last element to 1
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 1);
        (d, seed_c)
    } else if mutation_kind == 6 {
        // set last element to 100
        let mut d = elems;
        let last = d.len() - 1;
        d.set(last, 100);
        (d, seed_c)
    } else if mutation_kind == 7 {
        // set c to 1
        (elems, 1)
    } else if mutation_kind == 8 {
        // set c to 100
        (elems, 100)
    } else if mutation_kind == 9 && seed_c < 100 {
        // nudge c up
        (elems, seed_c + 1)
    } else if mutation_kind == 10 && seed_c > 1 {
        // nudge c down
        (elems, seed_c - 1)
    } else if mutation_kind == 11 {
        // set all elements to 1 (all distinct orbits minimal)
        let len = elems.len();
        let mut d: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < len
            invariant
                0 <= j <= len,
                d.len() == j,
                1 <= len <= 100,
                forall|k: int| 0 <= k < j as int ==> #[trigger] d@[k] == 1i32,
            decreases len - j,
        {
            d.push(1);
            j += 1;
        }
        (d, seed_c)
    } else if mutation_kind == 12 {
        // set all elements to 100 (all same orbit, maximal)
        let len = elems.len();
        let mut d: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < len
            invariant
                0 <= j <= len,
                d.len() == j,
                1 <= len <= 100,
                forall|k: int| 0 <= k < j as int ==> #[trigger] d@[k] == 100i32,
            decreases len - j,
        {
            d.push(100);
            j += 1;
        }
        (d, seed_c)
    } else if mutation_kind == 13 && elems.len() >= 2 {
        // swap first two elements
        let mut d = elems;
        let a = d[0];
        let b = d[1];
        d.set(0, b);
        d.set(1, a);
        (d, seed_c)
    } else if mutation_kind == 14 {
        // nudge first element up if < 100
        let mut d = elems;
        if d[0] < 100 {
            d.set(0, d[0] + 1);
        }
        (d, seed_c)
    } else if mutation_kind == 15 {
        // nudge first element down if > 1
        let mut d = elems;
        if d[0] > 1 {
            d.set(0, d[0] - 1);
        }
        (d, seed_c)
    } else {
        // fallback: identity
        (elems, seed_c)
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

// (n, c, orbits)
type TC = (usize, i32, Vec<i32>);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (n, c, orbits) in cases {
        s.push_str(&format!("{} {}\n", n, c));
        let parts: Vec<String> = orbits.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (_n, c, orbits) in cases {
        let ans = Solution::min_destroy_cost(orbits.clone(), *c);
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_case(rng: &mut Rng, max_n: usize) -> TC {
    let n = rng.gen_range_usize(1, max_n);
    let c = rng.gen_range_i32(1, 100);
    let orbits: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
    (n, c, orbits)
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1730);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        (4, 2, vec![1, 2, 3, 1]),
        (5, 1, vec![1, 1, 1, 1, 1]),
        (3, 100, vec![1, 1, 1]),
        (1, 1, vec![1]),
        (5, 5, vec![1, 1, 1, 1, 1]),
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
        let t: usize = if count < 20 { rng.gen_range_usize(1, 5) } else { rng.gen_range_usize(2, 30) };
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            cases.push(random_case(&mut rng, 100));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

