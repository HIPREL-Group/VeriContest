use vstd::prelude::*;

verus! {

pub open spec fn sum_group(seq: Seq<i64>, end: int, g: int) -> int
    recommends 0 <= g < 3, 0 <= end <= seq.len(),
    decreases end,
{
    if end <= 0 { 0 } else {
        let prev = end - 1;
        sum_group(seq, prev, g) + (if prev % 3 == g { seq[prev] as int } else { 0 })
    }
}
pub open spec fn unambiguous_workout(seq: Seq<i64>) -> bool {
    let s0 = sum_group(seq, seq.len() as int, 0);
    let s1 = sum_group(seq, seq.len() as int, 1);
    let s2 = sum_group(seq, seq.len() as int, 2);
    !((s0 >= s1 && s0 >= s2 && (s1 == s0 || s2 == s0))
        || (s1 >= s0 && s1 >= s2 && (s0 == s1 || s2 == s1))
        || (s2 >= s0 && s2 >= s1 && (s0 == s2 || s1 == s2)))
}
fn group_total(a: &Vec<i64>, group: usize) -> (result: i64)
    requires 1 <= a.len() <= 20, group < 3,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 25,
    ensures result == sum_group(a@, a.len() as int, group as int),
{
    let mut i = 0usize;
    let mut total = 0i64;
    while i < a.len()
        invariant i <= a.len() <= 20, group < 3, 0 <= total <= 25 * i,
            total == sum_group(a@, i as int, group as int),
            forall|j: int| 0 <= j < a.len() ==> 1 <= #[trigger] a[j] <= 25,
        decreases a.len() - i,
    {
        if i % 3 == group { total += a[i]; }
        i += 1;
    }
    total
}
fn unambiguous(a: &Vec<i64>) -> (valid: bool)
    requires 1 <= a.len() <= 20,
        forall|i: int| 0 <= i < a.len() ==> 1 <= #[trigger] a[i] <= 25,
    ensures valid == unambiguous_workout(a@),
{
    let x = group_total(a, 0);
    let y = group_total(a, 1);
    let z = group_total(a, 2);
    (x > y && x > z) || (y > x && y > z) || (z > x && z > y)
}
pub fn generate_test_case(raw: Vec<i64>) -> (result: Vec<i64>)
    ensures 1 <= result.len() <= 20,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 25,
        unambiguous_workout(result@),
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 20 { 20usize } else { raw.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 20, result.len() == i,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] result[j] <= 25,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 1 };
        result.push(if v < 1 { 1 } else if v > 25 { 25 } else { v });
        i += 1;
    }
    while result.len() > 1
        invariant 1 <= result.len() <= 20,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 25,
        decreases result.len(),
    {
        if unambiguous(&result) { return result; }
        result.pop();
    }
    reveal_with_fuel(sum_group, 2);
    result
}


pub fn generate_candidate(
    n: usize,
    seed_val: i64,
    mutation_kind: u8,
) -> (result: Vec<i64>)
    requires
        1 <= n <= 20,
        1 <= seed_val <= 25,
    ensures
        1 <= result.len() <= 20,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 25,
{
    if mutation_kind == 1 {
        // All elements = 1 (minimum)
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a[j] == 1i64,
            decreases n - i,
        {
            a.push(1i64);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 25 by {
                assert(a@[j] == 1i64);
            };
        }
        return a;
    }

    if mutation_kind == 2 {
        // All elements = 25 (maximum)
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> #[trigger] a[j] == 25i64,
            decreases n - i,
        {
            a.push(25i64);
            i += 1;
        }
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 25 by {
                assert(a@[j] == 25i64);
            };
        }
        return a;
    }

    if mutation_kind == 3 {
        // Single element
        let mut a: Vec<i64> = Vec::new();
        a.push(seed_val);
        proof {
            assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 25 by {
                assert(a@[j] == seed_val);
            };
        }
        return a;
    }

    if mutation_kind == 4 {
        // Alternating seed_val and 1
        let mut a: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                0 <= i <= n,
                1 <= n <= 20,
                1 <= seed_val <= 25,
                a.len() == i,
                forall|j: int| 0 <= j < i as int ==> 1 <= #[trigger] a[j] <= 25,
            decreases n - i,
        {
            if i % 2 == 0 {
                a.push(seed_val);
            } else {
                a.push(1i64);
            }
            i += 1;
        }
        return a;
    }

    // Default (mutation_kind == 0 or fallback): all same seed_val
    let mut a: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 20,
            1 <= seed_val <= 25,
            a.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] a[j] == seed_val,
        decreases n - i,
    {
        a.push(seed_val);
        i += 1;
    }
    proof {
        assert forall|j: int| 0 <= j < a@.len() implies 1 <= #[trigger] a@[j] <= 25 by {
            assert(a@[j] == seed_val);
        };
    }
    a
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

fn build_input(a: &[i64]) -> String {
    let mut s = format!("{}\n", a.len());
    let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
    s.push_str(&parts.join(" "));
    s.push('\n');
    s
}

fn build_output(chest: i64, biceps: i64, back: i64) -> String {
    if chest >= biceps && chest >= back {
        "chest\n".to_string()
    } else if biceps >= back {
        "biceps\n".to_string()
    } else {
        "back\n".to_string()
    }
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(255);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<Vec<i64>> = vec![
        vec![2, 8],
        vec![5, 1, 10],
        vec![3, 5, 4, 4, 1, 1],
    ];
    for ex in &examples {
        if count >= target { break; }
        let ex = generate_test_case(ex.clone());
        let inp = build_input(&ex);
        if !seen.insert(inp.clone()) { continue; }
        let (c, b, ba) = Solution::workout_sums(ex.clone());
        let outp = build_output(c, b, ba);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }

    let mut tries = 0;
    while count < target && tries < target * 100 {
        tries += 1;
        let n = rng.gen_range_usize(1, 20);
        let a: Vec<i64> = (0..n).map(|_| rng.gen_range_i64(1, 25)).collect();
        let a = generate_test_case(a);
        let inp = build_input(&a);
        if !seen.insert(inp.clone()) { continue; }
        let (c, b, ba) = Solution::workout_sums(a);
        let outp = build_output(c, b, ba);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
        count += 1;
    }
}
