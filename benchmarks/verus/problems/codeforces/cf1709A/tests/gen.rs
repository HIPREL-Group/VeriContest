use vstd::prelude::*;

verus! {

pub open spec fn count_value(v: int, x: int, a: int, b: int, c: int) -> int {
    (if x == v { 1int } else { 0 })
    + (if a == v { 1int } else { 0 })
    + (if b == v { 1int } else { 0 })
    + (if c == v { 1int } else { 0 })
}

/// Generates a valid (x, a, b, c) tuple satisfying the Three Doors constraints.
///
/// Construction parameters:
///   x_choice  — which key you hold (1, 2, or 3)
///   zero_pos  — which of a/b/c has no key behind it (0, 1, or 2)
///   swap      — order of the two remaining keys (0 or 1)
///   mutation_kind — selects hard-coded boundary cases (≥10 falls back to construction)
pub fn generate_test_case(
    x_choice: i32,
    zero_pos: u8,
    swap: u8,
    mutation_kind: u8,
) -> (result: (i32, i32, i32, i32))
    requires
        1 <= x_choice <= 3,
        zero_pos <= 2,
        swap <= 1,
    ensures
        1 <= result.0 <= 3,
        0 <= result.1 <= 3,
        0 <= result.2 <= 3,
        0 <= result.3 <= 3,
        count_value(1, result.0 as int, result.1 as int, result.2 as int, result.3 as int) == 1,
        count_value(2, result.0 as int, result.1 as int, result.2 as int, result.3 as int) == 1,
        count_value(3, result.0 as int, result.1 as int, result.2 as int, result.3 as int) == 1,
{
    // Hard-coded example / boundary mutations
    if mutation_kind == 0 {
        // Example 1 from problem: x=3, a=0, b=1, c=2
        (3i32, 0i32, 1i32, 2i32)
    } else if mutation_kind == 1 {
        // Example 2: x=1, a=0, b=3, c=2
        (1i32, 0i32, 3i32, 2i32)
    } else if mutation_kind == 2 {
        // Example 3: x=2, a=3, b=1, c=0
        (2i32, 3i32, 1i32, 0i32)
    } else if mutation_kind == 3 {
        // Example 4: x=2, a=1, b=3, c=0
        (2i32, 1i32, 3i32, 0i32)
    } else if mutation_kind == 4 {
        // x=1, zero at a, keys ordered
        (1i32, 0i32, 2i32, 3i32)
    } else if mutation_kind == 5 {
        // x=1, zero at b
        (1i32, 2i32, 0i32, 3i32)
    } else if mutation_kind == 6 {
        // x=1, zero at c
        (1i32, 3i32, 2i32, 0i32)
    } else if mutation_kind == 7 {
        // x=3, zero at a, keys swapped
        (3i32, 0i32, 2i32, 1i32)
    } else if mutation_kind == 8 {
        // x=3, zero at b
        (3i32, 1i32, 0i32, 2i32)
    } else if mutation_kind == 9 {
        // x=3, zero at c
        (3i32, 2i32, 1i32, 0i32)
    } else {
        // General construction from parameters
        let x = x_choice;

        // The two keys not held by the player
        let lo: i32 = if x == 1 { 2i32 } else { 1i32 };
        let hi: i32 = if x <= 2 { 3i32 } else { 2i32 };

        let first_key: i32 = if swap == 0 { lo } else { hi };
        let second_key: i32 = if swap == 0 { hi } else { lo };

        if zero_pos == 0 {
            (x, 0i32, first_key, second_key)
        } else if zero_pos == 1 {
            (x, first_key, 0i32, second_key)
        } else {
            (x, first_key, second_key, 0i32)
        }
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

// Each case: (x, a, b, c)
type TC = (i32, i32, i32, i32);

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for (x, a, b, c) in cases {
        s.push_str(&format!("{}\n{} {} {}\n", x, a, b, c));
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for (x, a, b, c) in cases {
        let ans = Solution::can_open_all_doors(*a, *b, *c, *x);
        s.push_str(if ans { "YES\n" } else { "NO\n" });
    }
    s
}

// Generates all valid cases: x in {1,2,3}, and {a,b,c} contains the other two values plus exactly one zero
fn enumerate_all() -> Vec<TC> {
    let mut out = Vec::new();
    for x in 1..=3 {
        // Two values to place in three slots, with one slot = 0
        let others: Vec<i32> = (1..=3i32).filter(|&v| v != x).collect();
        // Place 0 in slot zero_pos, the other two values in the remaining slots in some order
        for zero_pos in 0..3 {
            let remaining: Vec<usize> = (0..3).filter(|&i| i != zero_pos).collect();
            // Two perms of the two values
            for perm in 0..2 {
                let mut slots = [0i32; 3];
                slots[zero_pos] = 0;
                if perm == 0 {
                    slots[remaining[0]] = others[0];
                    slots[remaining[1]] = others[1];
                } else {
                    slots[remaining[0]] = others[1];
                    slots[remaining[1]] = others[0];
                }
                out.push((x, slots[0], slots[1], slots[2]));
            }
        }
    }
    out
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1709);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let all_cases = enumerate_all();

    // First, single-test entries for each unique configuration
    for ex in &all_cases {
        if count >= target { break; }
        let cases = vec![ex.clone()];
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }

    // Then bundle multiple cases
    while count < target {
        // t can be 1 to 18 per problem constraints
        let t: usize = rng.gen_range_usize(2, 18);
        let mut cases: Vec<TC> = Vec::new();
        for _ in 0..t {
            let idx = rng.gen_range_usize(0, all_cases.len() - 1);
            cases.push(all_cases[idx]);
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

