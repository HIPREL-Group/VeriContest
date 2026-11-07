use vstd::prelude::*;

verus! {

/// Generate a valid test case for cf1714B (Remove Prefix).
/// Construction: takes a length `n` and a vector `vals` of raw values,
/// then clamps each value to [1, n] to satisfy the spec's requires.
pub fn generate_test_case(
    n: usize,
    vals: Vec<i32>,
    mutation_kind: u8,
) -> (result: (usize, Vec<i32>))
    requires
        n >= 1,
        (n as int) <= 200_000,
        vals.len() == n,
    ensures
        result.0 >= 1,
        (result.0 as int) <= 200_000,
        result.1.len() == result.0,
        forall|i: int|
            #![trigger result.1[i]]
            0 <= i && i < result.0 as int ==> 1 <= result.1[i] as int && result.1[i] as int <= result.0 as int,
{
    let eff_n: usize = if mutation_kind == 1 {
        // min size
        1usize
    } else if mutation_kind == 2 && n >= 2 {
        // shrink by one
        (n - 1) as usize
    } else if mutation_kind == 3 && n < 200_000 {
        // grow by one
        (n + 1) as usize
    } else {
        n
    };

    // Build the output array of length eff_n with values clamped to [1, eff_n]
    let mut a: Vec<i32> = Vec::new();
    let mut idx: usize = 0;

    while idx < eff_n
        invariant
            eff_n >= 1,
            (eff_n as int) <= 200_000,
            vals.len() == n,
            n >= 1,
            (n as int) <= 200_000,
            a.len() == idx,
            idx <= eff_n,
            forall|j: int|
                #![trigger a[j]]
                0 <= j && j < idx as int ==> 1 <= a[j] as int && a[j] as int <= eff_n as int,
        decreases eff_n - idx,
    {
        // Pick a raw value from vals (wrapping index if eff_n != n)
        let raw_idx = idx % n;
        let raw = vals[raw_idx];

        // Clamp to [1, eff_n]
        let eff_n_i32: i32 = eff_n as i32;
        let v: i32 = if raw < 1 {
            1i32
        } else if raw > eff_n_i32 {
            eff_n_i32
        } else {
            raw
        };

        a.push(v);
        idx += 1;
    }

    // Apply element-level mutations
    if mutation_kind == 4 && eff_n >= 1 {
        // Set first element to 1
        a.set(0, 1i32);
    } else if mutation_kind == 5 && eff_n >= 1 {
        // Set first element to eff_n (max value)
        a.set(0, eff_n as i32);
    } else if mutation_kind == 6 && eff_n >= 2 {
        // Set last element same as second-to-last (force a duplicate at end)
        let last_idx = eff_n - 1;
        let prev_val = a[last_idx - 1];
        a.set(last_idx, prev_val);
    } else if mutation_kind == 7 && eff_n >= 1 {
        // Set all elements to 1
        let mut k: usize = 0;
        while k < eff_n
            invariant
                eff_n >= 1,
                (eff_n as int) <= 200_000,
                a.len() == eff_n,
                k <= eff_n,
                forall|j: int|
                    #![trigger a[j]]
                    0 <= j && j < k as int ==> a[j] as int == 1,
                forall|j: int|
                    #![trigger a[j]]
                    k as int <= j && j < eff_n as int ==> 1 <= a[j] as int && a[j] as int <= eff_n as int,
            decreases eff_n - k,
        {
            a.set(k, 1i32);
            k += 1;
        }
    } else if mutation_kind == 8 && eff_n >= 2 {
        // Swap first two elements
        let tmp = a[0];
        let tmp2 = a[1];
        a.set(0, tmp2);
        a.set(1, tmp);
    }

    (eff_n, a)
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

type TC = Vec<i32>;

fn build_input(cases: &[TC]) -> String {
    let mut s = format!("{}\n", cases.len());
    for a in cases {
        s.push_str(&format!("{}\n", a.len()));
        let parts: Vec<String> = a.iter().map(|x| x.to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(cases: &[TC]) -> String {
    let mut s = String::new();
    for a in cases {
        let ans = Solution::min_prefix_removals(a.len(), a.clone());
        s.push_str(&format!("{}\n", ans));
    }
    s
}

fn random_a(rng: &mut Rng, n: usize) -> Vec<i32> {
    (0..n).map(|_| rng.gen_range_i32(1, n as i32)).collect()
}

fn main() {
    let target: usize = 100;
    let mut rng = Rng::new(1714);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    let examples: Vec<TC> = vec![
        // Note: 1 <= a_i <= n constraint
        vec![1, 1, 2, 3, 1, 4, 5, 6, 7, 8],  // n=10
        vec![3, 1, 4, 3],                      // n=4
        vec![1, 1, 1, 1],                      // n=4
        vec![1, 2, 3, 4, 5],                   // n=5
        vec![1],                               // n=1
        vec![2, 2],                            // n=2
        vec![1, 2, 1, 2, 1, 2],                // n=6
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
            let n = match rng.gen_range_usize(0, 4) {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(2, 30),
                2 => rng.gen_range_usize(50, 200),
                _ => rng.gen_range_usize(1, 100),
            };
            cases.push(random_a(&mut rng, n));
        }
        let inp = build_input(&cases);
        if !seen.insert(inp.clone()) { continue; }
        let outs = build_output(&cases);
        writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outs)).unwrap();
        count += 1;
    }
}

