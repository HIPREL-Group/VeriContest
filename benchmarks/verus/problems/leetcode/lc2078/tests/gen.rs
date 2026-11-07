use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fill_val: i32,
    diff_val: i32,
    n: usize,
    diff_pos: usize,
    mutation_kind: u8,
) -> (colors: Vec<i32>)
    requires
        0 <= fill_val <= 100,
        0 <= diff_val <= 100,
        fill_val != diff_val,
        2 <= n <= 100,
        0 < diff_pos < n,
    ensures
        2 <= colors.len() <= 100,
        forall |i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 100,
        exists |i: int, j: int| 0 <= i < j < colors.len() && colors[i] != colors[j],
{
    let mut colors: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            colors.len() == k as int,
            0 <= k <= n,
            2 <= n <= 100,
            0 <= fill_val <= 100,
            forall |j: int| 0 <= j < k as int ==> #[trigger] colors[j] == fill_val,
        decreases n - k,
    {
        colors.push(fill_val);
        k = k + 1;
    }

    // Place diff_val at diff_pos to guarantee two different colors
    colors.set(diff_pos, diff_val);

    // Prove existence witness: colors[0] == fill_val, colors[diff_pos] == diff_val
    proof {
        assert(colors[0] == fill_val);
        assert(colors[diff_pos as int] == diff_val);
        assert(0int < diff_pos as int);
        assert(colors[0] != colors[diff_pos as int]);
    }

    if mutation_kind == 0 {
        // identity
        colors
    } else if mutation_kind == 1 && n < 100 {
        // grow: push fill_val
        colors.push(fill_val);
        proof {
            assert(colors[0] != colors[diff_pos as int]);
        }
        colors
    } else if mutation_kind == 2 && n > 2 && diff_pos < n - 1 {
        // shrink: pop last element (diff_pos preserved since diff_pos < n-1)
        colors.pop();
        proof {
            assert(colors[0] == fill_val);
            assert(colors[diff_pos as int] == diff_val);
            assert(colors[0] != colors[diff_pos as int]);
        }
        colors
    } else if mutation_kind == 3 {
        // set last element to diff_val
        colors.set(n - 1, diff_val);
        proof {
            assert(colors[0] == fill_val);
            assert(colors[diff_pos as int] == diff_val);
            assert(colors[0] != colors[diff_pos as int]);
        }
        colors
    } else if mutation_kind == 4 {
        // swap positions 0 and diff_pos
        let v0 = colors[0];
        let vd = colors[diff_pos];
        colors.set(0, vd);
        colors.set(diff_pos, v0);
        proof {
            assert(colors[0] == diff_val);
            assert(colors[diff_pos as int] == fill_val);
            assert(colors[0] != colors[diff_pos as int]);
        }
        colors
    } else if mutation_kind == 5 {
        // set position 1 to diff_val (more diff colors near start)
        colors.set(1usize, diff_val);
        proof {
            assert(colors[0] == fill_val);
            assert(colors[diff_pos as int] == diff_val);
            assert(colors[0] != colors[diff_pos as int]);
        }
        colors
    } else {
        // fallback: identity
        colors
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.0
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn gen(fill_val: i32, diff_val: i32, n: usize, diff_pos: usize, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(fill_val, diff_val, n, diff_pos, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(2078);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |colors: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}", colors);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_distance(colors.clone());
        writeln!(out, "{}", json!({"input": {"colors": colors}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from the problem description
    let examples: Vec<(i32, i32, usize, usize)> = vec![
        // (fill_val, diff_val, n, diff_pos) — approximations of example inputs
        // Example 1: [1,1,1,6,1,1,1] — fill=1, diff=6, n=7, diff_pos=3
        (1, 6, 7, 3),
        // Example 3: [0,1] — fill=0, diff=1, n=2, diff_pos=1
        (0, 1, 2, 1),
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    // Apply every mutation to example seeds
    for &(fv, dv, n, dp) in &examples {
        for &mk in &mutation_kinds {
            let colors = gen(fv, dv, n, dp, mk);
            emit(colors, &mut seen, &mut out, &mut count);
        }
    }

    // Interesting seed configurations
    let seeds: Vec<(i32, i32, usize, usize)> = vec![
        (0, 1, 2, 1),       // minimum size
        (0, 100, 2, 1),     // min size, max color diff
        (50, 51, 100, 99),  // max size, diff at end
        (0, 1, 100, 1),     // max size, diff near start
        (0, 1, 100, 50),    // max size, diff in middle
        (99, 0, 50, 25),    // mid size
        (100, 0, 3, 1),     // boundary colors
        (0, 100, 3, 2),     // boundary colors
        (1, 2, 10, 5),      // small array
        (42, 43, 20, 10),   // adjacent color values
    ];

    for &(fv, dv, n, dp) in &seeds {
        for &mk in &mutation_kinds {
            let colors = gen(fv, dv, n, dp, mk);
            emit(colors, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs across size classes
    while count < target_count {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),       // tiny
            1 => rng.gen_range_usize(2, 10),       // small
            2 => rng.gen_range_usize(11, 50),      // medium
            3 => rng.gen_range_usize(51, 100),     // large
            _ => rng.gen_range_usize(2, 100),      // any
        };

        let fill_val = if count % 5 == 0 {
            // boundary values ~20% of the time
            *[0i32, 100, 1, 50, 99].get(rng.gen_range_usize(0, 4)).unwrap()
        } else {
            rng.gen_range_i64(0, 100) as i32
        };

        let diff_val = {
            let mut d = rng.gen_range_i64(0, 100) as i32;
            if d == fill_val {
                d = if fill_val < 100 { fill_val + 1 } else { fill_val - 1 };
            }
            d
        };

        let diff_pos = rng.gen_range_usize(1, n - 1);
        let mk = rng.gen_range_usize(0, 5) as u8;

        let colors = gen(fill_val, diff_val, n, diff_pos, mk);
        emit(colors, &mut seen, &mut out, &mut count);
    }
}
