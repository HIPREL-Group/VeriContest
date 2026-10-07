use vstd::prelude::*;

verus! {

pub open spec fn grid_has_one_at(grid: Seq<i32>, r: int, c: int) -> bool
    recommends
        grid.len() == 25,
        0 <= r < 5,
        0 <= c < 5,
{
    grid[5 * r + c] == 1
}

pub open spec fn is_unique_one_position(grid: Seq<i32>, r: int, c: int) -> bool
    recommends
        grid.len() == 25,
{
    0 <= r < 5 && 0 <= c < 5
    && grid_has_one_at(grid, r, c)
    && (forall|r2: int, c2: int|
        0 <= r2 < 5 && 0 <= c2 < 5 && #[trigger] grid_has_one_at(grid, r2, c2) ==> r2 == r && c2 == c)
}

pub fn generate_test_case(
    pos_r: u8,
    pos_c: u8,
    mutation_kind: u8,
) -> (grid: Vec<i32>)
    requires
        0 <= pos_r < 5,
        0 <= pos_c < 5,
    ensures
        grid.len() == 25,
        forall|i: int| 0 <= i < 25 ==> (#[trigger] grid[i] == 0 || grid[i] == 1),
        exists|r: int, c: int| is_unique_one_position(grid@, r, c),
{
    let target_r: u8;
    let target_c: u8;

    if mutation_kind == 1 && pos_r < 4 {
        // nudge row up
        target_r = pos_r + 1;
        target_c = pos_c;
    } else if mutation_kind == 2 && pos_r > 0 {
        // nudge row down
        target_r = pos_r - 1;
        target_c = pos_c;
    } else if mutation_kind == 3 && pos_c < 4 {
        // nudge col right
        target_r = pos_r;
        target_c = pos_c + 1;
    } else if mutation_kind == 4 && pos_c > 0 {
        // nudge col left
        target_r = pos_r;
        target_c = pos_c - 1;
    } else if mutation_kind == 5 {
        // center
        target_r = 2;
        target_c = 2;
    } else if mutation_kind == 6 {
        // top-left corner
        target_r = 0;
        target_c = 0;
    } else if mutation_kind == 7 {
        // top-right corner
        target_r = 0;
        target_c = 4;
    } else if mutation_kind == 8 {
        // bottom-left corner
        target_r = 4;
        target_c = 0;
    } else if mutation_kind == 9 {
        // bottom-right corner
        target_r = 4;
        target_c = 4;
    } else {
        // identity
        target_r = pos_r;
        target_c = pos_c;
    }

    let one_pos: usize = 5 * (target_r as usize) + (target_c as usize);

    let mut grid: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < 25
        invariant
            0 <= i <= 25,
            grid.len() == i as int,
            0 <= one_pos < 25,
            0 <= target_r < 5,
            0 <= target_c < 5,
            one_pos == 5 * (target_r as usize) + (target_c as usize),
            forall|j: int| 0 <= j < i as int && j != one_pos as int ==> #[trigger] grid[j] == 0,
            forall|j: int| 0 <= j < i as int && j == one_pos as int ==> #[trigger] grid[j] == 1,
        decreases
            25 - i,
    {
        if i == one_pos {
            grid.push(1);
        } else {
            grid.push(0);
        }
        i += 1;
    }

    proof {
        // Prove all elements are 0 or 1
        assert(forall|j: int| 0 <= j < 25 ==> (#[trigger] grid[j] == 0 || grid[j] == 1));

        // Prove the 1 is at the target position
        assert(grid[one_pos as int] == 1);
        assert(grid[5 * (target_r as int) + (target_c as int)] == 1);
        assert(grid_has_one_at(grid@, target_r as int, target_c as int));

        // Prove uniqueness: any other position with a 1 must be (target_r, target_c)
        assert forall|r2: int, c2: int|
            0 <= r2 < 5 && 0 <= c2 < 5 && #[trigger] grid_has_one_at(grid@, r2, c2)
        implies r2 == target_r as int && c2 == target_c as int
        by {
            let idx2 = 5 * r2 + c2;
            assert(0 <= idx2 < 25);
            assert(grid[idx2] == 1);
            assert(idx2 == one_pos as int);
            // idx2 == 5 * target_r + target_c and idx2 == 5 * r2 + c2
            // Since 0 <= r2 < 5 and 0 <= c2 < 5, and 0 <= target_r < 5 and 0 <= target_c < 5,
            // 5 * r2 + c2 == 5 * target_r + target_c implies r2 == target_r and c2 == target_c
            assert(5 * r2 + c2 == 5 * (target_r as int) + (target_c as int));
            // Division/modulo argument
            assert(r2 == (5 * r2 + c2) / 5) by {
                assert(0 <= c2 < 5);
            }
            assert((target_r as int) == (5 * (target_r as int) + (target_c as int)) / 5) by {
                assert(0 <= (target_c as int) < 5);
            }
            assert(r2 == target_r as int);
            assert(c2 == target_c as int);
        }

        assert(is_unique_one_position(grid@, target_r as int, target_c as int));
    }

    grid
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

fn build_input(grid: &[i32]) -> String {
    let mut s = String::new();
    for r in 0..5 {
        let parts: Vec<String> = (0..5).map(|c| grid[5*r+c].to_string()).collect();
        s.push_str(&parts.join(" "));
        s.push('\n');
    }
    s
}

fn build_output(ans: i32) -> String {
    format!("{}\n", ans)
}

fn make_grid(r: usize, c: usize) -> Vec<i32> {
    let mut g = vec![0; 25];
    g[5*r+c] = 1;
    g
}

fn main() {
    let target: usize = 100;
    let _rng = Rng::new(263);
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // Generate all 25 possible positions
    for r in 0..5 {
        for c in 0..5 {
            if count >= target { break; }
            let g = make_grid(r, c);
            let inp = build_input(&g);
            if !seen.insert(inp.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // Add the same positions but maybe with different formatting? We have only 25 unique inputs.
    // To pad to 100, we generate alternative spacing. But the input is fixed format, so we can stop at 25.
    // Just keep what we have.
}

