use vstd::prelude::*;

verus! {

pub open spec fn grid_has_one_at_spec(grid: Seq<i32>, r: int, c: int) -> bool {
    grid[5 * r + c] == 1
}

pub fn generate_test_case(r: usize, c: usize) -> (grid: Vec<i32>)
    requires
        r < 5,
        c < 5,
    ensures
        grid.len() == 25,
        forall|i: int| 0 <= i < 25 ==> (#[trigger] grid[i] == 0 || grid[i] == 1),
        grid[(5 * r + c) as int] == 1,
        forall|i: int| 0 <= i < 25 && i != 5 * r + c ==> #[trigger] grid[i] == 0,
        exists|rr: int, cc: int|
            0 <= rr < 5 && 0 <= cc < 5
            && grid_has_one_at_spec(grid@, rr, cc)
            && (forall|r2: int, c2: int|
                0 <= r2 < 5 && 0 <= c2 < 5 && #[trigger] grid_has_one_at_spec(grid@, r2, c2) ==> r2 == rr && c2 == cc),
{
    let target: usize = 5 * r + c;
    let mut grid: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < 25
        invariant
            target == 5 * r + c,
            r < 5,
            c < 5,
            target < 25,
            i <= 25,
            grid.len() == i,
            forall|k: int| 0 <= k < i as int && k == target as int ==> #[trigger] grid[k] == 1,
            forall|k: int| 0 <= k < i as int && k != target as int ==> #[trigger] grid[k] == 0,
        decreases 25 - i,
    {
        if i == target {
            grid.push(1);
        } else {
            grid.push(0);
        }
        i = i + 1;
    }

    proof {
        let rr = r as int;
        let cc = c as int;
        assert(grid[5 * rr + cc] == 1);
        assert(grid_has_one_at_spec(grid@, rr, cc));
        assert forall|r2: int, c2: int|
            0 <= r2 < 5 && 0 <= c2 < 5 && #[trigger] grid_has_one_at_spec(grid@, r2, c2)
            implies r2 == rr && c2 == cc
        by {
            let idx = 5 * r2 + c2;
            assert(0 <= idx < 25);
            assert(grid[idx] == 1);
            if idx != target as int {
                assert(grid[idx] == 0);
            }
            assert(idx == target as int);
            assert(5 * r2 + c2 == 5 * rr + cc);
        }
    }

    grid
}

}

use std::io::Write;
use std::collections::HashSet;

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

// Alternative formatting with multiple spaces
fn build_input_alt(grid: &[i32]) -> String {
    let mut s = String::new();
    for r in 0..5 {
        let parts: Vec<String> = (0..5).map(|c| grid[5*r+c].to_string()).collect();
        s.push_str(&parts.join("  ")); // double space
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
    let mut seen = HashSet::new();
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("adv_testcase.jsonl");
    let f = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(f);
    let mut count = 0usize;

    // 25 standard
    for r in 0..5 {
        for c in 0..5 {
            let g = make_grid(r, c);
            let inp = build_input(&g);
            if !seen.insert(inp.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // 25 with double-space
    for r in 0..5 {
        for c in 0..5 {
            let g = make_grid(r, c);
            let inp = build_input_alt(&g);
            if !seen.insert(inp.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // Trailing newline variant
    for r in 0..5 {
        for c in 0..5 {
            let g = make_grid(r, c);
            let mut inp = build_input(&g);
            inp.push('\n');
            if !seen.insert(inp.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g);
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&inp), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // Trailing spaces variant
    for r in 0..5 {
        for c in 0..5 {
            let g = make_grid(r, c);
            let mut s = String::new();
            for ri in 0..5 {
                let parts: Vec<String> = (0..5).map(|ci| g[5*ri+ci].to_string()).collect();
                s.push_str(&parts.join(" "));
                s.push(' '); // trailing space
                s.push('\n');
            }
            if !seen.insert(s.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g.clone());
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&s), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // with leading spaces
    for r in 0..5 {
        for c in 0..5 {
            let g = make_grid(r, c);
            let mut s = String::new();
            for ri in 0..5 {
                s.push(' ');
                let parts: Vec<String> = (0..5).map(|ci| g[5*ri+ci].to_string()).collect();
                s.push_str(&parts.join(" "));
                s.push('\n');
            }
            if !seen.insert(s.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g.clone());
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&s), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // tab separator
    for r in 0..5 {
        for c in 0..5 {
            let g = make_grid(r, c);
            let mut s = String::new();
            for ri in 0..5 {
                let parts: Vec<String> = (0..5).map(|ci| g[5*ri+ci].to_string()).collect();
                s.push_str(&parts.join("\t"));
                s.push('\n');
            }
            if !seen.insert(s.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g.clone());
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&s), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // CRLF line endings
    for r in 0..5 {
        for c in 0..5 {
            if count >= 200 { break; }
            let g = make_grid(r, c);
            let mut s = String::new();
            for ri in 0..5 {
                let parts: Vec<String> = (0..5).map(|ci| g[5*ri+ci].to_string()).collect();
                s.push_str(&parts.join(" "));
                s.push_str("\r\n");
            }
            if !seen.insert(s.clone()) { continue; }
            let ans = Solution::min_moves_beautiful_matrix(g.clone());
            let outp = build_output(ans);
            writeln!(out, "{{\"input\":{},\"output\":{}}}", fmt_json_str(&s), fmt_json_str(&outp)).unwrap();
            count += 1;
        }
    }

    // multiple newlines - skip, would break parsing perhaps. Skip.

    // Also add some "missing 1" matrices (all zeros) and some with multiple - no, problem says exactly one 1
    let _ = count;
}

