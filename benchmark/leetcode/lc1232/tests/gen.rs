use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<Vec<i32>>) -> (result: Vec<Vec<i32>>)
    ensures
        2 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> valid_pt(#[trigger] result[i]@),
        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i].len() == 2,
        forall|i: int| 0 <= i < result.len() ==> -10000 <= (#[trigger] result[i])[0] <= 10000 && -10000 <= result[i][1] <= 10000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i]@ != result[j]@,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant
            0 <= i <= end <= raw.len(), end <= 1000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> #[trigger] result[j].len() == 2,
            forall|j: int| 0 <= j < result.len() ==> -10000 <= #[trigger] result[j][0] <= 10000 && -10000 <= result[j][1] <= 10000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> (#[trigger] result[j][0] < #[trigger] result[k][0] || (#[trigger] result[j][0] == #[trigger] result[k][0] && #[trigger] result[j][1] < #[trigger] result[k][1])),
        decreases end - i,
    {
        let x = if raw[i].len() > 0 { raw[i][0] } else { -10000 };
        let y = if raw[i].len() > 1 { raw[i][1] } else { -10000 };
        let x = if x < -10000 { -10000 } else if x > 10000 { 10000 } else { x };
        let y = if y < -10000 { -10000 } else if y > 10000 { 10000 } else { y };
        let mut accept = true;
        if result.len() > 0 {
            let last = result.len() - 1;
            assert(result[last as int].len() == 2);
            accept = result[last][0] < x || (result[last][0] == x && result[last][1] < y);
        }
        if accept {
            assert forall|j: int| 0 <= j < result.len() implies
                (result[j][0] < x || (result[j][0] == x && result[j][1] < y)) by {
                if j < result.len() - 1 { assert((result[j][0] < result[result.len() - 1][0] || (result[j][0] == result[result.len() - 1][0] && result[j][1] < result[result.len() - 1][1]))); }
            }
            let mut p = Vec::new();
            p.push(x);
            p.push(y);
            result.push(p);
        }
        i += 1;
    }
    if result.len() < 2 {
        let mut fallback: Vec<Vec<i32>> = Vec::new();
        let mut p = Vec::new();
        p.push(-10000);
        p.push(-10000);
        fallback.push(p);
        let mut p = Vec::new();
        p.push(-10000);
        p.push(-9999);
        fallback.push(p);
        assert(fallback[0][1] != fallback[1][1]);
        assert(fallback[0]@ != fallback[1]@);
        fallback
    } else {
        assert forall|j: int| 0 <= j < result.len() implies valid_pt(#[trigger] result[j]@) by {
            assert(result[j].len() == 2);
            assert(-10000 <= result[j][0] <= 10000 && -10000 <= result[j][1] <= 10000);
        }
        assert forall|j: int, k: int| 0 <= j < k < result.len()
            implies result[j]@ != result[k]@ by {
            assert((result[j][0] < result[k][0] || (result[j][0] == result[k][0] && result[j][1] < result[k][1])));
        }
        result
    }
}


pub open spec fn valid_pt(p: Seq<i32>) -> bool {
    p.len() == 2 && -10000 <= p[0] && p[0] <= 10000 && -10000 <= p[1] && p[1] <= 10000
}

fn make_point(x: i32, y: i32) -> (pt: Vec<i32>)
    requires -10000 <= x <= 10000, -10000 <= y <= 10000,
    ensures valid_pt(pt@),
{
    let mut pt = Vec::new();
    pt.push(x);
    pt.push(y);
    pt
}

pub fn generate_candidate(coordinates: Vec<Vec<i32>>, mutation_kind: u8) -> (result: Vec<Vec<i32>>)
    requires
        2 <= coordinates.len() <= 1000,
        forall |i: int| #![trigger coordinates[i]] 0 <= i < coordinates.len() ==> valid_pt(coordinates[i]@),
    ensures
        2 <= result.len() <= 1000,
        forall |i: int| #![trigger result[i]] 0 <= i < result.len() ==> valid_pt(result[i]@),
{
    if mutation_kind == 0 {
        // identity
        coordinates
    } else if mutation_kind == 1 && coordinates.len() < 1000 {
        // grow: duplicate first point at end
        let mut c = coordinates;
        let x = c[0][0];
        let y = c[0][1];
        let pt = make_point(x, y);
        c.push(pt);
        c
    } else if mutation_kind == 2 && coordinates.len() > 2 {
        // shrink: remove last point
        let mut c = coordinates;
        c.pop();
        c
    } else if mutation_kind == 3 {
        // set first point to origin
        let mut c = coordinates;
        let pt = make_point(0i32, 0i32);
        c.set(0, pt);
        c
    } else if mutation_kind == 4 {
        // set last point to max boundary
        let mut c = coordinates;
        let last = c.len() - 1;
        let pt = make_point(10000i32, 10000i32);
        c.set(last, pt);
        c
    } else if mutation_kind == 5 {
        // set last point to min boundary
        let mut c = coordinates;
        let last = c.len() - 1;
        let pt = make_point(-10000i32, -10000i32);
        c.set(last, pt);
        c
    } else if mutation_kind == 6 {
        // negate first point
        let mut c = coordinates;
        let x = c[0][0];
        let y = c[0][1];
        let pt = make_point(-x, -y);
        c.set(0, pt);
        c
    } else if mutation_kind == 7 {
        // nudge first point x+1 if possible
        let mut c = coordinates;
        let x = c[0][0];
        let y = c[0][1];
        if x < 10000 {
            let pt = make_point(x + 1, y);
            c.set(0, pt);
        }
        c
    } else {
        coordinates
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
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

fn random_coordinates(rng: &mut Rng, n: usize) -> Vec<Vec<i32>> {
    let mut coords = Vec::new();
    for _ in 0..n {
        let x = rng.gen_range_i64(-10000, 10000) as i32;
        let y = rng.gen_range_i64(-10000, 10000) as i32;
        coords.push(vec![x, y]);
    }
    coords
}

fn collinear_coords(n: usize, base_x: i64, base_y: i64, dx: i64, dy: i64) -> Vec<Vec<i32>> {
    let mut coords = Vec::new();
    for i in 0..n {
        let x = (base_x + i as i64 * dx).max(-10000).min(10000) as i32;
        let y = (base_y + i as i64 * dy).max(-10000).min(10000) as i32;
        coords.push(vec![x, y]);
    }
    coords
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |coords: Vec<Vec<i32>>, seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        let mut coords = coords.clone();
        coords.sort();
        let coords = generate_test_case(coords);
        if *count >= target { return; }
        let key = format!("{:?}", coords);
        if !seen.insert(key) { return; }
        let output = Solution::check_straight_line(coords.clone());
        writeln!(out, "{}", json!({
            "input": {"coordinates": coords},
            "output": output
        })).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![1,2],vec![2,3],vec![3,4],vec![4,5],vec![5,6],vec![6,7]],
        vec![vec![1,1],vec![2,2],vec![3,4],vec![4,5],vec![5,6],vec![7,7]],
    ];
    for ex in examples {
        for mk in 0..=7u8 {
            let result = generate_candidate(ex.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Collinear seeds of various sizes and slopes
    let collinear_configs: Vec<(usize, i64, i64, i64, i64)> = vec![
        // (n, base_x, base_y, dx, dy)
        (2, 0, 0, 1, 1),            // minimal, diagonal
        (2, -10000, -10000, 20000, 20000), // minimal, boundary to boundary
        (3, 0, 0, 1, 0),            // horizontal
        (3, 0, 0, 0, 1),            // vertical
        (5, -5, 3, 2, 3),           // slope 3/2
        (10, 0, 0, 1, 1),           // diagonal
        (10, -10, 5, 3, -1),        // negative slope
        (50, 0, 0, 1, 0),           // long horizontal
        (100, -100, 0, 2, 1),       // medium
        (500, 0, 0, 1, 0),          // large horizontal
        (1000, 0, 0, 1, 0),         // max size horizontal
        (1000, -5000, -5000, 10, 10), // max size diagonal
    ];
    for (n, bx, by, dx, dy) in collinear_configs {
        let coords = collinear_coords(n, bx, by, dx, dy);
        for mk in 0..=7u8 {
            emit(generate_candidate(coords.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Non-collinear: collinear + one perturbed point
    for &n in &[3usize, 5, 10, 50, 100] {
        let mut coords = collinear_coords(n, 0, 0, 1, 1);
        let last = coords.len() - 1;
        coords[last][1] = (coords[last][1] as i64 + 1).min(10000) as i32;
        for mk in [0u8, 3, 4, 5, 7] {
            emit(generate_candidate(coords.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Two-point edge cases
    let two_pt_cases: Vec<Vec<Vec<i32>>> = vec![
        vec![vec![0, 0], vec![0, 0]],             // same point
        vec![vec![-10000, -10000], vec![10000, 10000]], // boundary diagonal
        vec![vec![-10000, 10000], vec![10000, -10000]], // boundary anti-diagonal
        vec![vec![0, 0], vec![10000, 0]],          // boundary horizontal
        vec![vec![0, 0], vec![0, 10000]],          // boundary vertical
    ];
    for tc in two_pt_cases {
        for mk in 0..=7u8 {
            emit(generate_candidate(tc.clone(), mk), &mut seen, &mut out, &mut count);
        }
    }

    // Random coordinates with mutations
    while count < target {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 500),
            _ => rng.gen_range_usize(501, 1000),
        };
        let coords = random_coordinates(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        emit(generate_candidate(coords, mk), &mut seen, &mut out, &mut count);
    }
}
