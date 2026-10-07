use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    tops: Vec<i32>,
    bottoms: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        2 <= tops.len() <= 20000,
        bottoms.len() == tops.len(),
        forall|i: int| 0 <= i < tops.len() ==> 1 <= #[trigger] tops[i] <= 6,
        forall|i: int| 0 <= i < bottoms.len() ==> 1 <= #[trigger] bottoms[i] <= 6,
    ensures
        2 <= result.0.len() <= 20000,
        result.1.len() == result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 6,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 6,
{
    if mutation_kind == 0 {
        // identity
        (tops, bottoms)
    } else if mutation_kind == 1 {
        // swap tops and bottoms
        (bottoms, tops)
    } else if mutation_kind == 2 {
        // swap tops[0] and bottoms[0]
        let mut t = tops;
        let mut b = bottoms;
        let tv = t[0];
        let bv = b[0];
        t.set(0, bv);
        b.set(0, tv);
        (t, b)
    } else if mutation_kind == 3 {
        // set tops[0] = bottoms[0]
        let mut t = tops;
        let v = bottoms[0];
        t.set(0, v);
        (t, bottoms)
    } else if mutation_kind == 4 {
        // set bottoms[0] = tops[0]
        let mut b = bottoms;
        let v = tops[0];
        b.set(0, v);
        (tops, b)
    } else if mutation_kind == 5 {
        // nudge tops[0] up within [1,6]
        let mut t = tops;
        if t[0] < 6 {
            t.set(0, t[0] + 1);
        } else {
            t.set(0, 1);
        }
        (t, bottoms)
    } else if mutation_kind == 6 {
        // nudge bottoms[0] up within [1,6]
        let mut b = bottoms;
        if b[0] < 6 {
            b.set(0, b[0] + 1);
        } else {
            b.set(0, 1);
        }
        (tops, b)
    } else if mutation_kind == 7 {
        // set tops[last] = bottoms[last]
        let mut t = tops;
        let last = t.len() - 1;
        let v = bottoms[last];
        t.set(last, v);
        (t, bottoms)
    } else {
        // fallback: identity
        (tops, bottoms)
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

fn random_domino_row(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut row = Vec::with_capacity(len);
    for _ in 0..len {
        row.push(rng.gen_range_i64(1, 6) as i32);
    }
    row
}

/// Build tops/bottoms where value `v` appears in every position (in top or bottom).
/// This guarantees a solution exists.
fn solvable_pair(rng: &mut Rng, len: usize, v: i32) -> (Vec<i32>, Vec<i32>) {
    let mut tops = Vec::with_capacity(len);
    let mut bottoms = Vec::with_capacity(len);
    for _ in 0..len {
        let r = rng.gen_range_usize(0, 2);
        if r == 0 {
            // v on top, random on bottom
            tops.push(v);
            bottoms.push(rng.gen_range_i64(1, 6) as i32);
        } else if r == 1 {
            // random on top, v on bottom
            tops.push(rng.gen_range_i64(1, 6) as i32);
            bottoms.push(v);
        } else {
            // v on both
            tops.push(v);
            bottoms.push(v);
        }
    }
    (tops, bottoms)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1007);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |tops: Vec<i32>, bottoms: Vec<i32>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}|{:?}", tops, bottoms);
        if !seen.insert(key) { return; }
        let result = Solution::min_domino_rotations(tops.clone(), bottoms.clone());
        writeln!(out, "{}", json!({
            "input": {"tops": tops, "bottoms": bottoms},
            "output": result
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![2,1,2,4,2,2], vec![5,2,6,2,3,2]),
        (vec![3,5,1,2,3], vec![3,6,3,3,4]),
    ];
    for (t, b) in examples {
        let (rt, rb) = generate_test_case(t, b, 0);
        emit(rt, rb, &mut seen, &mut out, &mut emitted);
    }

    // Edge cases: length 2
    let small_cases: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![1,1], vec![1,1]),       // all same
        (vec![1,2], vec![2,1]),       // swappable
        (vec![1,2], vec![3,4]),       // no solution
        (vec![6,6], vec![6,6]),       // all 6s
        (vec![1,6], vec![6,1]),       // swapped pair
    ];
    for (t, b) in small_cases {
        for mk in 0..=7u8 {
            if emitted >= count { break; }
            let (rt, rb) = generate_test_case(t.clone(), b.clone(), mk);
            emit(rt, rb, &mut seen, &mut out, &mut emitted);
        }
    }

    // Solvable cases: all positions have value v in top or bottom
    let size_classes: Vec<usize> = vec![2, 3, 5, 10, 50, 100, 500, 1000, 5000, 10000];
    for &n in &size_classes {
        if emitted >= count { break; }
        let v = rng.gen_range_i64(1, 6) as i32;
        let (t, b) = solvable_pair(&mut rng, n, v);
        for mk in 0..=3u8 {
            if emitted >= count { break; }
            let (rt, rb) = generate_test_case(t.clone(), b.clone(), mk);
            emit(rt, rb, &mut seen, &mut out, &mut emitted);
        }
    }

    // Uniform rows (0 rotations needed)
    for v in 1..=6i32 {
        if emitted >= count { break; }
        let n = rng.gen_range_usize(2, 20);
        let tops: Vec<i32> = vec![v; n];
        let bottoms: Vec<i32> = (0..n).map(|_| rng.gen_range_i64(1, 6) as i32).collect();
        let (rt, rb) = generate_test_case(tops, bottoms, 0);
        emit(rt, rb, &mut seen, &mut out, &mut emitted);
    }

    // Random cases (likely unsolvable for larger sizes)
    while emitted < count {
        let n = match emitted % 5 {
            0 => rng.gen_range_usize(2, 5),
            1 => rng.gen_range_usize(2, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let mk = (rng.next_u64() % 8) as u8;
        // Mix solvable and random
        if emitted % 3 == 0 {
            let v = rng.gen_range_i64(1, 6) as i32;
            let (t, b) = solvable_pair(&mut rng, n, v);
            let (rt, rb) = generate_test_case(t, b, mk);
            emit(rt, rb, &mut seen, &mut out, &mut emitted);
        } else {
            let t = random_domino_row(&mut rng, n);
            let b = random_domino_row(&mut rng, n);
            let (rt, rb) = generate_test_case(t, b, mk);
            emit(rt, rb, &mut seen, &mut out, &mut emitted);
        }
    }
}
