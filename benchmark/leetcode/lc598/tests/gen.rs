use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    a_vals: Vec<i32>,
    b_vals: Vec<i32>,
    mutation_kind: u8,
) -> (ops: Vec<Vec<i32>>)
    requires
        m >= 1,
        n >= 1,
        m <= 40000,
        n <= 40000,
        a_vals.len() == b_vals.len(),
        0 <= a_vals.len() <= 10_000,
        forall|i: int| 0 <= i < a_vals.len() ==> 1 <= #[trigger] a_vals[i] <= m,
        forall|i: int| 0 <= i < b_vals.len() ==> 1 <= #[trigger] b_vals[i] <= n,
    ensures
        m >= 1,
        n >= 1,
        m <= 40000,
        n <= 40000,
        0 <= ops@.len() <= 10_000,
        forall|i: int| 0 <= i < ops@.len() ==> (#[trigger] ops@[i]).len() == 2,
        forall|i: int| 0 <= i < ops@.len() ==>
            1 <= ops@[i]@[0] && ops@[i]@[0] <= m &&
            1 <= ops@[i]@[1] && ops@[i]@[1] <= n,
{
    if mutation_kind == 4 {
        // Empty ops mutation
        let empty: Vec<Vec<i32>> = Vec::new();
        return empty;
    }

    let mut ops: Vec<Vec<i32>> = Vec::new();
    let mut i: usize = 0;
    while i < a_vals.len()
        invariant
            0 <= i <= a_vals.len(),
            a_vals.len() == b_vals.len(),
            a_vals.len() <= 10_000,
            ops@.len() == i as int,
            m >= 1,
            n >= 1,
            m <= 40000,
            n <= 40000,
            forall|j: int| 0 <= j < ops@.len() ==> (#[trigger] ops@[j]).len() == 2,
            forall|j: int| 0 <= j < ops@.len() ==>
                1 <= ops@[j]@[0] && ops@[j]@[0] <= m &&
                1 <= ops@[j]@[1] && ops@[j]@[1] <= n,
            forall|k: int| 0 <= k < a_vals.len() ==> 1 <= #[trigger] a_vals[k] <= m,
            forall|k: int| 0 <= k < b_vals.len() ==> 1 <= #[trigger] b_vals[k] <= n,
        decreases a_vals.len() - i,
    {
        let mut op: Vec<i32> = Vec::new();
        op.push(a_vals[i]);
        op.push(b_vals[i]);
        ops.push(op);
        i += 1;
    }

    if mutation_kind == 1 && ops.len() < 10_000 {
        // Grow: add op (1, 1) — minimum range
        let mut op: Vec<i32> = Vec::new();
        op.push(1i32);
        op.push(1i32);
        ops.push(op);
    } else if mutation_kind == 2 && ops.len() > 0 {
        // Shrink: remove last op
        ops.pop();
    } else if mutation_kind == 3 && ops.len() < 10_000 {
        // Grow: add op (m, n) — full matrix range
        let mut op: Vec<i32> = Vec::new();
        op.push(m);
        op.push(n);
        ops.push(op);
    }
    // mutation_kind 0 or fallback: identity

    ops
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

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |m: i32, n: i32, ops: &Vec<Vec<i32>>,
                    seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>,
                    emitted: &mut usize| {
        if *emitted >= count {
            return;
        }
        let key = format!("{},{},{:?}", m, n, ops);
        if !seen.insert(key) {
            return;
        }
        let output = Solution::max_count(m, n, ops.clone());
        writeln!(out, "{}", json!({
            "input": {"m": m, "n": n, "ops": ops},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example test cases from description.md
    emit(3, 3, &vec![vec![2, 2], vec![3, 3]], &mut seen, &mut out, &mut emitted);
    emit(3, 3, &vec![vec![2,2],vec![3,3],vec![3,3],vec![3,3],vec![2,2],vec![3,3],vec![3,3],vec![3,3],vec![2,2],vec![3,3],vec![3,3],vec![3,3]], &mut seen, &mut out, &mut emitted);
    emit(3, 3, &vec![], &mut seen, &mut out, &mut emitted);

    // Boundary cases
    emit(1, 1, &vec![], &mut seen, &mut out, &mut emitted);
    emit(1, 1, &vec![vec![1, 1]], &mut seen, &mut out, &mut emitted);
    emit(40000, 40000, &vec![], &mut seen, &mut out, &mut emitted);
    emit(40000, 40000, &vec![vec![1, 1]], &mut seen, &mut out, &mut emitted);
    emit(40000, 40000, &vec![vec![40000, 40000]], &mut seen, &mut out, &mut emitted);

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4];

    // Generate random test cases with mutations
    while emitted < count {
        // Size class for m, n
        let m: i32 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(1, 5) as i32,        // tiny
            1 => rng.gen_range_i64(1, 100) as i32,      // small
            2 => rng.gen_range_i64(100, 1000) as i32,   // medium
            3 => rng.gen_range_i64(1000, 10000) as i32,  // large
            _ => rng.gen_range_i64(10000, 40000) as i32, // max
        };
        let n: i32 = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_i64(1, 5) as i32,
            1 => rng.gen_range_i64(1, 100) as i32,
            2 => rng.gen_range_i64(100, 1000) as i32,
            3 => rng.gen_range_i64(1000, 10000) as i32,
            _ => rng.gen_range_i64(10000, 40000) as i32,
        };

        // Size class for ops length
        let ops_len: usize = match rng.gen_range_usize(0, 4) {
            0 => 0,                                       // empty
            1 => rng.gen_range_usize(1, 5),               // tiny
            2 => rng.gen_range_usize(1, 50),              // small
            3 => rng.gen_range_usize(50, 500),            // medium
            _ => rng.gen_range_usize(500, 10_000.min(count * 10)), // large
        };

        let mut a_vals: Vec<i32> = Vec::with_capacity(ops_len);
        let mut b_vals: Vec<i32> = Vec::with_capacity(ops_len);
        for _ in 0..ops_len {
            a_vals.push(rng.gen_range_i64(1, m as i64) as i32);
            b_vals.push(rng.gen_range_i64(1, n as i64) as i32);
        }

        let mk = mutation_kinds[rng.gen_range_usize(0, mutation_kinds.len() - 1)];
        let ops = generate_test_case(m, n, a_vals, b_vals, mk);
        emit(m, n, &ops, &mut seen, &mut out, &mut emitted);
    }
}
