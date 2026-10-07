use vstd::prelude::*;

verus! {

/// Build a strictly increasing Vec<i64> of length `n` starting at `base`
/// with consecutive differences given by `deltas`.
/// Also return p unchanged.
pub fn generate_test_case(
    base: i64,
    deltas: Vec<i64>,
    p: Vec<i64>,
    mutation_kind: u8,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        1 <= deltas.len() <= 299_999,
        1 <= base,
        forall|k: int| 0 <= k < deltas.len() ==> 1 <= #[trigger] deltas[k] <= 1_000_000,
        // base + sum of all deltas <= 10^18
        base as int + (deltas.len() as int) * 1_000_000 <= 1_000_000_000_000_000_000,
        1 <= p.len() <= 300_000,
        forall|k: int| 0 <= k < p.len() ==> 1 <= #[trigger] p[k] <= 1_000_000_000_000_000_000,
    ensures
        2 <= result.0.len() <= 300_000,
        1 <= result.1.len() <= 300_000,
        forall|k: int| 0 <= k < result.0.len() - 1 ==> #[trigger] result.0[k] < result.0[k + 1],
        forall|k: int| 0 <= k < result.0.len() ==> 1 <= #[trigger] result.0[k] <= 1_000_000_000_000_000_000,
        forall|k: int| 0 <= k < result.1.len() ==> 1 <= #[trigger] result.1[k] <= 1_000_000_000_000_000_000,
{
    let n = deltas.len() + 1;
    let mut x: Vec<i64> = Vec::new();
    x.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            x.len() == i + 1,
            n == deltas.len() + 1,
            2 <= n <= 300_000,
            1 <= base,
            base as int + (deltas.len() as int) * 1_000_000 <= 1_000_000_000_000_000_000,
            forall|k: int| 0 <= k < deltas.len() ==> 1 <= #[trigger] deltas[k] <= 1_000_000,
            forall|k: int| 0 <= k < x.len() ==> 1 <= #[trigger] x[k],
            forall|k: int| 0 <= k < x.len() ==> #[trigger] x[k] <= base as int + (i as int) * 1_000_000,
            forall|k: int| 0 <= k < x.len() - 1 ==> #[trigger] x[k] < x[k + 1],
            x[0] == base,
        decreases deltas.len() - i,
    {
        let prev = x[i];
        let d = deltas[i];
        let next = prev + d;

        assert(prev <= base as int + (i as int) * 1_000_000);
        assert(1 <= d <= 1_000_000);
        assert(next <= base as int + (i as int) * 1_000_000 + 1_000_000);
        assert(next <= base as int + ((i + 1) as int) * 1_000_000);

        x.push(next);

        i = i + 1;
    }

    // Apply mutations to p
    let out_p: Vec<i64>;
    if mutation_kind == 0 {
        // identity
        out_p = p;
    } else if mutation_kind == 1 && p.len() > 1 {
        // drop last element of p
        let mut pp = p;
        pp.pop();
        out_p = pp;
    } else if mutation_kind == 2 && p.len() < 300_000 {
        // duplicate first element of p
        let mut pp = p;
        let v = pp[0];
        pp.push(v);
        out_p = pp;
    } else if mutation_kind == 3 {
        // set first element to 1 (min boundary)
        let mut pp = p;
        pp.set(0, 1);
        out_p = pp;
    } else if mutation_kind == 4 {
        // set first element to max boundary
        let mut pp = p;
        pp.set(0, 1_000_000_000_000_000_000);
        out_p = pp;
    } else {
        out_p = p;
    }

    assert(x.len() == n);
    assert(n >= 2);
    assert(x.len() >= 2);

    (x, out_p)
}

} // verus!

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

fn gen_call(base: i64, deltas: Vec<i64>, p: Vec<i64>, mutation_kind: u8) -> (Vec<i64>, Vec<i64>) {
    generate_test_case(base, deltas, p, mutation_kind)
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1155);
    let target_count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |x: Vec<i64>, p: Vec<i64>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target_count {
            return;
        }
        let key = format!("{:?}|{:?}", x, p);
        if !seen.insert(key) {
            return;
        }
        let result = Solution::choose_alarm(x.clone(), p.clone());
        let output: serde_json::Value = if result.0 {
            json!({"found": true, "y": result.1, "j": result.2})
        } else {
            json!({"found": false, "y": 0, "j": 0})
        };
        writeln!(out, "{}", json!({"input": {"x": x, "p": p}, "output": output})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    emit(vec![3, 12, 18], vec![2, 6, 5, 3, 3], &mut seen, &mut out, &mut count);
    emit(vec![1, 5, 17, 19], vec![4, 5], &mut seen, &mut out, &mut count);
    emit(vec![1, 5, 17, 19], vec![2, 1], &mut seen, &mut out, &mut count);

    // Random test cases with diverse sizes and values
    for i in 0..500 {
        if count >= target_count {
            break;
        }

        // Size classes for x (number of deltas = n-1)
        let nd: usize = match i % 6 {
            0 => rng.gen_range_usize(1, 3),        // tiny (n=2..4)
            1 => rng.gen_range_usize(1, 9),         // small
            2 => rng.gen_range_usize(10, 50),       // medium
            3 => rng.gen_range_usize(51, 200),      // large
            4 => rng.gen_range_usize(201, 1000),    // very large
            _ => rng.gen_range_usize(1001, 5000),   // max-ish
        };

        // Delta magnitude classes
        let max_delta: i64 = match i % 5 {
            0 => 1,         // all diffs = 1 (consecutive)
            1 => 10,        // small diffs
            2 => 1000,      // medium diffs
            3 => 100_000,   // large diffs
            _ => 1_000_000, // max diffs
        };

        // Build deltas
        let mut deltas = Vec::with_capacity(nd);
        for _ in 0..nd {
            deltas.push(rng.gen_range_i64(1, max_delta));
        }

        // Choose base ensuring base + nd * 1_000_000 <= 10^18
        let max_base = 1_000_000_000_000_000_000i64 - (nd as i64) * 1_000_000;
        if max_base < 1 {
            continue;
        }
        let base = if i % 4 == 0 {
            1 // min boundary
        } else if i % 4 == 1 {
            max_base // max boundary
        } else {
            rng.gen_range_i64(1, max_base)
        };

        // Size classes for p
        let mp: usize = match i % 4 {
            0 => 1,
            1 => rng.gen_range_usize(1, 5),
            2 => rng.gen_range_usize(5, 50),
            _ => rng.gen_range_usize(50, 500),
        };

        let mut p = Vec::with_capacity(mp);
        for _ in 0..mp {
            p.push(rng.gen_range_i64(1, 1_000_000_000_000_000_000));
        }

        let mutation = (i % 5) as u8;
        let (x, pp) = gen_call(base, deltas, p, mutation);
        emit(x, pp, &mut seen, &mut out, &mut count);
    }

    eprintln!("Generated {} test cases", count);
}
