use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_param: i32,
    quantities: Vec<i32>,
    mutation_kind: u8,
) -> (result: (i32, Vec<i32>))
    requires
        1 <= quantities.len() <= n_param <= 100000,
        forall |i: int| 0 <= i < quantities.len() ==> 1 <= #[trigger] quantities[i] <= 100000,
    ensures
        1 <= result.1.len() <= result.0 <= 100000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100000,
{
    if mutation_kind == 0 {
        // identity
        (n_param, quantities)
    } else if mutation_kind == 1 && n_param < 100000 {
        // increase n by 1 (more stores available)
        (n_param + 1, quantities)
    } else if mutation_kind == 2 {
        // tightest n: set n = m (number of product types)
        let m = quantities.len() as i32;
        (m, quantities)
    } else if mutation_kind == 3 {
        // set all quantities to 1 (minimum)
        let mut q = quantities;
        let mut i: usize = 0;
        while i < q.len()
            invariant
                0 <= i <= q.len(),
                q.len() == quantities.len(),
                1 <= q.len() <= n_param <= 100000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] q[j] == 1i32,
                forall|j: int| i as int <= j < q.len() ==> q[j] == quantities[j],
            decreases q.len() - i,
        {
            q.set(i, 1);
            i += 1;
        }
        (n_param, q)
    } else if mutation_kind == 4 {
        // set all quantities to 100000 (maximum)
        let mut q = quantities;
        let mut i: usize = 0;
        while i < q.len()
            invariant
                0 <= i <= q.len(),
                q.len() == quantities.len(),
                1 <= q.len() <= n_param <= 100000,
                forall|j: int| 0 <= j < i as int ==> #[trigger] q[j] == 100000i32,
                forall|j: int| i as int <= j < q.len() ==> q[j] == quantities[j],
            decreases q.len() - i,
        {
            q.set(i, 100000);
            i += 1;
        }
        (n_param, q)
    } else if mutation_kind == 5 {
        // nudge first quantity up
        let mut q = quantities;
        if q[0] < 100000 {
            q.set(0, q[0] + 1);
        }
        (n_param, q)
    } else if mutation_kind == 6 {
        // nudge first quantity down
        let mut q = quantities;
        if q[0] > 1 {
            q.set(0, q[0] - 1);
        }
        (n_param, q)
    } else if mutation_kind == 7 {
        // grow: add one more product type with quantity 1
        let m_i32 = quantities.len() as i32;
        if m_i32 < n_param {
            let mut q = quantities;
            q.push(1);
            (n_param, q)
        } else {
            (n_param, quantities)
        }
    } else if mutation_kind == 8 && quantities.len() > 1 {
        // shrink: remove last product type
        let mut q = quantities;
        q.pop();
        (n_param, q)
    } else if mutation_kind == 9 {
        // set n to maximum (100000)
        (100000i32, quantities)
    } else {
        // fallback: identity
        (n_param, quantities)
    }
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

extern crate serde_json;
use serde_json::json;

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut emitted = 0usize;

    macro_rules! emit {
        ($n:expr, $quantities:expr, $mk:expr) => {
            if emitted < count {
                let n_val: i32 = $n;
                let q_val: Vec<i32> = $quantities;
                let mk_val: u8 = $mk;
                let (n_out, q_out) = generate_test_case(n_val, q_val, mk_val);
                let result = Solution::minimized_maximum(n_out, q_out.clone());
                writeln!(out, "{}", json!({
                    "input": {"n": n_out, "quantities": q_out},
                    "output": result
                })).unwrap();
                emitted += 1;
            }
        };
    }

    // Example inputs from problem description
    emit!(6, vec![11, 6], 0);
    emit!(7, vec![15, 10, 10], 0);
    emit!(1, vec![100000], 0);

    // Example inputs with all mutations
    for mk in 0u8..=9 {
        emit!(6, vec![11, 6], mk);
        emit!(7, vec![15, 10, 10], mk);
        emit!(1, vec![100000], mk);
    }

    // Boundary cases
    emit!(1, vec![1], 0);
    emit!(100000, vec![100000], 0);
    emit!(100000, vec![1], 0);
    emit!(2, vec![1, 1], 0);
    emit!(100000, vec![1, 1], 0);

    // Single element quantities with various n and mutations
    for mk in 0u8..=9 {
        emit!(1, vec![50000], mk);
        emit!(100000, vec![50000], mk);
    }

    // Fill remaining with random test cases
    while emitted < count {
        // Size class for m (number of product types)
        let m: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };

        // n >= m, with diverse ratios
        let n: i32 = match emitted % 4 {
            0 => m as i32,                                                          // tight: n == m
            1 => rng.gen_range_i64(m as i64, (m as i64 * 2).min(100000)) as i32,    // small slack
            2 => rng.gen_range_i64(m as i64, 100000) as i32,                        // random
            _ => 100000,                                                            // max n
        };

        // Generate quantities with diverse values
        let mut quantities = Vec::new();
        for j in 0..m {
            let q = if j == 0 && emitted % 10 == 0 {
                1 // boundary: min quantity
            } else if j == 0 && emitted % 10 == 1 {
                100000 // boundary: max quantity
            } else {
                rng.gen_range_i64(1, 100000) as i32
            };
            quantities.push(q);
        }

        let mk = (rng.next_u64() % 10) as u8;
        emit!(n, quantities, mk);
    }
}
