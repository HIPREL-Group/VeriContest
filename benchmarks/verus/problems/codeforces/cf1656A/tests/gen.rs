use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seed_vals: Vec<i64>,
    mutation_kind: u8,
    extra_val: i64,
) -> (result: Vec<i64>)
    requires
        1 <= seed_vals.len() <= 200_000,
        forall|t: int| 0 <= t < seed_vals.len() ==> #[trigger] (seed_vals[t] as int) >= 1,
        extra_val >= 1i64,
    ensures
        1 <= result.len() <= 200_000,
        forall|t: int| 0 <= t < result.len() ==> #[trigger] (result[t] as int) >= 1,
{
    if mutation_kind == 0 {
        seed_vals
    } else if mutation_kind == 1 && seed_vals.len() < 200_000 {
        let mut v = seed_vals;
        v.push(extra_val);
        proof {
            assert forall|t: int| 0 <= t < v.len() implies #[trigger] (v[t] as int) >= 1 by {
                if t < seed_vals.len() as int {
                    assert(v@[t] == seed_vals@[t]);
                } else {
                    assert(v@[t] == extra_val);
                }
            };
        }
        v
    } else if mutation_kind == 2 && seed_vals.len() > 1 {
        let mut v = seed_vals;
        v.pop();
        proof {
            assert forall|t: int| 0 <= t < v.len() implies #[trigger] (v[t] as int) >= 1 by {
                assert(v@[t] == seed_vals@[t]);
            };
        }
        v
    } else if mutation_kind == 3 {
        let n = seed_vals.len();
        let mut v: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < n
            invariant
                n == seed_vals.len(),
                1 <= n <= 200_000,
                0 <= i <= n,
                v.len() == i,
                extra_val >= 1i64,
                forall|t: int| 0 <= t < v.len() ==> #[trigger] (v[t] as int) >= 1,
            decreases n - i,
        {
            v.push(extra_val);
            proof {
                assert forall|t: int| 0 <= t < v.len() implies #[trigger] (v[t] as int) >= 1 by {
                    if t < i as int {
                    } else {
                        assert(v@[t] == extra_val);
                    }
                };
            }
            i = i + 1;
        }
        v
    } else if mutation_kind == 4 && seed_vals.len() >= 2 {
        let n = seed_vals.len();
        let mut v = seed_vals;
        let first = v[0];
        let last = v[n - 1];
        v.set(0, last);
        v.set(n - 1, first);
        proof {
            assert forall|t: int| 0 <= t < v.len() implies #[trigger] (v[t] as int) >= 1 by {
                if t == 0 {
                    assert(v@[t] == last);
                } else if t == n - 1 {
                    assert(v@[t] == first);
                } else {
                    assert(v@[t] == seed_vals@[t]);
                }
            };
        }
        v
    } else if mutation_kind == 5 {
        let mut v = seed_vals;
        v.set(0, extra_val);
        proof {
            assert forall|t: int| 0 <= t < v.len() implies #[trigger] (v[t] as int) >= 1 by {
                if t == 0 {
                    assert(v@[t] == extra_val);
                } else {
                    assert(v@[t] == seed_vals@[t]);
                }
            };
        }
        v
    } else if mutation_kind == 6 {
        let n = seed_vals.len();
        let mut v = seed_vals;
        v.set(n - 1, extra_val);
        proof {
            assert forall|t: int| 0 <= t < v.len() implies #[trigger] (v[t] as int) >= 1 by {
                if t == n - 1 {
                    assert(v@[t] == extra_val);
                } else {
                    assert(v@[t] == seed_vals@[t]);
                }
            };
        }
        v
    } else {
        seed_vals
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

    fn gen_u8(&mut self) -> u8 {
        (self.next_u64() % 256) as u8
    }
}

struct Solution;
include!("../code.rs");

fn main() {
    use std::io::Write;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut count = 0usize;

    // Example inputs from description.md
    let examples: Vec<Vec<i64>> = vec![
        vec![5, 2, 7],
        vec![1, 4, 2, 2, 3],
        vec![12],
    ];
    for a in &examples {
        if count >= goal { break; }
        let (i, j) = Solution::good_pair_indices(a.clone());
        writeln!(out, "{}", json!({"input": {"a": a}, "output": [i, j]})).unwrap();
        count += 1;
    }

    // Size classes for array length
    let size_classes: Vec<(usize, usize)> = vec![
        (1, 3),
        (4, 10),
        (11, 100),
        (101, 1000),
        (1001, 10000),
    ];

    while count < goal {
        let (lo_n, hi_n) = size_classes[count % size_classes.len()];
        let n = rng.gen_range_usize(lo_n, hi_n);

        let mut seed_vals: Vec<i64> = Vec::with_capacity(n);
        for _ in 0..n {
            let val = if rng.gen_u8() < 50 {
                match rng.gen_u8() % 5 {
                    0 => 1i64,
                    1 => 1_000_000_000i64,
                    2 => 2i64,
                    3 => 999_999_999i64,
                    _ => 42i64,
                }
            } else {
                rng.gen_range_i64(1, 1_000_000_000)
            };
            seed_vals.push(val);
        }

        let mk = rng.gen_u8() % 7;
        let extra_val = rng.gen_range_i64(1, 1_000_000_000);
        let a = generate_test_case(seed_vals, mk, extra_val);
        let (i, j) = Solution::good_pair_indices(a.clone());
        writeln!(out, "{}", json!({"input": {"a": a}, "output": [i, j]})).unwrap();
        count += 1;
    }
}
