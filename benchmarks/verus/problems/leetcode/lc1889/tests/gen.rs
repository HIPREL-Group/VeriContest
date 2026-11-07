use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    packages: Vec<i32>,
    boxes: Vec<Vec<i32>>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= packages.len() <= 100_000,
        forall |i: int| 0 <= i < packages.len() ==> 1 <= #[trigger] packages[i] <= 100_000,
        1 <= boxes.len() <= 100_000,
        forall |j: int| #![trigger boxes@[j]] 0 <= j < boxes@.len() ==> 1 <= boxes@[j]@.len() <= 100_000,
        forall |j: int, k: int| 0 <= j < boxes@.len() && 0 <= k < boxes@[j]@.len()
            ==> 1 <= #[trigger] boxes@[j]@[k] <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall |j: int| #![trigger result.1@[j]] 0 <= j < result.1@.len() ==> 1 <= result.1@[j]@.len() <= 100_000,
        forall |j: int, k: int| 0 <= j < result.1@.len() && 0 <= k < result.1@[j]@.len()
            ==> 1 <= #[trigger] result.1@[j]@[k] <= 100_000,
{
    if mutation_kind == 0 {
        // identity
        (packages, boxes)
    } else if mutation_kind == 1 && packages[0] < 100_000i32 {
        // nudge first package up
        let mut pkgs = packages;
        pkgs.set(0, pkgs[0] + 1);
        (pkgs, boxes)
    } else if mutation_kind == 2 && packages[0] > 1i32 {
        // nudge first package down
        let mut pkgs = packages;
        pkgs.set(0, pkgs[0] - 1);
        (pkgs, boxes)
    } else if mutation_kind == 3 {
        // set first package to min boundary
        let mut pkgs = packages;
        pkgs.set(0, 1i32);
        (pkgs, boxes)
    } else if mutation_kind == 4 {
        // set first package to max boundary
        let mut pkgs = packages;
        pkgs.set(0, 100_000i32);
        (pkgs, boxes)
    } else if mutation_kind == 5 {
        // nudge last package up
        let last = packages.len() - 1;
        let mut pkgs = packages;
        if pkgs[last] < 100_000i32 {
            pkgs.set(last, pkgs[last] + 1);
        }
        (pkgs, boxes)
    } else if mutation_kind == 6 {
        // nudge last package down
        let last = packages.len() - 1;
        let mut pkgs = packages;
        if pkgs[last] > 1i32 {
            pkgs.set(last, pkgs[last] - 1);
        }
        (pkgs, boxes)
    } else if mutation_kind == 7 {
        // set first package to min and last to max
        let mut pkgs = packages;
        pkgs.set(0, 1i32);
        let last = pkgs.len() - 1;
        pkgs.set(last, 100_000i32);
        (pkgs, boxes)
    } else if mutation_kind == 8 {
        // set all packages to same value (first element)
        let val = packages[0];
        let n = packages.len();
        let mut pkgs = packages;
        let mut i: usize = 1;
        while i < n
            invariant
                n == pkgs.len(),
                1 <= n <= 100_000,
                1 <= i <= n,
                1 <= val <= 100_000,
                forall |k: int| 0 <= k < i as int ==> pkgs[k] == val,
                forall |k: int| 0 <= k < pkgs.len() ==> 1 <= #[trigger] pkgs[k] <= 100_000,
            decreases n - i,
        {
            pkgs.set(i, val);
            i = i + 1;
        }
        (pkgs, boxes)
    } else {
        // fallback: identity
        (packages, boxes)
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

fn random_packages(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut pkgs = Vec::with_capacity(n);
    for _ in 0..n {
        pkgs.push(rng.gen_range_i64(1, 100_000) as i32);
    }
    pkgs
}

fn random_boxes(rng: &mut Rng, m: usize, max_bj_len: usize) -> Vec<Vec<i32>> {
    let mut bxs = Vec::with_capacity(m);
    for _ in 0..m {
        let bj_len = rng.gen_range_usize(1, max_bj_len);
        let mut supplier = Vec::with_capacity(bj_len);
        for _ in 0..bj_len {
            supplier.push(rng.gen_range_i64(1, 100_000) as i32);
        }
        bxs.push(supplier);
    }
    bxs
}

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

    // Example 1: packages = [2,3,5], boxes = [[4,8],[2,8]]
    {
        let (pkgs, bxs) = generate_test_case(
            vec![2, 3, 5],
            vec![vec![4, 8], vec![2, 8]],
            0,
        );
        let result = Solution::min_wasted_space(pkgs.clone(), bxs.clone());
        writeln!(out, "{}", json!({"input": {"packages": pkgs, "boxes": bxs}, "output": result})).unwrap();
        emitted += 1;
    }

    // Example 2: packages = [2,3,5], boxes = [[1,4],[2,3],[3,4]]
    {
        let (pkgs, bxs) = generate_test_case(
            vec![2, 3, 5],
            vec![vec![1, 4], vec![2, 3], vec![3, 4]],
            0,
        );
        let result = Solution::min_wasted_space(pkgs.clone(), bxs.clone());
        writeln!(out, "{}", json!({"input": {"packages": pkgs, "boxes": bxs}, "output": result})).unwrap();
        emitted += 1;
    }

    // Example 3: packages = [3,5,8,10,11,12], boxes = [[12],[11,9],[10,5,14]]
    {
        let (pkgs, bxs) = generate_test_case(
            vec![3, 5, 8, 10, 11, 12],
            vec![vec![12], vec![11, 9], vec![10, 5, 14]],
            0,
        );
        let result = Solution::min_wasted_space(pkgs.clone(), bxs.clone());
        writeln!(out, "{}", json!({"input": {"packages": pkgs, "boxes": bxs}, "output": result})).unwrap();
        emitted += 1;
    }

    let num_mutations: u8 = 9;

    while emitted < count {
        // Size classes for packages
        let n_pkg: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 50),     // medium
            3 => rng.gen_range_usize(51, 200),    // large
            _ => rng.gen_range_usize(201, 500),   // bigger
        };

        // Size classes for number of suppliers
        let n_sup: usize = match emitted % 4 {
            0 => 1,
            1 => rng.gen_range_usize(1, 3),
            2 => rng.gen_range_usize(2, 5),
            _ => rng.gen_range_usize(3, 10),
        };

        // Max boxes per supplier (keep total manageable for O(n*m*k) code)
        let max_bj = match emitted % 3 {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            _ => rng.gen_range_usize(1, 20),
        };

        let pkgs = random_packages(&mut rng, n_pkg);
        let bxs = random_boxes(&mut rng, n_sup, max_bj);

        let mutation = (emitted as u8) % num_mutations;
        let (pkgs, bxs) = generate_test_case(pkgs, bxs, mutation);

        let result = Solution::min_wasted_space(pkgs.clone(), bxs.clone());
        writeln!(out, "{}", json!({
            "input": {"packages": pkgs, "boxes": bxs},
            "output": result
        })).unwrap();
        emitted += 1;
    }

    eprintln!("Generated {} test cases to {:?}", emitted, out_path);
}
