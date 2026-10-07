use vstd::prelude::*;

verus! {

/// Generates valid (nums, change_indices) pairs for lc3048.
///
/// Construction: takes `nums` values and `change_raw` values as seeds,
/// then applies mutations. The cross-dependency (change_indices[i] must
/// be in [1, nums.len()]) makes pure scalar construction impractical,
/// so the construction parameters carry the arrays directly.
///
/// Mutations provide structural diversity:
///   0 = identity
///   1 = set all nums to 0
///   2 = set a specific nums element to 0
///   3 = set all change_indices to 1
///   4 = swap two elements in change_indices
///   5 = set a specific nums element to max (1_000_000_000)
///   else = identity fallback
pub fn generate_test_case(
    nums: Vec<i32>,
    change_indices: Vec<i32>,
    mutation_kind: u8,
    swap_a: usize,
    swap_b: usize,
    target_idx: usize,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums.len() <= 2000,
        1 <= change_indices.len() <= 2000,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < change_indices.len() ==> 1 <= #[trigger] change_indices[i] <= nums.len(),
        swap_a < change_indices.len(),
        swap_b < change_indices.len(),
        target_idx < nums.len(),
    ensures
        1 <= result.0.len() <= 2000,
        1 <= result.1.len() <= 2000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= result.0.len(),
{
    if mutation_kind == 0u8 {
        // identity
        (nums, change_indices)
    } else if mutation_kind == 1u8 {
        // set all nums to 0
        let mut n = nums;
        let len = n.len();
        let mut i: usize = 0;
        while i < len
            invariant
                len == n.len(),
                n.len() == nums.len(),
                0 <= i <= len,
                1 <= n.len() <= 2000,
                forall|j: int| 0 <= j < i ==> n[j] == 0i32,
                forall|j: int| i <= j < len ==> n[j] == nums[j],
                forall|j: int| 0 <= j < i ==> 0 <= #[trigger] n[j] <= 1_000_000_000,
                forall|j: int| i <= j < len ==> 0 <= #[trigger] n[j] <= 1_000_000_000,
            decreases len - i,
        {
            n.set(i, 0i32);
            i = i + 1;
        }
        assert(n.len() == nums.len());
        (n, change_indices)
    } else if mutation_kind == 2u8 {
        // set target_idx element of nums to 0
        let mut n = nums;
        n.set(target_idx, 0i32);
        assert forall|i: int| 0 <= i < n.len() implies 0 <= #[trigger] n[i] <= 1_000_000_000
        by {
            if i == target_idx as int {
                assert(n[i] == 0i32);
            } else {
                assert(n[i] == nums[i]);
            }
        }
        (n, change_indices)
    } else if mutation_kind == 3u8 {
        // set all change_indices to 1
        let mut c = change_indices;
        let len = c.len();
        let mut i: usize = 0;
        while i < len
            invariant
                len == c.len(),
                c.len() == change_indices.len(),
                0 <= i <= len,
                1 <= c.len() <= 2000,
                1 <= nums.len() <= 2000,
                forall|j: int| 0 <= j < i ==> c[j] == 1i32,
                forall|j: int| 0 <= j < i ==> 1 <= #[trigger] c[j] <= nums.len(),
                forall|j: int| i <= j < len ==> c[j] == change_indices[j],
                forall|j: int| i <= j < len ==> 1 <= #[trigger] c[j] <= nums.len(),
            decreases len - i,
        {
            c.set(i, 1i32);
            i = i + 1;
        }
        (nums, c)
    } else if mutation_kind == 4u8 {
        // swap two elements in change_indices
        let mut c = change_indices;
        let va = c[swap_a];
        let vb = c[swap_b];
        c.set(swap_a, vb);
        c.set(swap_b, va);
        assert forall|i: int| 0 <= i < c.len() implies 1 <= #[trigger] c[i] <= nums.len()
        by {
            if i == swap_a as int {
                assert(c[i] == vb);
                assert(1 <= vb <= nums.len());
            } else if i == swap_b as int {
                assert(c[i] == va);
                assert(1 <= va <= nums.len());
            } else {
                assert(c[i] == change_indices[i]);
            }
        }
        (nums, c)
    } else if mutation_kind == 5u8 {
        // set target_idx element of nums to max value
        let mut n = nums;
        n.set(target_idx, 1_000_000_000i32);
        assert forall|i: int| 0 <= i < n.len() implies 0 <= #[trigger] n[i] <= 1_000_000_000
        by {
            if i == target_idx as int {
                assert(n[i] == 1_000_000_000i32);
            } else {
                assert(n[i] == nums[i]);
            }
        }
        (n, change_indices)
    } else {
        // fallback: identity
        (nums, change_indices)
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

struct Solution;
include!("../code.rs");

extern crate serde_json;
use serde_json::json;

fn random_nums(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i64(0, 1_000_000_000) as i32);
    }
    v
}

fn random_change_indices(rng: &mut Rng, m: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(m);
    for _ in 0..m {
        v.push(rng.gen_range_i64(1, n as i64) as i32);
    }
    v
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

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![2, 2, 0], vec![2, 2, 2, 2, 3, 2, 2, 1]),
        (vec![1, 3], vec![1, 1, 1, 2, 1, 1, 1]),
        (vec![0, 1], vec![2, 2, 2]),
    ];

    let mut written = 0usize;

    // Write example inputs first
    for (nums, change_indices) in &examples {
        if written >= count {
            break;
        }
        let result = Solution::earliest_second_to_mark_indices(
            nums.clone(),
            change_indices.clone(),
        );
        writeln!(
            out,
            "{}",
            json!({"input": {"nums": nums, "changeIndices": change_indices}, "output": result})
        )
        .unwrap();
        written += 1;
    }

    // Generate random test cases
    let num_mutations: u8 = 6;
    while written < count {
        // Size classes for n
        let n: usize = match written % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 2000),  // max
        };

        // Size classes for m
        let m: usize = match (written / 5) % 5 {
            0 => rng.gen_range_usize(1, 3),       // tiny
            1 => rng.gen_range_usize(1, 10),      // small
            2 => rng.gen_range_usize(11, 100),    // medium
            3 => rng.gen_range_usize(101, 500),   // large
            _ => rng.gen_range_usize(501, 2000),  // max
        };

        // Build base arrays
        let nums_base = random_nums(&mut rng, n);
        let ci_base = random_change_indices(&mut rng, m, n);

        // Pick mutation
        let mutation_kind = (written % num_mutations as usize) as u8;
        let swap_a = rng.gen_range_usize(0, m - 1);
        let swap_b = rng.gen_range_usize(0, m - 1);
        let target_idx = rng.gen_range_usize(0, n - 1);

        // Boundary value injection (~20% of cases)
        let nums_input = if written % 5 == 0 {
            let mut v = nums_base.clone();
            // Set some elements to boundary values
            v[0] = 0;
            let vlen = v.len();
            if vlen > 1 {
                v[vlen - 1] = 1_000_000_000;
            }
            v
        } else {
            nums_base
        };

        let (nums_out, ci_out) = generate_test_case(
            nums_input,
            ci_base,
            mutation_kind,
            swap_a,
            swap_b,
            target_idx,
        );

        let result = Solution::earliest_second_to_mark_indices(
            nums_out.clone(),
            ci_out.clone(),
        );

        writeln!(
            out,
            "{}",
            json!({"input": {"nums": nums_out, "changeIndices": ci_out}, "output": result})
        )
        .unwrap();
        written += 1;
    }
}
