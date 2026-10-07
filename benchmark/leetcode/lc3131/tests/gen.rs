use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    base_vals: Vec<i32>,
    delta: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= base_vals.len() <= 100,
        forall |i: int| 0 <= i < base_vals.len() ==> 0 <= #[trigger] base_vals[i] <= 500,
        0 <= delta <= 500,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] as int + (result.1[0] as int - result.0[0] as int) == result.1[i] as int,
{
    let n = base_vals.len();

    // Build nums2 where nums2[i] = base_vals[i] + delta
    let mut nums2: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == base_vals.len(),
            0 <= idx <= n,
            nums2.len() == idx,
            1 <= n <= 100,
            0 <= delta <= 500,
            forall |j: int| 0 <= j < base_vals.len() ==> 0 <= #[trigger] base_vals[j] <= 500,
            forall |j: int| 0 <= j < idx as int ==> nums2[j] == base_vals[j] + delta,
            forall |j: int| 0 <= j < idx as int ==> 0 <= #[trigger] nums2[j] <= 1000,
        decreases n - idx,
    {
        nums2.push(base_vals[idx] + delta);
        idx += 1;
    }

    if mutation_kind == 1 {
        // swap: nums1 = base+delta, nums2 = base (negative effective delta)
        (nums2, base_vals)
    } else if mutation_kind == 2 {
        // uniform: all elements of nums1 = base_vals[0], nums2 = base_vals[0]+delta
        let v1 = base_vals[0];
        let v2 = v1 + delta;
        let mut u1: Vec<i32> = Vec::new();
        let mut u2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                n == base_vals.len(),
                u1.len() == k,
                u2.len() == k,
                0 <= v1 <= 500,
                0 <= v2 <= 1000,
                v2 == v1 + delta,
                0 <= delta <= 500,
                forall |j: int| 0 <= j < k as int ==> #[trigger] u1[j] == v1,
                forall |j: int| 0 <= j < k as int ==> #[trigger] u2[j] == v2,
            decreases n - k,
        {
            u1.push(v1);
            u2.push(v2);
            k += 1;
        }
        (u1, u2)
    } else if mutation_kind == 3 {
        // zero offset: nums2 = copy of base_vals (delta effectively 0)
        let mut u2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                n == base_vals.len(),
                u2.len() == k,
                forall |j: int| 0 <= j < base_vals.len() ==> 0 <= #[trigger] base_vals[j] <= 500,
                forall |j: int| 0 <= j < k as int ==> #[trigger] u2[j] == base_vals[j],
            decreases n - k,
        {
            u2.push(base_vals[k]);
            k += 1;
        }
        (base_vals, u2)
    } else if mutation_kind == 4 {
        // all-zero base: nums1 = [0..0], nums2 = [delta..delta]
        let mut u1: Vec<i32> = Vec::new();
        let mut u2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                n == base_vals.len(),
                u1.len() == k,
                u2.len() == k,
                0 <= delta <= 500,
                forall |j: int| 0 <= j < k as int ==> #[trigger] u1[j] == 0i32,
                forall |j: int| 0 <= j < k as int ==> #[trigger] u2[j] == delta,
            decreases n - k,
        {
            u1.push(0);
            u2.push(delta);
            k += 1;
        }
        (u1, u2)
    } else if mutation_kind == 5 {
        // max base: nums1 = [500..500], nums2 = [500+delta..500+delta]
        let v2 = 500 + delta;
        let mut u1: Vec<i32> = Vec::new();
        let mut u2: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < n
            invariant
                0 <= k <= n,
                1 <= n <= 100,
                n == base_vals.len(),
                u1.len() == k,
                u2.len() == k,
                0 <= delta <= 500,
                v2 == 500i32 + delta,
                forall |j: int| 0 <= j < k as int ==> #[trigger] u1[j] == 500i32,
                forall |j: int| 0 <= j < k as int ==> #[trigger] u2[j] == v2,
            decreases n - k,
        {
            u1.push(500);
            u2.push(v2);
            k += 1;
        }
        (u1, u2)
    } else {
        // default: identity (base_vals, base_vals + delta)
        (base_vals, nums2)
    }
}

} // verus!

extern crate serde_json;
use serde_json::json;

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

fn random_base_vals(rng: &mut Rng, len: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_range_i64(lo as i64, hi as i64) as i32);
    }
    v
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(3131);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let mut emit = |nums1: Vec<i32>, nums2: Vec<i32>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, emitted: &mut usize| {
        if *emitted >= count { return; }
        let key = format!("{:?}|{:?}", nums1, nums2);
        if !seen.insert(key) { return; }
        let output = Solution::added_integer(nums1.clone(), nums2.clone());
        writeln!(out, "{}", json!({
            "input": {"nums1": nums1, "nums2": nums2},
            "output": output
        })).unwrap();
        *emitted += 1;
    };

    // Example inputs from description.md
    let examples: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![2, 6, 4], vec![9, 7, 5]),       // delta=7, but nums1+7=nums2 element-wise
        (vec![10], vec![5]),                    // delta=-5
        (vec![1, 1, 1, 1], vec![1, 1, 1, 1]),  // delta=0
    ];
    for (n1, n2) in examples {
        emit(n1, n2, &mut seen, &mut out, &mut emitted);
    }

    // Seed base arrays with mutations
    let seed_bases: Vec<Vec<i32>> = vec![
        vec![0],
        vec![500],
        vec![250],
        vec![0, 0],
        vec![100, 200, 300],
        vec![0, 500, 250, 100, 400],
    ];
    let deltas: Vec<i32> = vec![0, 1, 250, 499, 500];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5];

    for base in &seed_bases {
        for &d in &deltas {
            for &mk in &mutation_kinds {
                if emitted >= count { break; }
                let (n1, n2) = generate_test_case(base.clone(), d, mk);
                emit(n1, n2, &mut seen, &mut out, &mut emitted);
            }
        }
    }

    // Random cases with diverse size classes and mutations
    while emitted < count {
        let n: usize = match emitted % 5 {
            0 => rng.gen_range_usize(1, 3),     // tiny
            1 => rng.gen_range_usize(1, 10),    // small
            2 => rng.gen_range_usize(11, 30),   // medium
            3 => rng.gen_range_usize(31, 70),   // large
            _ => rng.gen_range_usize(71, 100),  // max
        };
        let delta = rng.gen_range_i64(0, 500) as i32;
        let base = random_base_vals(&mut rng, n, 0, 500);
        let mk = rng.gen_range_usize(0, 5) as u8;
        let (n1, n2) = generate_test_case(base, delta, mk);
        emit(n1, n2, &mut seen, &mut out, &mut emitted);
    }
}
