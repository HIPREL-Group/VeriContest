use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_plain_prefix(nums: Seq<i32>, end: int, v: int) -> int
        decreases end,
    {
        if end <= 0 {
            0int
        } else {
            Self::count_plain_prefix(nums, end - 1, v) + if nums[end - 1] as int == v { 1int } else { 0int }
        }
    }

    pub open spec fn count_shift_prefix(nums: Seq<i32>, end: int, x: int, v: int) -> int
        decreases end,
    {
        if end <= 0 {
            0int
        } else {
            Self::count_shift_prefix(nums, end - 1, x, v) + if nums[end - 1] as int + x == v { 1int } else { 0int }
        }
    }

    pub open spec fn valid_x_spec(nums1: Seq<i32>, nums2: Seq<i32>, x: int) -> bool {
        forall |v: int| 0 <= v <= 1000 ==> Self::count_shift_prefix(nums1, nums1.len() as int, x, v) >= Self::count_plain_prefix(nums2, nums2.len() as int, v)
    }

    proof fn lemma_count_shift_nonneg(nums: Seq<i32>, end: int, x: int, v: int)
        requires 0 <= end <= nums.len(),
        ensures Self::count_shift_prefix(nums, end, x, v) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_shift_nonneg(nums, end - 1, x, v);
        }
    }

    proof fn lemma_count_plain_nonneg(nums: Seq<i32>, end: int, v: int)
        requires 0 <= end <= nums.len(),
        ensures Self::count_plain_prefix(nums, end, v) >= 0,
        decreases end,
    {
        if end > 0 {
            Self::lemma_count_plain_nonneg(nums, end - 1, v);
        }
    }

    proof fn lemma_prefix_subset(nums1: Seq<i32>, nums2: Seq<i32>, n: int, m: int, v: int)
        requires
            0 <= m <= n,
            n <= nums1.len(),
            m <= nums2.len(),
            forall |i: int| 0 <= i < m ==> nums1[i] == nums2[i],
        ensures
            Self::count_shift_prefix(nums1, n, 0, v) >= Self::count_plain_prefix(nums2, m, v),
        decreases n,
    {
        Self::lemma_count_shift_nonneg(nums1, n, 0, v);
        Self::lemma_count_plain_nonneg(nums2, m, v);
        if m <= 0 {
        } else if n == m {
            Self::lemma_prefix_subset(nums1, nums2, n - 1, m - 1, v);
            assert(nums1[n - 1] == nums2[m - 1]);
        } else {
            Self::lemma_prefix_subset(nums1, nums2, n - 1, m, v);
        }
    }

    pub fn generate_test_case(
        seed_vals: Vec<i32>,
        extra1: i32,
        extra2: i32,
        mutation_kind: u8,
    ) -> (result: (Vec<i32>, Vec<i32>))
        requires
            1 <= seed_vals.len() <= 198,
            forall |i: int| 0 <= i < seed_vals.len() ==> 0 <= #[trigger] seed_vals[i] <= 1000,
            0 <= extra1 <= 1000,
            0 <= extra2 <= 1000,
            mutation_kind < 5,
        ensures
            3 <= result.0.len() <= 200,
            result.1.len() + 2 == result.0.len(),
            forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
            forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
            exists |x: int| -1000 <= x <= 1000 && Self::valid_x_spec(result.0@, result.1@, x),
    {
        let n2 = seed_vals.len();

        let mut nums1: Vec<i32> = Vec::new();
        let mut nums2: Vec<i32> = Vec::new();

        let mut i: usize = 0;
        while i < seed_vals.len()
            invariant
                0 <= i <= seed_vals.len(),
                nums1.len() == i,
                nums2.len() == i,
                seed_vals.len() == n2,
                1 <= n2 <= 198,
                forall |k: int| 0 <= k < seed_vals.len() ==> 0 <= #[trigger] seed_vals[k] <= 1000,
                forall |j: int| 0 <= j < i as int ==> nums1[j] == seed_vals[j],
                forall |j: int| 0 <= j < i as int ==> nums2[j] == seed_vals[j],
                forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums1[j] <= 1000,
                forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums2[j] <= 1000,
            decreases seed_vals.len() - i,
        {
            let val = seed_vals[i];
            assert(0 <= val <= 1000);
            nums1.push(val);
            nums2.push(val);
            i += 1;
        }

        let e1: i32;
        let e2: i32;
        if mutation_kind == 0 {
            e1 = extra1;
            e2 = extra2;
        } else if mutation_kind == 1 {
            e1 = 0;
            e2 = 0;
        } else if mutation_kind == 2 {
            e1 = 1000;
            e2 = 1000;
        } else if mutation_kind == 3 {
            e1 = 0;
            e2 = 1000;
        } else {
            e1 = extra2;
            e2 = extra1;
        }

        nums1.push(e1);
        nums1.push(e2);

        assert(nums1.len() == n2 + 2);
        assert(nums2.len() == n2);
        assert(3 <= nums1.len() <= 200) by {
            assert(nums1.len() == n2 + 2);
            assert(1 <= n2 <= 198);
        }

        assert forall |j: int| 0 <= j < nums1.len() implies 0 <= #[trigger] nums1[j] <= 1000 by {
            if j < n2 as int {
                assert(nums1[j] == seed_vals[j]);
                assert(0 <= seed_vals[j] <= 1000);
            } else if j == n2 as int {
                assert(nums1[j] == e1);
            } else {
                assert(j == n2 as int + 1);
                assert(nums1[j] == e2);
            }
        }

        assert forall |j: int| 0 <= j < nums2.len() implies 0 <= #[trigger] nums2[j] <= 1000 by {
            assert(nums2[j] == seed_vals[j]);
            assert(0 <= seed_vals[j] <= 1000);
        }

        assert(forall |j: int| 0 <= j < n2 as int ==> nums1[j] == nums2[j]);

        proof {
            assert forall |v: int| 0 <= v <= 1000 implies
                Self::count_shift_prefix(nums1@, nums1@.len() as int, 0, v)
                >= Self::count_plain_prefix(nums2@, nums2@.len() as int, v)
            by {
                Self::lemma_prefix_subset(
                    nums1@, nums2@,
                    nums1@.len() as int,
                    nums2@.len() as int,
                    v,
                );
            }
            assert(Self::valid_x_spec(nums1@, nums2@, 0));
            assert(-1000 <= 0int <= 1000 && Self::valid_x_spec(nums1@, nums2@, 0));
        }

        let result = (nums1, nums2);

        proof {
            assert(Self::valid_x_spec(result.0@, result.1@, 0));
            assert(-1000 <= 0int <= 1000 && Self::valid_x_spec(result.0@, result.1@, 0));
        }

        result
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
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let (lo, hi) = if lo <= hi { (lo, hi) } else { (hi, lo) };
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

#[allow(dead_code)]
mod solution_code {
    pub struct Solution;
    include!("../code.rs");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);

    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    use std::io::Write;
    use std::collections::HashSet;

    let mut seen = HashSet::new();
    let mut emitted = 0usize;

    let boundaries: [i32; 5] = [0, 1, 500, 999, 1000];

    macro_rules! emit {
        ($seed_vals:expr, $extra1:expr, $extra2:expr, $mk:expr) => {
            if emitted < count {
                let sv: Vec<i32> = $seed_vals;
                let e1: i32 = $extra1;
                let e2: i32 = $extra2;
                let mk: u8 = $mk;
                let (nums1, nums2) = Solution::generate_test_case(sv, e1, e2, mk);
                let result = solution_code::Solution::minimum_added_integer(
                    nums1.clone(), nums2.clone(),
                );
                let line = json!({
                    "input": {"nums1": nums1, "nums2": nums2},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    emitted += 1;
                }
            }
        };
    }

    // ---- LeetCode examples ----
    emit!(vec![14, 18, 10], 4, 8, 0);    // example 1: nums1=[14,18,10,4,8] nums2=[14,18,10]
    emit!(vec![7, 7], 3, 3, 0);          // example 2: nums1=[7,7,3,3] nums2=[7,7]

    // ---- Boundary: single-element seed_vals with all mutations ----
    for mk in 0u8..5 {
        emit!(vec![0], 0, 0, mk);
        emit!(vec![1000], 1000, 1000, mk);
        emit!(vec![500], 0, 1000, mk);
        emit!(vec![0], 1000, 0, mk);
    }

    // ---- Two-element seed_vals, all mutations ----
    for mk in 0u8..5 {
        emit!(vec![0, 1000], 500, 500, mk);
        emit!(vec![100, 200], 0, 1000, mk);
    }

    // ---- Small seed_vals (3-5 elements), varied mutations ----
    for mk in 0u8..5 {
        emit!(vec![10, 20, 30], 5, 15, mk);
        emit!(vec![0, 0, 0, 0, 0], 0, 0, mk);
        emit!(vec![1000, 1000, 1000], 1000, 1000, mk);
    }

    // ---- Random tiny arrays (1-3 elements), all mutations ----
    for _ in 0..4 {
        let n2 = rng.gen_range_usize(1, 3);
        let sv: Vec<i32> = (0..n2).map(|j| {
            if j % 3 == 0 { boundaries[rng.gen_range_usize(0, 4)] }
            else { rng.gen_range_i64(0, 1000) as i32 }
        }).collect();
        let e1 = rng.gen_range_i64(0, 1000) as i32;
        let e2 = rng.gen_range_i64(0, 1000) as i32;
        for mk in 0u8..5 {
            emit!(sv.clone(), e1, e2, mk);
        }
    }

    // ---- Random small arrays (4-10 elements), random mutations ----
    for _ in 0..6 {
        let n2 = rng.gen_range_usize(4, 10);
        let sv: Vec<i32> = (0..n2).map(|j| {
            if j % 5 == 0 { boundaries[rng.gen_range_usize(0, 4)] }
            else { rng.gen_range_i64(0, 1000) as i32 }
        }).collect();
        let e1 = rng.gen_range_i64(0, 1000) as i32;
        let e2 = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 4)) as u8;
        emit!(sv.clone(), e1, e2, mk);
    }

    // ---- Random medium arrays (11-50 elements), random mutations ----
    for _ in 0..6 {
        let n2 = rng.gen_range_usize(11, 50);
        let sv: Vec<i32> = (0..n2).map(|j| {
            if j % 5 == 0 { boundaries[rng.gen_range_usize(0, 4)] }
            else { rng.gen_range_i64(0, 1000) as i32 }
        }).collect();
        let e1 = rng.gen_range_i64(0, 1000) as i32;
        let e2 = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 4)) as u8;
        emit!(sv.clone(), e1, e2, mk);
    }

    // ---- Random large arrays (51-100 elements), random mutations ----
    for _ in 0..4 {
        let n2 = rng.gen_range_usize(51, 100);
        let sv: Vec<i32> = (0..n2).map(|j| {
            if j % 5 == 0 { boundaries[rng.gen_range_usize(0, 4)] }
            else { rng.gen_range_i64(0, 1000) as i32 }
        }).collect();
        let e1 = rng.gen_range_i64(0, 1000) as i32;
        let e2 = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 4)) as u8;
        emit!(sv.clone(), e1, e2, mk);
    }

    // ---- Maximum size arrays (198 elements) ----
    for mk in 0u8..5 {
        let sv: Vec<i32> = (0..198).map(|j| {
            if j % 5 == 0 { boundaries[rng.gen_range_usize(0, 4)] }
            else { rng.gen_range_i64(0, 1000) as i32 }
        }).collect();
        emit!(sv, rng.gen_range_i64(0, 1000) as i32, rng.gen_range_i64(0, 1000) as i32, mk);
    }

    // ---- Fill remaining with random sizes and random mutations ----
    let mut _attempts: usize = 0;
    while emitted < count {
        _attempts += 1;
        if _attempts > 10000 { break; }

        let n2: usize = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 3),
            1 => rng.gen_range_usize(1, 10),
            2 => rng.gen_range_usize(11, 50),
            3 => rng.gen_range_usize(51, 100),
            _ => rng.gen_range_usize(101, 198),
        };

        let sv: Vec<i32> = (0..n2).map(|j| {
            if j % 5 == 0 { boundaries[rng.gen_range_usize(0, 4)] }
            else { rng.gen_range_i64(0, 1000) as i32 }
        }).collect();

        let e1 = rng.gen_range_i64(0, 1000) as i32;
        let e2 = rng.gen_range_i64(0, 1000) as i32;
        let mk = (rng.gen_range_usize(0, 4)) as u8;

        emit!(sv, e1, e2, mk);
    }
}
