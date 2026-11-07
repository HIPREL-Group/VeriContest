use vstd::prelude::*;

verus! {

// Spec fn helpers copied from spec.rs

pub open spec fn ord_tuple(small: &(bool, i32), big: &(bool, i32)) -> bool {
    if small.0 != big.0 {
        !small.0 && big.0
    } else {
        small.1 < big.1
    }
}

pub open spec fn rot_tuple(nums: &Vec<i32>, i: int) -> (bool, i32) {
    if 0 <= i < nums.len() {
        (nums[i] < nums[0], nums[i])
    } else {
        (false, 0)
    }
}

// Sum of the first `end` elements of `deltas`.
pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

proof fn lemma_sum_deltas_strict(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a < b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 1i32,
    ensures
        sum_deltas(deltas, a) + (b - a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if b - a == 1 {
    } else {
        lemma_sum_deltas_strict(deltas, a, b - 1);
    }
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    rot: usize,
    target: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        deltas.len() + 1 <= 5_000,
        -10_000 <= base <= 10_000,
        -10_000 <= target <= 10_000,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
        rot <= deltas.len(),
    ensures
        1 <= result.0.len() <= 5_000,
        forall|i: int| 0 <= i < result.0.len() ==> -10_000 <= #[trigger] result.0[i] <= 10_000,
        forall|i: int, j: int|
            0 <= i < j < result.0.len() ==> #[trigger] ord_tuple(
                &rot_tuple(&result.0, i),
                &rot_tuple(&result.0, j),
            ),
        -10_000 <= result.1 <= 10_000,
{
    let n: usize = deltas.len() + 1;

    // Phase 1: Build strictly sorted array from base + cumulative deltas
    let mut sorted_arr: Vec<i32> = Vec::new();
    sorted_arr.push(base);

    let mut idx: usize = 0;
    while idx < deltas.len()
        invariant
            0 <= idx <= deltas.len(),
            sorted_arr.len() == (idx + 1) as int,
            deltas.len() + 1 <= 5_000,
            -10_000 <= base <= 10_000,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 10_000,
            forall|k: int| 0 <= k <= idx as int ==>
                sorted_arr[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < sorted_arr.len() ==> -10_000 <= #[trigger] sorted_arr[k] <= 10_000,
            forall|k: int, l: int| 0 <= k < l < sorted_arr.len() ==> sorted_arr[k] < sorted_arr[l],
        decreases deltas.len() - idx,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (idx + 1) as int, deltas.len() as int);
        }

        let next = sorted_arr[idx] + deltas[idx];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));

            assert(-10_000 <= next <= 10_000) by {
                assert(base as int + sum_deltas(deltas@, (idx + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
                assert(next as int <= 10_000);
                lemma_sum_deltas_mono(deltas@, 0, (idx + 1) as int);
                assert(sum_deltas(deltas@, (idx + 1) as int) >= 0);
                assert(next as int >= base as int >= -10_000);
            };

            assert forall|k: int| 0 <= k < sorted_arr.len() implies sorted_arr[k] < next by {
                assert(sorted_arr[k] as int == base as int + sum_deltas(deltas@, k));
                assert(next as int == base as int + sum_deltas(deltas@, (idx + 1) as int));
                lemma_sum_deltas_strict(deltas@, k, (idx + 1) as int);
            };
        }

        sorted_arr.push(next);
        idx = idx + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < sorted_arr.len()
                implies sorted_arr[k] < sorted_arr[l] by {
                if l < (sorted_arr.len() - 1) as int {
                } else {
                    assert(l == (sorted_arr.len() - 1) as int);
                    assert(sorted_arr[l] == next);
                }
            };
        }
    }

    // Phase 2: Build rotated array
    let mut nums: Vec<i32> = Vec::new();

    // First part: sorted_arr[rot .. n]  (the "high" segment, values >= sorted_arr[rot])
    let mut j: usize = rot;
    while j < n
        invariant
            rot <= j <= n,
            n == deltas.len() + 1,
            sorted_arr.len() == n as int,
            nums.len() == (j - rot) as int,
            forall|k: int| 0 <= k < sorted_arr.len() ==> -10_000 <= #[trigger] sorted_arr[k] <= 10_000,
            forall|k: int, l: int| 0 <= k < l < sorted_arr.len() ==> sorted_arr[k] < sorted_arr[l],
            forall|m: int| 0 <= m < nums.len() ==> nums[m] == sorted_arr[rot as int + m],
            forall|m: int| 0 <= m < nums.len() ==> -10_000 <= #[trigger] nums[m] <= 10_000,
            forall|m1: int, m2: int| 0 <= m1 < m2 < nums.len() ==> nums[m1] < nums[m2],
        decreases n - j,
    {
        proof {
            assert(-10_000 <= sorted_arr[j as int] <= 10_000);
            assert forall|m: int| 0 <= m < nums.len() implies nums[m] < sorted_arr[j as int] by {
                assert(nums[m] == sorted_arr[rot as int + m]);
                assert(rot as int + m < j as int);
            };
        }

        nums.push(sorted_arr[j]);
        j = j + 1;

        proof {
            assert forall|m: int| 0 <= m < nums.len()
                implies nums[m] == sorted_arr[rot as int + m] by {
                if m < (nums.len() - 1) as int {
                } else {
                    assert(nums[m] == sorted_arr[(j - 1) as int]);
                    assert(rot as int + m == (j - 1) as int);
                }
            };
            assert forall|m1: int, m2: int| 0 <= m1 < m2 < nums.len()
                implies nums[m1] < nums[m2] by {
                if m2 < (nums.len() - 1) as int {
                } else {
                    assert(nums[m1] == sorted_arr[rot as int + m1]);
                    assert(rot as int + m1 < (j - 1) as int);
                }
            };
        }
    }

    let high_len: usize = nums.len();

    // Second part: sorted_arr[0 .. rot]  (the "low" segment, values < sorted_arr[rot])
    let mut k: usize = 0;
    while k < rot
        invariant
            0 <= k <= rot,
            rot <= deltas.len(),
            n == deltas.len() + 1,
            sorted_arr.len() == n as int,
            nums.len() == (high_len + k) as int,
            high_len == (n - rot) as int,
            forall|k2: int| 0 <= k2 < sorted_arr.len() ==> -10_000 <= #[trigger] sorted_arr[k2] <= 10_000,
            forall|k2: int, l: int| 0 <= k2 < l < sorted_arr.len() ==> sorted_arr[k2] < sorted_arr[l],
            forall|m: int| 0 <= m < high_len as int ==> nums[m] == sorted_arr[rot as int + m],
            forall|m: int| high_len as int <= m < nums.len() ==> nums[m] == sorted_arr[m - high_len as int],
            forall|m: int| 0 <= m < nums.len() ==> -10_000 <= #[trigger] nums[m] <= 10_000,
            forall|m1: int, m2: int| 0 <= m1 < m2 < high_len as int ==> nums[m1] < nums[m2],
            forall|m1: int, m2: int| high_len as int <= m1 < m2 < nums.len() ==> nums[m1] < nums[m2],
        decreases rot - k,
    {
        proof {
            assert(-10_000 <= sorted_arr[k as int] <= 10_000);
            assert forall|m: int| high_len as int <= m < nums.len()
                implies nums[m] < sorted_arr[k as int] by {
                assert(nums[m] == sorted_arr[m - high_len as int]);
                assert((m - high_len as int) < (k as int));
            };
        }

        nums.push(sorted_arr[k]);
        k = k + 1;

        proof {
            assert forall|m: int| high_len as int <= m < nums.len()
                implies nums[m] == sorted_arr[m - high_len as int] by {
                if m < (nums.len() - 1) as int {
                } else {
                    assert(nums[m] == sorted_arr[(k - 1) as int]);
                    assert(m - high_len as int == (k - 1) as int);
                }
            };
            assert forall|m1: int, m2: int| high_len as int <= m1 < m2 < nums.len()
                implies nums[m1] < nums[m2] by {
                if m2 < (nums.len() - 1) as int {
                } else {
                    assert(nums[m1] == sorted_arr[m1 - high_len as int]);
                    assert((m1 - high_len as int) < ((k - 1) as int));
                }
            };
        }
    }

    // Final proof: ord_tuple holds for all pairs
    proof {
        assert(nums.len() == n as int);
        assert(1 <= nums.len() <= 5_000);

        assert forall|i2: int, j2: int| 0 <= i2 < j2 < nums.len() implies
            #[trigger] ord_tuple(&rot_tuple(&nums, i2), &rot_tuple(&nums, j2))
        by {
            let hl = high_len as int;

            if i2 < hl && j2 < hl {
                // Both in the high segment
                assert(nums[i2] == sorted_arr[rot as int + i2]);
                assert(nums[j2] == sorted_arr[rot as int + j2]);
                assert(nums[0] == sorted_arr[rot as int]);
                assert(rot as int + i2 < rot as int + j2);
                assert(sorted_arr[rot as int + i2] < sorted_arr[rot as int + j2]);

                // Both values >= nums[0], so rot_tuple gives (false, _)
                if i2 > 0 {
                    assert(rot as int + i2 > rot as int);
                    assert(sorted_arr[rot as int + i2] > sorted_arr[rot as int]);
                    assert(nums[i2] > nums[0]);
                }
                assert(!(nums[i2] < nums[0]));

                assert(rot as int + j2 > rot as int);
                assert(sorted_arr[rot as int + j2] > sorted_arr[rot as int]);
                assert(!(nums[j2] < nums[0]));

                // ord_tuple((false, nums[i2]), (false, nums[j2])) = nums[i2] < nums[j2]
                assert(nums[i2] < nums[j2]);
            } else if i2 >= hl && j2 >= hl {
                // Both in the low segment
                assert(nums[i2] == sorted_arr[i2 - hl]);
                assert(nums[j2] == sorted_arr[j2 - hl]);
                assert(nums[0] == sorted_arr[rot as int]);

                assert((i2 - hl) < (rot as int));
                assert(sorted_arr[i2 - hl] < sorted_arr[rot as int]);
                assert(nums[i2] < nums[0]);

                assert((j2 - hl) < (rot as int));
                assert(sorted_arr[j2 - hl] < sorted_arr[rot as int]);
                assert(nums[j2] < nums[0]);

                assert(i2 - hl < j2 - hl);
                assert(sorted_arr[i2 - hl] < sorted_arr[j2 - hl]);
                assert(nums[i2] < nums[j2]);

                // ord_tuple((true, nums[i2]), (true, nums[j2])) = nums[i2] < nums[j2]
            } else {
                // i2 in high segment, j2 in low segment
                assert(i2 < hl);
                assert(j2 >= hl);
                assert(nums[0] == sorted_arr[rot as int]);

                // nums[i2] >= nums[0], so rot_tuple = (false, _)
                if i2 > 0 {
                    assert(nums[i2] == sorted_arr[rot as int + i2]);
                    assert(rot as int + i2 > rot as int);
                    assert(sorted_arr[rot as int + i2] > sorted_arr[rot as int]);
                }
                assert(!(nums[i2] < nums[0]));

                // nums[j2] < nums[0], so rot_tuple = (true, _)
                assert(nums[j2] == sorted_arr[j2 - hl]);
                assert((j2 - hl) < (rot as int));
                assert(sorted_arr[j2 - hl] < sorted_arr[rot as int]);
                assert(nums[j2] < nums[0]);

                // ord_tuple((false, _), (true, _)): different bools, !false && true = true
            }
        };
    }

    // Target mutations
    let mutated_target: i32 =
        if mutation_kind == 1 {
            nums[0]
        } else if mutation_kind == 2 {
            let last = nums.len() - 1;
            nums[last]
        } else if mutation_kind == 3 {
            let mid = nums.len() / 2;
            nums[mid]
        } else if mutation_kind == 4 {
            -10_000
        } else if mutation_kind == 5 {
            10_000
        } else if mutation_kind == 6 && nums.len() >= 2 {
            if nums[1] - nums[0] > 1 {
                (nums[0] + 1) as i32
            } else {
                target
            }
        } else {
            target
        };

    (nums, mutated_target)
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

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(1, max_d as i64) as i32);
    }
    deltas
}

fn rotated_to_params(arr: &[i32]) -> (Vec<i32>, i32, usize) {
    if arr.len() <= 1 {
        return (vec![], arr[0], 0);
    }
    let mut bp = arr.len();
    for i in 0..arr.len() - 1 {
        if arr[i] > arr[i + 1] {
            bp = i;
            break;
        }
    }
    if bp == arr.len() {
        let mut deltas = Vec::new();
        for i in 1..arr.len() {
            deltas.push(arr[i] - arr[i - 1]);
        }
        return (deltas, arr[0], 0);
    }
    let mut sorted = Vec::new();
    for i in bp + 1..arr.len() {
        sorted.push(arr[i]);
    }
    for i in 0..=bp {
        sorted.push(arr[i]);
    }
    let base = sorted[0];
    let rot = arr.len() - bp - 1;
    let mut deltas = Vec::new();
    for i in 1..sorted.len() {
        deltas.push(sorted[i] - sorted[i - 1]);
    }
    (deltas, base, rot)
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(33);
    let count: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut total = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $rot:expr, $target:expr, $mk:expr) => {
            if total < count {
                let d: Vec<i32> = $deltas;
                let b: i32 = $base;
                let r: usize = $rot;
                let t: i32 = $target;
                let mk: u8 = $mk;
                let (nums_out, target_out) = generate_test_case(&d, b, r, t, mk);
                let result = Solution::search(nums_out.clone(), target_out);
                let line = json!({
                    "input": {"nums": nums_out, "target": target_out},
                    "output": result
                }).to_string();
                if seen.insert(line.clone()) {
                    writeln!(out, "{}", line).unwrap();
                    total += 1;
                }
            }
        };
    }

    // ---- Example inputs from description.md ----
    {
        let (d, b, r) = rotated_to_params(&[4, 5, 6, 7, 0, 1, 2]);
        emit!(d.clone(), b, r, 0, 0);
        emit!(d.clone(), b, r, 3, 0);
    }
    {
        let (d, b, r) = rotated_to_params(&[1]);
        emit!(d.clone(), b, r, 0, 0);
    }

    // ---- Single element, all mutations ----
    for mk in 0u8..=6 {
        emit!(vec![], 0, 0, 5, mk);
        emit!(vec![], -10000, 0, 0, mk);
        emit!(vec![], 10000, 0, 0, mk);
        emit!(vec![], 1, 0, 1, mk);
    }

    // ---- Two elements, no rotation, all mutations ----
    for mk in 0u8..=6 {
        emit!(vec![1], 0, 0, 0, mk);
        emit!(vec![100], -50, 0, 50, mk);
    }

    // ---- Two elements, rotated, all mutations ----
    for mk in 0u8..=6 {
        emit!(vec![1], 0, 1, 0, mk);
        emit!(vec![100], -50, 1, 50, mk);
    }

    // ---- Small sorted arrays with various rotations ----
    for rot in 0..5 {
        for mk in 0u8..=6 {
            emit!(vec![2, 2, 2, 2], 1, rot, 5, mk);
        }
    }

    // ---- Near boundaries ----
    for mk in 0u8..=6 {
        emit!(vec![1, 1, 1, 1, 1], 9995, 0, 9997, mk);
        emit!(vec![1, 1, 1, 1, 1], -10000, 0, -9998, mk);
        emit!(vec![1, 1, 1, 1, 1], 9995, 3, 9997, mk);
        emit!(vec![1, 1, 1, 1, 1], -10000, 3, -9998, mk);
    }

    // ---- Consecutive spanning zero, with rotation ----
    for mk in [0u8, 1, 2, 3, 4, 5, 6] {
        emit!(vec![1; 20], -10, 10, 0, mk);
        emit!(vec![1; 20], -10, 0, 0, mk);
        emit!(vec![1; 20], -10, 15, 0, mk);
    }

    // ---- Random tiny arrays (2-5 elements), all rotations, all mutations ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(2, 5);
        let max_d = std::cmp::max(1, (20000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100));
        let total_d: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10000i64, 10000 - total_d);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let t = rng.gen_range_i64(-10000, 10000) as i32;
        for rot in 0..n {
            for mk in 0u8..=6 {
                emit!(deltas.clone(), base, rot, t, mk);
            }
        }
    }

    // ---- Random medium arrays (10-200 elements), random rotation, random mutation ----
    for _ in 0..10 {
        let n = rng.gen_range_usize(10, 200);
        let max_d = std::cmp::max(1, (20000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total_d: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10000i64, 10000 - total_d);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let t = rng.gen_range_i64(-10000, 10000) as i32;
        let rot = rng.gen_range_usize(0, n - 1);
        let mk = (rng.gen_range_usize(0, 6)) as u8;
        emit!(deltas.clone(), base, rot, t, mk);
        emit!(deltas.clone(), base, 0, t, mk);
    }

    // ---- Random large arrays (500-2000 elements), delta=1 ----
    for _ in 0..4 {
        let n = rng.gen_range_usize(500, 2000);
        let deltas = vec![1i32; n - 1];
        let total_d = (n - 1) as i64;
        let hi = std::cmp::min(10000i64, 10000 - total_d);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let t = rng.gen_range_i64(-10000, 10000) as i32;
        let rot = rng.gen_range_usize(0, n - 1);
        for mk in [0u8, 1, 2, 3, 4, 5] {
            emit!(deltas.clone(), base, rot, t, mk);
        }
    }

    // ---- Maximum size (5000 elements), delta=1 ----
    {
        let deltas = vec![1i32; 4999];
        let base = -2500i32;
        for rot in [0, 1, 2499, 4999] {
            for mk in [0u8, 1, 2, 3, 4, 5] {
                emit!(deltas.clone(), base, rot, 0, mk);
            }
        }
    }

    // ---- Large deltas, small arrays ----
    for _ in 0..3 {
        let n = rng.gen_range_usize(2, 10);
        let max_d = std::cmp::max(1, (20000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 2000));
        let total_d: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10000i64, 10000 - total_d);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let t = rng.gen_range_i64(-10000, 10000) as i32;
        let rot = rng.gen_range_usize(0, n - 1);
        emit!(deltas.clone(), base, rot, t, 6);
        emit!(deltas.clone(), base, rot, t, 0);
    }

    // ---- Fill remaining with diverse random cases ----
    while total < count {
        let n = match rng.gen_range_usize(0, 4) {
            0 => rng.gen_range_usize(1, 5),
            1 => rng.gen_range_usize(5, 20),
            2 => rng.gen_range_usize(20, 200),
            3 => rng.gen_range_usize(200, 1000),
            _ => rng.gen_range_usize(1000, 5000),
        };
        let max_d = std::cmp::max(1, (20000 / std::cmp::max(n, 1)) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 100));
        let total_d: i64 = deltas.iter().map(|d| *d as i64).sum();
        let hi = std::cmp::min(10000i64, 10000 - total_d);
        let base = if hi < -10000 { -10000i32 } else { rng.gen_range_i64(-10000, hi) as i32 };
        let target = rng.gen_range_i64(-10000, 10000) as i32;
        let rot = if n <= 1 { 0 } else { rng.gen_range_usize(0, n - 1) };
        let mk = rng.gen_range_usize(0, 6) as u8;
        emit!(deltas, base, rot, target, mk);
    }
}
