use vstd::prelude::*;

verus! {

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

pub open spec fn is_rotation_point(nums: Seq<i32>, k: int) -> bool {
    0 <= k < nums.len()
    && (forall |a: int, b: int| k <= a < b < nums.len() ==> nums[a] < nums[b])
    && (forall |a: int, b: int| 0 <= a < b < k ==> nums[a] < nums[b])
    && (k == 0 || forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() ==> nums[a] > nums[b])
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    rot: usize,
    mutation_kind: u8,
) -> (result: Vec<i32>)
    requires
        deltas.len() >= 0,
        deltas.len() + 1 <= 5000,
        -5000 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 1 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= 5000,
        rot <= deltas.len(),
    ensures
        1 <= result.len() <= 5000,
        forall |i: int| 0 <= i < result.len() ==> -5000 <= #[trigger] result[i] <= 5000,
        forall |i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
        exists |k: int| is_rotation_point(result@, k),
{
    let n: usize = deltas.len() + 1;

    // Build sorted array via cumulative sums
    let mut sorted: Vec<i32> = Vec::new();

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        // base <= base + sum_deltas(..., n) <= 5000
    }

    sorted.push(base);

    // Prove base <= 5000 for the initial invariant
    assert(sorted[0] == base);
    assert(base as int <= base as int + sum_deltas(deltas@, deltas.len() as int));
    assert(base <= 5000i32);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            sorted.len() == i + 1,
            deltas.len() + 1 <= 5000,
            -5000 <= base,
            forall|k: int| 0 <= k < deltas.len() ==> #[trigger] deltas[k] >= 1i32,
            base as int + sum_deltas(deltas@, deltas.len() as int) <= 5000,
            forall|k: int| 0 <= k <= i as int ==>
                (#[trigger] sorted[k]) as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < sorted.len() ==> -5000 <= sorted[k],
            forall|k: int| 0 <= k < sorted.len() ==> #[trigger] sorted[k] <= 5000,
            forall|k: int, l: int| 0 <= k < l < sorted.len() ==> sorted[k] < sorted[l],
        decreases deltas.len() - i,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = sorted[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));
            lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);

            assert forall|k: int| 0 <= k < sorted.len() implies sorted[k] < next by {
                assert(sorted[k] as int == base as int + sum_deltas(deltas@, k));
                lemma_sum_deltas_strict(deltas@, k, (i + 1) as int);
            };
        }

        let ghost old_len = sorted.len();
        sorted.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < sorted.len() implies sorted[k] < sorted[l] by {
                if l < old_len as int {
                } else {
                    assert(sorted[l] == next);
                }
            };
        }
    }

    assert(sorted.len() == n);

    // Compute effective rotation
    let eff_rot: usize =
        if mutation_kind == 1 {
            0
        } else if mutation_kind == 2 {
            n - 1
        } else {
            rot
        };

    if eff_rot == 0 {
        proof {
            assert(is_rotation_point(sorted@, 0int));
        }
        sorted
    } else {
        let split = n - eff_rot;
        let mut result: Vec<i32> = Vec::new();

        // Copy sorted[split..n]
        let mut j: usize = split;
        while j < n
            invariant
                split <= j <= n,
                result.len() == (j - split) as int,
                n == sorted.len(),
                1 <= n <= 5000,
                0 < eff_rot <= deltas.len(),
                split == n - eff_rot,
                forall|k: int| 0 <= k < sorted.len() ==> -5000 <= sorted[k],
                forall|k: int| 0 <= k < sorted.len() ==> #[trigger] sorted[k] <= 5000,
                forall|k: int, l: int| 0 <= k < l < sorted.len() ==> sorted[k] < sorted[l],
                forall|k: int| 0 <= k < result.len() ==>
                    (#[trigger] result[k]) == sorted[split as int + k],
            decreases n - j,
        {
            result.push(sorted[j]);
            j = j + 1;
        }

        assert(result.len() == eff_rot as int);

        // Copy sorted[0..split]
        let ghost phase1_len = result.len();
        let mut j2: usize = 0;
        while j2 < split
            invariant
                0 <= j2 <= split,
                result.len() == eff_rot as int + j2 as int,
                phase1_len == eff_rot as int,
                n == sorted.len(),
                1 <= n <= 5000,
                0 < eff_rot <= deltas.len(),
                split == n - eff_rot,
                forall|k: int| 0 <= k < sorted.len() ==> -5000 <= sorted[k],
                forall|k: int| 0 <= k < sorted.len() ==> #[trigger] sorted[k] <= 5000,
                forall|k: int, l: int| 0 <= k < l < sorted.len() ==> sorted[k] < sorted[l],
                forall|k: int| 0 <= k < eff_rot as int ==>
                    (#[trigger] result[k]) == sorted[split as int + k],
                forall|k: int| 0 <= k < j2 as int ==>
                    (#[trigger] result[eff_rot as int + k]) == sorted[k],
            decreases split - j2,
        {
            result.push(sorted[j2]);
            j2 = j2 + 1;
        }

        assert(result.len() == n as int);

        proof {
            let r = eff_rot as int;
            let s = split as int;

            // Establish mapping for all indices
            assert forall|idx: int| r <= idx < n as int implies result[idx] == sorted[idx - r] by {
                // idx = r + k where k = idx - r, and 0 <= k < j2 == split
                assert(result[r + (idx - r)] == sorted[idx - r]);
            };

            assert forall|idx: int| 0 <= idx < r implies result[idx] == sorted[s + idx] by {
                // From phase 1 invariant
            };

            // Elements from r..n are ascending (from sorted[0..split])
            assert forall|a: int, b: int| r <= a < b < n as int implies result[a] < result[b] by {
                assert(result[a] == sorted[a - r]);
                assert(result[b] == sorted[b - r]);
            };

            // Elements from 0..r are ascending (from sorted[split..n])
            assert forall|a: int, b: int| 0 <= a < b < r implies result[a] < result[b] by {
                assert(result[a] == sorted[s + a]);
                assert(result[b] == sorted[s + b]);
            };

            // Elements before r > elements from r onward
            assert forall|a: int, b: int| 0 <= a < r && r <= b < n as int implies result[a] > result[b] by {
                assert(result[a] == sorted[s + a]);
                assert(result[b] == sorted[b - r]);
                assert(0 <= b - r);
                assert(b - r < s);
                assert(s + a >= s);
                assert(s + a < n as int);
            };

            assert(is_rotation_point(result@, r));

            // Uniqueness via strict ordering
            assert forall|ii: int, jj: int| 0 <= ii < jj < result.len() implies result[ii] != result[jj] by {
                if ii < r && jj < r {
                    // both in upper part: ascending
                } else if ii >= r && jj >= r {
                    // both in lower part: ascending
                } else {
                    // ii < r, jj >= r: result[ii] > result[jj]
                }
            };
        }

        result
    }
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

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 { args[1].parse().unwrap_or(153) } else { 153 };
    let goal: usize = if args.len() > 2 { args[2].parse().unwrap_or(100) } else { 100 };

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($nums:expr) => {
            let nums: Vec<i32> = $nums;
            let key = format!("{:?}", nums);
            if !seen.contains(&key) {
                seen.insert(key);
                let result = Solution::find_min(nums.clone());
                let line = json!({"input": {"nums": nums}, "output": result});
                writeln!(out, "{}", line).unwrap();
                count += 1;
            }
        };
    }

    // Example test cases from description.md
    emit!(vec![3, 4, 5, 1, 2]);
    emit!(vec![4, 5, 6, 7, 0, 1, 2]);
    emit!(vec![11, 13, 15, 17]);

    // Edge cases: single element
    emit!(generate_test_case(&vec![], 0, 0, 0));
    emit!(generate_test_case(&vec![], -5000, 0, 0));
    emit!(generate_test_case(&vec![], 5000, 0, 0));

    // Two elements, all mutation kinds
    for mk in 0u8..=2 {
        emit!(generate_test_case(&vec![1], -5000, 1, mk));
        emit!(generate_test_case(&vec![1], 0, 1, mk));
        emit!(generate_test_case(&vec![10], 0, 1, mk));
    }

    // Small arrays (3-5 elements), all mutation kinds
    for mk in 0u8..=2 {
        emit!(generate_test_case(&vec![1, 1, 1, 1], -2, 2, mk));
        emit!(generate_test_case(&vec![2, 2, 2, 2], 1, 3, mk));
        emit!(generate_test_case(&vec![1, 2, 3], 0, 1, mk));
    }

    // Near boundaries
    emit!(generate_test_case(&vec![1, 1, 1, 1, 1, 1, 1, 1, 1], 4990, 5, 0));
    emit!(generate_test_case(&vec![1, 1, 1, 1, 1, 1, 1, 1, 1], -5000, 5, 0));
    emit!(generate_test_case(&vec![1, 1, 1, 1, 1, 1, 1, 1, 1], -5000, 0, 1));

    // Random tiny arrays (1-5 elements), all mutations
    for _ in 0..5 {
        let n = rng.gen_range_usize(2, 5);
        let deltas = random_deltas(&mut rng, n, 3);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(5000i64, 5000 - total);
        let base = if max_base < -5000 { -5000i32 } else { rng.gen_range_i64(-5000, max_base) as i32 };
        let rot = rng.gen_range_usize(0, n - 1);
        for mk in 0u8..=2 {
            emit!(generate_test_case(&deltas, base, rot, mk));
        }
    }

    // Random small arrays (5-10 elements)
    for _ in 0..5 {
        let n = rng.gen_range_usize(5, 10);
        let deltas = random_deltas(&mut rng, n, 5);
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(5000i64, 5000 - total);
        let base = if max_base < -5000 { -5000i32 } else { rng.gen_range_i64(-5000, max_base) as i32 };
        let rot = rng.gen_range_usize(0, n - 1);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(generate_test_case(&deltas, base, rot, mk));
    }

    // Random medium arrays (10-100 elements)
    for _ in 0..8 {
        let n = rng.gen_range_usize(10, 100);
        let max_d = std::cmp::max(1, (10000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 50));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(5000i64, 5000 - total);
        let base = if max_base < -5000 { -5000i32 } else { rng.gen_range_i64(-5000, max_base) as i32 };
        let rot = rng.gen_range_usize(0, n - 1);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(generate_test_case(&deltas, base, rot, mk));
    }

    // Random large arrays (100-1000 elements)
    for _ in 0..5 {
        let n = rng.gen_range_usize(100, 1000);
        let max_d = std::cmp::max(1, (10000 / n) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 10));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(5000i64, 5000 - total);
        let base = if max_base < -5000 { -5000i32 } else { rng.gen_range_i64(-5000, max_base) as i32 };
        let rot = rng.gen_range_usize(0, n - 1);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(generate_test_case(&deltas, base, rot, mk));
    }

    // Max-size arrays (up to 5000 elements), delta=1
    for _ in 0..3 {
        let n = rng.gen_range_usize(1000, 4999);
        let deltas = vec![1i32; n - 1];
        let total = (n - 1) as i64;
        let max_base = std::cmp::min(5000i64, 5000 - total);
        let base = if max_base < -5000 { -5000i32 } else { rng.gen_range_i64(-5000, max_base) as i32 };
        let rot = rng.gen_range_usize(0, n - 1);
        for mk in [0u8, 1, 2] {
            emit!(generate_test_case(&deltas, base, rot, mk));
        }
    }

    // Maximum size 5000, delta=1
    {
        let deltas = vec![1i32; 4999];
        let base = -2500i32;
        emit!(generate_test_case(&deltas, base, 2500, 0));
        emit!(generate_test_case(&deltas, base, 0, 1));
        emit!(generate_test_case(&deltas, base, 4999, 2));
    }

    // Fill remaining with random sizes and random mutations
    while count < goal {
        let n = rng.gen_range_usize(2, 500);
        let max_d = std::cmp::max(1, (10000 / std::cmp::max(n, 1)) as i32);
        let deltas = random_deltas(&mut rng, n, std::cmp::min(max_d, 20));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        let max_base = std::cmp::min(5000i64, 5000 - total);
        let base = if max_base < -5000 { -5000i32 } else { rng.gen_range_i64(-5000, max_base) as i32 };
        let rot = rng.gen_range_usize(0, n - 1);
        let mk = rng.gen_range_usize(0, 2) as u8;
        emit!(generate_test_case(&deltas, base, rot, mk));
    }
}
