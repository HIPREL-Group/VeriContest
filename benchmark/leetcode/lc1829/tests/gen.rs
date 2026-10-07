use vstd::prelude::*;

verus! {

pub open spec fn mask_for(mb: i32) -> i32 {
    !(!0i32 << (mb as u32))
}

pub open spec fn sum_deltas(deltas: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 { 0 }
    else { sum_deltas(deltas, end - 1) + deltas[end - 1] as int }
}

proof fn lemma_sum_deltas_mono(deltas: Seq<i32>, a: int, b: int)
    requires
        0 <= a <= b <= deltas.len(),
        forall|i: int| 0 <= i < deltas.len() ==> #[trigger] deltas[i] >= 0i32,
    ensures
        sum_deltas(deltas, a) <= sum_deltas(deltas, b),
    decreases b - a,
{
    if a < b {
        lemma_sum_deltas_mono(deltas, a, b - 1);
    }
}

proof fn mask_nonneg(mb: i32)
    requires
        1 <= mb <= 20,
    ensures
        mask_for(mb) >= 0i32,
{
    assert(!(!0i32 << (mb as u32)) >= 0i32) by(bit_vector)
        requires 1 <= mb <= 20;
}

pub fn generate_test_case(
    deltas: &Vec<i32>,
    base: i32,
    maximum_bit: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= deltas.len() + 1 <= 100_000,
        1 <= maximum_bit <= 20,
        0 <= base,
        forall|i: int| 0 <= i < deltas.len() ==> 0 <= #[trigger] deltas[i],
        base as int + sum_deltas(deltas@, deltas.len() as int) <= mask_for(maximum_bit) as int,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 20,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= mask_for(result.1),
        forall|i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
{
    proof { mask_nonneg(maximum_bit); }

    proof {
        lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        assert(base as int <= mask_for(maximum_bit) as int) by {
            assert(sum_deltas(deltas@, deltas.len() as int) >= 0);
        };
    }

    let mut nums: Vec<i32> = Vec::new();
    nums.push(base);

    let mut i: usize = 0;
    while i < deltas.len()
        invariant
            0 <= i <= deltas.len(),
            nums.len() == i + 1,
            1 <= maximum_bit <= 20,
            0 <= base,
            deltas.len() + 1 <= 100_000,
            forall|k: int| 0 <= k < deltas.len() ==> 0 <= #[trigger] deltas[k],
            base as int + sum_deltas(deltas@, deltas.len() as int) <= mask_for(maximum_bit) as int,
            mask_for(maximum_bit) >= 0i32,
            forall|k: int| 0 <= k <= i as int ==>
                #[trigger] nums[k] as int == base as int + sum_deltas(deltas@, k),
            forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= mask_for(maximum_bit),
            forall|k: int, l: int| 0 <= k < l < nums.len() ==> nums[k] <= nums[l],
        decreases deltas.len() - i,
    {
        proof {
            lemma_sum_deltas_mono(deltas@, (i + 1) as int, deltas.len() as int);
        }

        let next = nums[i] + deltas[i];

        proof {
            assert(next as int == base as int + sum_deltas(deltas@, (i + 1) as int));

            // next is in bounds [0, mask_for(maximum_bit)]
            assert(next as int <= mask_for(maximum_bit) as int) by {
                assert(base as int + sum_deltas(deltas@, (i + 1) as int)
                    <= base as int + sum_deltas(deltas@, deltas.len() as int));
            };
            assert(next as int >= 0) by {
                lemma_sum_deltas_mono(deltas@, 0, (i + 1) as int);
            };

            // next >= nums[i] because deltas[i] >= 0
            assert(next >= nums[i as int]);
        }

        let ghost old_len = nums.len();
        nums.push(next);
        i = i + 1;

        proof {
            assert forall|k: int, l: int| 0 <= k < l < nums.len() implies nums[k] <= nums[l] by {
                if l < old_len as int {
                } else {
                    assert(l == old_len as int);
                    assert(nums[l] == next);
                }
            };
        }
    }

    if mutation_kind == 1 {
        // All zeros
        let mut zeros: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                zeros.len() == j,
                nums.len() <= 100_000,
                1 <= maximum_bit <= 20,
                mask_for(maximum_bit) >= 0i32,
                forall|k: int| 0 <= k < zeros.len() ==> #[trigger] zeros[k] == 0i32,
            decreases nums.len() - j,
        {
            zeros.push(0i32);
            j = j + 1;
        }
        proof {
            assert forall|k: int| 0 <= k < zeros.len() implies 0 <= #[trigger] zeros[k] <= mask_for(maximum_bit) by {
                assert(zeros[k] == 0i32);
            };
            assert forall|k: int, l: int| 0 <= k < l < zeros.len() implies zeros[k] <= zeros[l] by {
                assert(zeros[k] == 0i32);
                assert(zeros[l] == 0i32);
            };
        }
        (zeros, maximum_bit)
    } else if mutation_kind == 2 {
        // Single element [base]
        let mut single: Vec<i32> = Vec::new();
        single.push(base);
        proof {
            lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
            assert(0 <= base <= mask_for(maximum_bit)) by {
                assert(base as int + sum_deltas(deltas@, deltas.len() as int) <= mask_for(maximum_bit) as int);
                assert(sum_deltas(deltas@, deltas.len() as int) >= 0);
            };
        }
        (single, maximum_bit)
    } else if mutation_kind == 3 {
        // All same value (base)
        let mut same: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        proof {
            lemma_sum_deltas_mono(deltas@, 0, deltas.len() as int);
        }
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                same.len() == j,
                nums.len() <= 100_000,
                1 <= maximum_bit <= 20,
                mask_for(maximum_bit) >= 0i32,
                0 <= base <= mask_for(maximum_bit),
                forall|k: int| 0 <= k < same.len() ==> #[trigger] same[k] == base,
            decreases nums.len() - j,
        {
            same.push(base);
            j = j + 1;
        }
        proof {
            assert forall|k: int| 0 <= k < same.len() implies 0 <= #[trigger] same[k] <= mask_for(maximum_bit) by {
                assert(same[k] == base);
            };
            assert forall|k: int, l: int| 0 <= k < l < same.len() implies same[k] <= same[l] by {
                assert(same[k] == base);
                assert(same[l] == base);
            };
        }
        (same, maximum_bit)
    } else if mutation_kind == 4 {
        // All max value (mask_for(maximum_bit))
        let mask = !(!0i32 << (maximum_bit as u32));
        let mut maxes: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nums.len()
            invariant
                0 <= j <= nums.len(),
                maxes.len() == j,
                nums.len() <= 100_000,
                1 <= maximum_bit <= 20,
                mask == mask_for(maximum_bit),
                mask >= 0i32,
                forall|k: int| 0 <= k < maxes.len() ==> #[trigger] maxes[k] == mask,
            decreases nums.len() - j,
        {
            maxes.push(mask);
            j = j + 1;
        }
        proof {
            assert forall|k: int| 0 <= k < maxes.len() implies 0 <= #[trigger] maxes[k] <= mask_for(maximum_bit) by {
                assert(maxes[k] == mask);
            };
            assert forall|k: int, l: int| 0 <= k < l < maxes.len() implies maxes[k] <= maxes[l] by {
                assert(maxes[k] == mask);
                assert(maxes[l] == mask);
            };
        }
        (maxes, maximum_bit)
    } else {
        // Identity: return constructed sorted array
        (nums, maximum_bit)
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

struct Solution;
include!("../code.rs");

fn mask_value(mb: i32) -> i32 {
    !(!0i32 << (mb as u32))
}

fn random_deltas(rng: &mut Rng, n: usize, max_d: i32) -> Vec<i32> {
    let mut deltas = Vec::new();
    for _ in 0..n.saturating_sub(1) {
        deltas.push(rng.gen_range_i64(0, max_d as i64) as i32);
    }
    deltas
}

fn sorted_to_deltas(vals: &[i32]) -> Vec<i32> {
    let mut deltas = Vec::new();
    for i in 1..vals.len() {
        deltas.push(vals[i] - vals[i - 1]);
    }
    deltas
}

fn main() {
    use std::io::Write;
    use std::collections::HashSet;

    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(1829);
    let goal: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    macro_rules! emit {
        ($deltas:expr, $base:expr, $mb:expr, $mk:expr) => {{
            let deltas_v: Vec<i32> = $deltas;
            let base_v: i32 = $base;
            let mb_v: i32 = $mb;
            let mk_v: u8 = $mk;
            let (nums, maximum_bit) = generate_test_case(&deltas_v, base_v, mb_v, mk_v);
            let result = Solution::get_maximum_xor(nums.clone(), maximum_bit);
            let key = format!("{:?}:{}", nums, maximum_bit);
            if seen.insert(key) {
                writeln!(out, "{}", json!({
                    "input": {"nums": nums, "maximum_bit": maximum_bit},
                    "output": result
                })).unwrap();
                count += 1;
            }
        }};
    }

    // ---- LeetCode examples ----
    emit!(sorted_to_deltas(&[0, 1, 1, 3]), 0, 2, 0);
    emit!(sorted_to_deltas(&[2, 3, 4, 7]), 2, 3, 0);
    emit!(sorted_to_deltas(&[0, 1, 2, 2, 5, 7]), 0, 3, 0);

    // ---- Single element with all mutations ----
    for mk in 0u8..=4 {
        emit!(vec![], 0, 1, mk);
        emit!(vec![], 0, 10, mk);
        emit!(vec![], 0, 20, mk);
        emit!(vec![], 1, 1, mk);
    }

    // ---- Two elements, all mutations ----
    for mk in 0u8..=4 {
        emit!(vec![0], 0, 5, mk);
        emit!(vec![1], 0, 5, mk);
        emit!(vec![3], 0, 3, mk);
    }

    // ---- Small arrays with constant deltas, all mutations ----
    for mk in 0u8..=4 {
        emit!(vec![1, 1, 1, 1], 0, 5, mk);
        emit!(vec![0, 0, 0, 0], 3, 4, mk);
    }

    // ---- Boundary maximum_bit values ----
    for mb in [1i32, 2, 5, 10, 15, 20] {
        let mask = mask_value(mb);
        emit!(vec![], 0, mb, 0);
        emit!(vec![], mask, mb, 0);
        emit!(vec![0, 0, 0], 0, mb, 0);
        if mask >= 3 {
            emit!(vec![1, 1], 0, mb, 0);
        }
    }

    // ---- Random tiny arrays (2-5 elements), all mutations ----
    while count < goal / 3 {
        let mb = rng.gen_range_i64(1, 20) as i32;
        let mask = mask_value(mb) as i64;
        let n = rng.gen_range_usize(2, 5);
        let max_d = std::cmp::max(0, mask / n as i64);
        if max_d < 0 { continue; }
        let base = rng.gen_range_i64(0, std::cmp::max(0, mask / 2)) as i32;
        let remaining = mask - base as i64;
        if remaining < 0 { continue; }
        let d_max = std::cmp::min(max_d, std::cmp::max(0, remaining / std::cmp::max(1, n as i64 - 1)));
        let deltas = random_deltas(&mut rng, n, std::cmp::max(0, d_max as i32));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        if base as i64 + total > mask { continue; }
        for mk in 0u8..=4 {
            emit!(deltas.clone(), base, mb, mk);
        }
    }

    // ---- Random medium arrays (10-200 elements), random mutations ----
    while count < 2 * goal / 3 {
        let mb = rng.gen_range_i64(1, 20) as i32;
        let mask = mask_value(mb) as i64;
        let n = rng.gen_range_usize(10, 200);
        let base = rng.gen_range_i64(0, std::cmp::max(0, mask / 2)) as i32;
        let remaining = mask - base as i64;
        if remaining < 0 { continue; }
        let d_max = std::cmp::max(0, remaining / std::cmp::max(1, n as i64 - 1));
        let deltas = random_deltas(&mut rng, n, std::cmp::max(0, std::cmp::min(d_max, i32::MAX as i64) as i32));
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        if base as i64 + total > mask { continue; }
        let mk = (rng.gen_range_usize(0, 4)) as u8;
        emit!(deltas.clone(), base, mb, mk);
        emit!(deltas.clone(), base, mb, 0);
    }

    // ---- Random large arrays (500-5000 elements), delta=0 or delta=1 ----
    let mut _attempts_0 = 0usize;
    while count < goal {
        _attempts_0 += 1; if _attempts_0 > 10000 { break; }
        let mb = rng.gen_range_i64(5, 20) as i32;
        let mask = mask_value(mb) as i64;
        let n = rng.gen_range_usize(500, std::cmp::min(5000, mask as usize + 1));
        let base = rng.gen_range_i64(0, std::cmp::max(0, mask - n as i64 + 1)) as i32;
        let deltas: Vec<i32> = (0..n.saturating_sub(1)).map(|_| {
            if rng.gen_range_usize(0, 1) == 0 { 0 } else { 1 }
        }).collect();
        let total: i64 = deltas.iter().map(|d| *d as i64).sum();
        if base as i64 + total > mask { continue; }
        let mk = rng.gen_range_usize(0, 4) as u8;
        emit!(deltas.clone(), base, mb, mk);
    }

    eprintln!("Generated {} test cases -> {:?}", count, out_path);
}
