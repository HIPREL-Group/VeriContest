use vstd::prelude::*;

verus! {

pub open spec fn ord_tuple_spec(small: (bool, i32), big: (bool, i32)) -> bool {
    if small.0 != big.0 {
        !small.0 && big.0
    } else {
        small.1 < big.1
    }
}

pub open spec fn rot_tuple_spec(nums: Seq<i32>, i: int) -> (bool, i32) {
    if 0 <= i < nums.len() {
        (nums[i] < nums[0], nums[i])
    } else {
        (false, 0)
    }
}

// We construct the rotated array by taking sorted values v[0] < v[1] < ... < v[n-1]
// and a rotation point k in [0, n). The resulting array is:
//   [v[k], v[k+1], ..., v[n-1], v[0], v[1], ..., v[k-1]]
// Note: k == 0 gives the original sorted array (no rotation), which is also
// a valid case per the specification (since rot_tuple compares against nums[0]).

pub fn generate_test_case(
    sorted_vals: &Vec<i32>,
    k: usize,
    target: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= sorted_vals.len() <= 5_000,
        k < sorted_vals.len(),
        forall|i: int| 0 <= i < sorted_vals.len() ==> -10_000 <= #[trigger] sorted_vals[i] <= 10_000,
        forall|i: int, j: int| 0 <= i < j < sorted_vals.len() ==> sorted_vals[i] < sorted_vals[j],
        -10_000 <= target <= 10_000,
    ensures
        ({
            let nums = result.0;
            let t = result.1;
            &&& 1 <= nums.len() <= 5_000
            &&& t == target
            &&& (forall|i: int| 0 <= i < nums.len() ==> -10_000 <= #[trigger] nums[i] <= 10_000)
            &&& (forall|i: int, j: int|
                0 <= i < j < nums.len() ==> #[trigger] ord_tuple_spec(
                    rot_tuple_spec(nums@, i),
                    rot_tuple_spec(nums@, j),
                ))
            &&& -10_000 <= t <= 10_000
        }),
{
    let n: usize = sorted_vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    // First copy sorted_vals[k..n]
    while pos < n - k
        invariant
            n == sorted_vals.len(),
            k < n,
            0 <= pos <= n - k,
            nums.len() == pos,
            forall|i: int| 0 <= i < pos ==> nums[i] == sorted_vals[k as int + i],
        decreases n - k - pos,
    {
        nums.push(sorted_vals[k + pos]);
        pos = pos + 1;
    }

    // Then copy sorted_vals[0..k]
    let mut pos2: usize = 0;
    while pos2 < k
        invariant
            n == sorted_vals.len(),
            k < n,
            0 <= pos2 <= k,
            nums.len() == (n - k) + pos2,
            forall|i: int| 0 <= i < n - k ==> nums[i] == sorted_vals[k as int + i],
            forall|i: int| 0 <= i < pos2 ==> nums[(n - k) as int + i] == sorted_vals[i],
        decreases k - pos2,
    {
        nums.push(sorted_vals[pos2]);
        pos2 = pos2 + 1;
    }

    proof {
        assert(nums.len() == n);
        // Characterization: for 0 <= i < n-k, nums[i] == sorted_vals[k+i]
        // for n-k <= i < n,   nums[i] == sorted_vals[i - (n-k)]
        assert forall|i: int| 0 <= i < nums.len() implies -10_000 <= #[trigger] nums[i] <= 10_000 by {
            if i < (n - k) as int {
                assert(nums[i] == sorted_vals[k as int + i]);
            } else {
                assert(nums[i] == sorted_vals[i - (n - k) as int]);
            }
        }

        // nums[0] == sorted_vals[k]
        assert(nums[0] == sorted_vals[k as int]);

        // Prove the rotation-sorted property
        assert forall|i: int, j: int|
            0 <= i < j < nums.len() implies #[trigger] ord_tuple_spec(
                rot_tuple_spec(nums@, i),
                rot_tuple_spec(nums@, j),
            )
        by {
            let boundary = (n - k) as int;
            // Determine which region i and j are in
            let vi = if i < boundary { sorted_vals[k as int + i] } else { sorted_vals[i - boundary] };
            let vj = if j < boundary { sorted_vals[k as int + j] } else { sorted_vals[j - boundary] };
            assert(nums[i] == vi);
            assert(nums[j] == vj);

            let pivot = sorted_vals[k as int];
            assert(nums[0] == pivot);

            if i < boundary && j < boundary {
                // Both in first segment: values are sorted_vals[k+i] < sorted_vals[k+j]
                // Both are >= pivot (sorted_vals[k])
                assert(k as int + i >= k as int);
                assert(k as int + j > k as int + i);
                assert(sorted_vals[k as int + i] >= pivot);
                assert(sorted_vals[k as int + j] >= pivot);
                // rot tuple: nums[i] < nums[0]? sorted_vals[k+i] < sorted_vals[k]? No (>=)
                assert(!(nums[i] < nums[0]));
                assert(!(nums[j] < nums[0]));
                assert(nums[i] < nums[j]);
            } else if i < boundary && j >= boundary {
                // i in first (>= pivot), j in second (< pivot if k > 0)
                assert(sorted_vals[k as int + i] >= pivot);
                let ji = j - boundary;
                assert(0 <= ji < k as int);
                assert(sorted_vals[ji] < pivot);
                assert(!(nums[i] < nums[0]));
                assert(nums[j] < nums[0]);
            } else {
                // Both in second segment
                assert(i >= boundary && j >= boundary);
                let ii = i - boundary;
                let jj = j - boundary;
                assert(0 <= ii < jj < k as int);
                assert(sorted_vals[ii] < sorted_vals[jj]);
                assert(sorted_vals[ii] < pivot);
                assert(sorted_vals[jj] < pivot);
                assert(nums[i] < nums[0]);
                assert(nums[j] < nums[0]);
                assert(nums[i] < nums[j]);
            }
        }
    }

    (nums, target)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_sorted_distinct(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    // Generate n distinct values in [lo, hi], sorted.
    let span = (hi as i64 - lo as i64 + 1) as usize;
    let nn = if n > span { span } else { n };
    let mut used = std::collections::BTreeSet::new();
    while used.len() < nn {
        let v = rng.gen_range_i32(lo, hi);
        used.insert(v);
    }
    used.into_iter().collect()
}

fn make_sorted_consecutive(start: i32, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(start + i as i32);
    }
    v
}

fn print_json(nums: &[i32], target: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{}}}", target);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 220usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let (sorted, k, target) = match mode {
            0 => {
                // small arrays
                let n = rng.gen_range_usize(1, 5);
                let sv = make_sorted_distinct(&mut rng, n, -10_000, 10_000);
                let k = rng.gen_range_usize(0, sv.len() - 1);
                let tgt = rng.gen_range_i32(-10_000, 10_000);
                (sv, k, tgt)
            }
            1 => {
                // size 1
                let v = rng.gen_range_i32(-10_000, 10_000);
                (vec![v], 0usize, v)
            }
            2 => {
                // large array
                let n = 5_000usize;
                let sv = make_sorted_distinct(&mut rng, n, -10_000, 10_000);
                let k = rng.gen_range_usize(0, sv.len() - 1);
                let tgt = if t % 2 == 0 { sv[rng.gen_range_usize(0, sv.len() - 1)] } else { rng.gen_range_i32(-10_000, 10_000) };
                (sv, k, tgt)
            }
            3 => {
                // consecutive small range
                let n = rng.gen_range_usize(2, 50);
                let start = rng.gen_range_i32(-10_000, 10_000 - n as i32);
                let sv = make_sorted_consecutive(start, n);
                let k = rng.gen_range_usize(0, n - 1);
                let tgt = sv[rng.gen_range_usize(0, n - 1)];
                (sv, k, tgt)
            }
            4 => {
                // target at start (pivot)
                let n = rng.gen_range_usize(2, 200);
                let sv = make_sorted_distinct(&mut rng, n, -10_000, 10_000);
                let k = rng.gen_range_usize(1, sv.len() - 1);
                let tgt = sv[k];
                (sv, k, tgt)
            }
            5 => {
                // target at end
                let n = rng.gen_range_usize(2, 200);
                let sv = make_sorted_distinct(&mut rng, n, -10_000, 10_000);
                let k = rng.gen_range_usize(1, sv.len() - 1);
                // last element of rotated is sv[k-1]
                let tgt = sv[k - 1];
                (sv, k, tgt)
            }
            6 => {
                // no rotation (k=0)
                let n = rng.gen_range_usize(1, 100);
                let sv = make_sorted_distinct(&mut rng, n, -10_000, 10_000);
                let tgt = if t % 2 == 0 && sv.len() > 0 { sv[rng.gen_range_usize(0, sv.len() - 1)] } else { rng.gen_range_i32(-10_000, 10_000) };
                (sv, 0usize, tgt)
            }
            7 => {
                // rotation near middle
                let n = rng.gen_range_usize(10, 500);
                let sv = make_sorted_distinct(&mut rng, n, -10_000, 10_000);
                let k = sv.len() / 2;
                let tgt = rng.gen_range_i32(-10_000, 10_000);
                (sv, k, tgt)
            }
            8 => {
                // target not present (use value not in range likely)
                let n = rng.gen_range_usize(2, 100);
                let sv = make_sorted_distinct(&mut rng, n, -9_000, 9_000);
                let k = rng.gen_range_usize(0, sv.len() - 1);
                let tgt = if t % 2 == 0 { 10_000i32 } else { -10_000i32 };
                (sv, k, tgt)
            }
            _ => {
                // generic random
                let n = rng.gen_range_usize(1, 500);
                let sv = make_sorted_distinct(&mut rng, n, -10_000, 10_000);
                let k = rng.gen_range_usize(0, sv.len() - 1);
                let tgt = rng.gen_range_i32(-10_000, 10_000);
                (sv, k, tgt)
            }
        };

        let (nums, tgt) = generate_test_case(&sorted, k, target);
        print_json(&nums, tgt);
    }
}