use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn is_rotation_point(nums: Seq<i32>, k: int) -> bool {
        0 <= k < nums.len()
        && (forall |a: int, b: int| k <= a < b < nums.len() ==> nums[a] <= nums[b])
        && (forall |a: int, b: int| 0 <= a < b < k ==> nums[a] <= nums[b])
        && (k == 0 || forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() ==> nums[a] >= nums[b])
    }
}

// Generate a test case by assembling a sorted array then rotating it.
// Inputs:
//   - sorted_vals: a non-decreasing sequence of i32 values in [-5000, 5000]
//   - rot: rotation amount in [0, sorted_vals.len())
// The output is: nums[i] = sorted_vals[(i + rot) % n], where we treat it as
// taking sorted array and rotating so element at index rot becomes index 0.
// Actually rotating the sorted array `r` times means taking the last r and moving to front.
// We'll just produce: nums = sorted_vals[n-rot..] ++ sorted_vals[..n-rot].
// The rotation point k = rot (position where the smallest element lies... actually k = n - rot mod n).
// Let split = n - rot (for rot in [1, n], split in [0, n-1]). Then:
//   nums[i] = sorted_vals[split + i] for i in [0, rot)
//   nums[i] = sorted_vals[i - rot] for i in [rot, n)
// The rotation point k = rot. For i >= k: nums[i] = sorted_vals[i-rot], which is sorted.
// For 0 <= i < k: nums[i] = sorted_vals[split+i], which is also sorted.
// And nums[a] for a<k is sorted_vals[split+a] >= sorted_vals[split] >= sorted_vals[i-rot] = nums[i]
//   for i >= k when split + a >= i - rot, i.e., n - rot + a >= i - rot, i.e., n + a >= i, which holds.

pub fn generate_test_case(
    sorted_vals: &Vec<i32>,
    rot: usize,
) -> (nums: Vec<i32>)
    requires
        1 <= sorted_vals.len() <= 5000,
        rot < sorted_vals.len(),
        forall |i: int| 0 <= i < sorted_vals.len() ==> -5000 <= #[trigger] sorted_vals[i] <= 5000,
        forall |i: int, j: int| 0 <= i < j < sorted_vals.len() ==> sorted_vals[i] <= sorted_vals[j],
    ensures
        1 <= nums.len() <= 5000,
        nums.len() == sorted_vals.len(),
        forall |i: int| 0 <= i < nums.len() ==> -5000 <= #[trigger] nums[i] <= 5000,
        exists |k: int| Solution::is_rotation_point(nums@, k),
{
    let n: usize = sorted_vals.len();
    let split: usize = n - rot; // in [1, n]
    let mut nums: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < rot
        invariant
            0 <= i <= rot,
            rot < n,
            n == sorted_vals.len(),
            split == n - rot,
            nums.len() == i,
            forall |j: int| 0 <= j < i as int ==> #[trigger] nums[j] == sorted_vals[split as int + j],
            forall |j: int| 0 <= j < sorted_vals.len() ==> -5000 <= #[trigger] sorted_vals[j] <= 5000,
            forall |a: int, b: int| 0 <= a < b < sorted_vals.len() ==> sorted_vals[a] <= sorted_vals[b],
        decreases rot - i,
    {
        nums.push(sorted_vals[split + i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < split
        invariant
            0 <= j <= split,
            rot < n,
            n == sorted_vals.len(),
            split == n - rot,
            nums.len() == rot + j,
            forall |k: int| 0 <= k < rot as int ==> #[trigger] nums[k] == sorted_vals[split as int + k],
            forall |k: int| rot as int <= k < rot as int + j as int ==> #[trigger] nums[k] == sorted_vals[k - rot as int],
            forall |k: int| 0 <= k < sorted_vals.len() ==> -5000 <= #[trigger] sorted_vals[k] <= 5000,
            forall |a: int, b: int| 0 <= a < b < sorted_vals.len() ==> sorted_vals[a] <= sorted_vals[b],
        decreases split - j,
    {
        nums.push(sorted_vals[j]);
        j = j + 1;
    }

    proof {
        let k: int = rot as int;
        assert(nums.len() == n);
        // bounds
        assert forall |i: int| 0 <= i < nums.len() implies -5000 <= #[trigger] nums[i] <= 5000 by {
            if i < rot as int {
                assert(nums[i] == sorted_vals[split as int + i]);
            } else {
                assert(nums[i] == sorted_vals[i - rot as int]);
            }
        }

        // second half sorted: for k <= a < b < n, nums[a] = sorted_vals[a-rot], nums[b] = sorted_vals[b-rot]
        assert forall |a: int, b: int| k <= a < b < nums.len() implies nums[a] <= nums[b] by {
            assert(nums[a] == sorted_vals[a - k]);
            assert(nums[b] == sorted_vals[b - k]);
        }

        // first part sorted: for 0 <= a < b < k, nums[a] = sorted_vals[split+a], nums[b] = sorted_vals[split+b]
        assert forall |a: int, b: int| 0 <= a < b < k implies nums[a] <= nums[b] by {
            assert(nums[a] == sorted_vals[split as int + a]);
            assert(nums[b] == sorted_vals[split as int + b]);
        }

        // rotation relation: if k > 0, then for 0 <= a < k and k <= b < n,
        // nums[a] = sorted_vals[split+a] >= sorted_vals[b-rot] = nums[b] since split+a >= b-rot means n-rot+a >= b-rot means n+a >= b, which holds.
        if k != 0 {
            assert forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() implies nums[a] >= nums[b] by {
                assert(nums[a] == sorted_vals[split as int + a]);
                assert(nums[b] == sorted_vals[b - k]);
                // split + a = n - rot + a, and b - rot <= n - 1 - rot < n - rot <= n - rot + a
                // so split + a > b - rot, thus sorted_vals[split+a] >= sorted_vals[b-rot]
                assert(split as int + a >= b - k);
            }
        }

        assert(Solution::is_rotation_point(nums@, k));
        assert(exists |kk: int| Solution::is_rotation_point(nums@, kk));
    }

    nums
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_sorted_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v.sort();
    v
}

fn make_all_same(n: usize, val: i32) -> Vec<i32> {
    vec![val; n]
}

fn make_two_runs(n: usize, a: i32, b: i32) -> Vec<i32> {
    // a <= b
    let half = n / 2;
    let mut v = Vec::with_capacity(n);
    for _ in 0..half {
        v.push(a);
    }
    for _ in half..n {
        v.push(b);
    }
    v
}

fn make_mostly_same_one_diff(n: usize, base: i32, diff: i32, pos: usize) -> Vec<i32> {
    // produce non-decreasing: if diff > base we put diff at end, if diff < base at start
    let mut v = Vec::with_capacity(n);
    if diff < base {
        for _ in 0..pos.min(n).max(1).min(n) {}
        let p = pos.min(n);
        for _ in 0..p {
            v.push(diff);
        }
        while v.len() < n {
            v.push(base);
        }
    } else {
        let p = pos.min(n);
        for _ in 0..p {
            v.push(base);
        }
        while v.len() < n {
            v.push(diff);
        }
    }
    v
}

fn make_ascending(n: usize, start: i32, step: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur = start as i64;
    for _ in 0..n {
        let c = if cur > 5000 { 5000 } else if cur < -5000 { -5000 } else { cur as i32 };
        v.push(c);
        cur += step as i64;
    }
    // enforce non-decreasing in case of clamping
    for i in 1..v.len() {
        if v[i] < v[i-1] {
            v[i] = v[i-1];
        }
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => 1,
            1 => 2 + (t % 5),
            2 => 5000,
            3 => 50 + (t % 100),
            4 => 500,
            5 => 2,
            6 => 3 + (t % 20),
            7 => 4999,
            8 => 100 + (t % 500),
            _ => 10 + (t % 50),
        };

        let sorted_vals: Vec<i32> = match mode {
            0 => {
                // n==1
                vec![rng.gen_range_i32(-5000, 5000)]
            }
            1 => {
                // all same
                let v = rng.gen_range_i32(-5000, 5000);
                make_all_same(n, v)
            }
            2 => {
                // large random
                make_sorted_random(&mut rng, n, -5000, 5000)
            }
            3 => {
                // two runs
                let a = rng.gen_range_i32(-5000, 4999);
                let b = rng.gen_range_i32(a, 5000);
                make_two_runs(n, a, b)
            }
            4 => {
                // mostly same, one different smaller
                let base = rng.gen_range_i32(-4999, 5000);
                let diff = rng.gen_range_i32(-5000, base);
                let pos = rng.gen_range_usize(0, n);
                make_mostly_same_one_diff(n, base, diff, pos)
            }
            5 => {
                // n==2 adversarial
                let a = rng.gen_range_i32(-5000, 5000);
                let b = rng.gen_range_i32(a, 5000);
                vec![a, b]
            }
            6 => {
                // small random
                make_sorted_random(&mut rng, n, -10, 10)
            }
            7 => {
                // ascending
                let start = rng.gen_range_i32(-5000, 0);
                make_ascending(n, start, 1)
            }
            8 => {
                // medium random narrow range
                make_sorted_random(&mut rng, n, -3, 3)
            }
            _ => {
                // mixed
                make_sorted_random(&mut rng, n, -5000, 5000)
            }
        };

        // Ensure length and bounds hold
        if sorted_vals.is_empty() || sorted_vals.len() > 5000 {
            continue;
        }
        // Final safety: enforce sorted and bounds
        let mut sv = sorted_vals;
        for i in 0..sv.len() {
            if sv[i] < -5000 { sv[i] = -5000; }
            if sv[i] > 5000 { sv[i] = 5000; }
        }
        for i in 1..sv.len() {
            if sv[i] < sv[i-1] {
                sv[i] = sv[i-1];
            }
        }

        let rot = rng.gen_range_usize(0, sv.len() - 1);
        let nums = generate_test_case(&sv, rot);
        print_json(&nums);
    }
}