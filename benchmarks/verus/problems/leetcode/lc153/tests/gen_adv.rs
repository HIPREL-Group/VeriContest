use vstd::prelude::*;

verus! {

pub open spec fn is_rotation_point_spec(nums: Seq<i32>, k: int) -> bool {
    0 <= k < nums.len()
    && (forall |a: int, b: int| k <= a < b < nums.len() ==> nums[a] < nums[b])
    && (forall |a: int, b: int| 0 <= a < b < k ==> nums[a] < nums[b])
    && (k == 0 || forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() ==> nums[a] > nums[b])
}

// Generate a rotated sorted array of length n with values:
// sorted sequence is: start, start+1, start+2, ..., start+n-1
// rotation point rot (0 <= rot < n): nums[i] = sorted[(i + rot) % n]
// Wait: we want nums[rot..n] ascending, nums[0..rot] ascending, and nums[rot-1] > nums[rot].
// So nums[i] for i in 0..rot = start + (n - rot) + i
// and nums[i] for i in rot..n = start + (i - rot)
// Then the minimum is at index rot with value start.

pub fn generate_test_case(
    n: usize,
    rot: usize,
    start: i32,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 5000,
        rot < n,
        -5000 <= start,
        start as int + n as int - 1 <= 5000,
    ensures
        nums.len() == n,
        1 <= nums.len() <= 5000,
        forall |i: int| 0 <= i < nums.len() ==> -5000 <= #[trigger] nums[i] <= 5000,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
        exists |k: int| is_rotation_point_spec(nums@, k),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let offset_before: i32 = (n - rot) as i32;

    while i < n
        invariant
            1 <= n <= 5000,
            rot < n,
            -5000 <= start,
            start as int + n as int - 1 <= 5000,
            offset_before as int == n as int - rot as int,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int && k < rot as int ==>
                #[trigger] nums[k] as int == start as int + (n as int - rot as int) + k,
            forall |k: int| 0 <= k < i as int && rot as int <= k ==>
                #[trigger] nums[k] as int == start as int + (k - rot as int),
        decreases n - i,
    {
        if i < rot {
            let v: i32 = start + offset_before + (i as i32);
            nums.push(v);
        } else {
            let v: i32 = start + (i as i32) - (rot as i32);
            nums.push(v);
        }
        i = i + 1;
    }

    proof {
        let k = rot as int;
        assert(0 <= k < nums.len());

        assert forall |a: int, b: int| k <= a < b < nums.len() implies nums@[a] < nums@[b] by {
            assert(nums@[a] as int == start as int + (a - rot as int));
            assert(nums@[b] as int == start as int + (b - rot as int));
        }

        assert forall |a: int, b: int| 0 <= a < b < k implies nums@[a] < nums@[b] by {
            assert(nums@[a] as int == start as int + (n as int - rot as int) + a);
            assert(nums@[b] as int == start as int + (n as int - rot as int) + b);
        }

        if k != 0 {
            assert forall |a: int, b: int| 0 <= a < k && k <= b < nums.len() implies nums@[a] > nums@[b] by {
                assert(nums@[a] as int == start as int + (n as int - rot as int) + a);
                assert(nums@[b] as int == start as int + (b - rot as int));
                // a < rot, b >= rot, b < n
                // nums[a] - nums[b] = (n - rot + a) - (b - rot) = n + a - b > 0 since b < n, a >= 0
            }
        }

        assert(is_rotation_point_spec(nums@, k));
        assert(exists |kk: int| is_rotation_point_spec(nums@, kk)) by {
            assert(is_rotation_point_spec(nums@, k));
        }

        // distinctness
        assert forall |i: int, j: int| 0 <= i < j < nums.len() implies nums@[i] != nums@[j] by {
            if i < rot as int && j < rot as int {
                assert(nums@[i] as int == start as int + (n as int - rot as int) + i);
                assert(nums@[j] as int == start as int + (n as int - rot as int) + j);
            } else if i >= rot as int && j >= rot as int {
                assert(nums@[i] as int == start as int + (i - rot as int));
                assert(nums@[j] as int == start as int + (j - rot as int));
            } else {
                // i < rot <= j
                assert(nums@[i] as int == start as int + (n as int - rot as int) + i);
                assert(nums@[j] as int == start as int + (j - rot as int));
                // diff: nums[i] - nums[j] = n - rot + i - j + rot = n + i - j
                // since j < n and i >= 0, n + i - j > 0
            }
        }

        // bounds
        assert forall |i: int| 0 <= i < nums.len() implies -5000 <= #[trigger] nums@[i] <= 5000 by {
            if i < rot as int {
                assert(nums@[i] as int == start as int + (n as int - rot as int) + i);
            } else {
                assert(nums@[i] as int == start as int + (i - rot as int));
            }
        }
    }

    nums
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, i32) {
    match mode {
        0 => {
            // n = 1
            let start = rng.gen_range_i32(-5000, 5000);
            (1, 0, start)
        }
        1 => {
            // small n, rot = 0 (no rotation applied in the rotation-point sense with k=0)
            let n = rng.gen_range_usize(2, 10);
            let start = rng.gen_range_i32(-5000, 5000 - n as i32 + 1);
            (n, 0, start)
        }
        2 => {
            // small n, rot = n-1
            let n = rng.gen_range_usize(2, 10);
            let start = rng.gen_range_i32(-5000, 5000 - n as i32 + 1);
            (n, n - 1, start)
        }
        3 => {
            // n max
            let n = 5000usize;
            let rot = rng.gen_range_usize(0, n - 1);
            let start = rng.gen_range_i32(-5000, 5000 - n as i32 + 1);
            (n, rot, start)
        }
        4 => {
            // rot = 1
            let n = rng.gen_range_usize(2, 100);
            let start = rng.gen_range_i32(-5000, 5000 - n as i32 + 1);
            (n, 1, start)
        }
        5 => {
            // rot = n/2
            let n = rng.gen_range_usize(2, 200);
            let start = rng.gen_range_i32(-5000, 5000 - n as i32 + 1);
            (n, n / 2, start)
        }
        6 => {
            // start at min
            let n = rng.gen_range_usize(1, 1000);
            let rot = rng.gen_range_usize(0, n - 1);
            (n, rot, -5000)
        }
        7 => {
            // start such that max = 5000
            let n = rng.gen_range_usize(1, 1000);
            let rot = rng.gen_range_usize(0, n - 1);
            let start = 5000 - n as i32 + 1;
            (n, rot, start)
        }
        8 => {
            // n = 2
            let rot = rng.gen_range_usize(0, 1);
            let start = rng.gen_range_i32(-5000, 4999);
            (2, rot, start)
        }
        9 => {
            // medium random
            let n = rng.gen_range_usize(3, 500);
            let rot = rng.gen_range_usize(0, n - 1);
            let max_start = 5000 - n as i32 + 1;
            let start = rng.gen_range_i32(-5000, max_start);
            (n, rot, start)
        }
        _ => {
            let n = rng.gen_range_usize(1, 5000);
            let rot = rng.gen_range_usize(0, n - 1);
            let max_start = 5000 - n as i32 + 1;
            let start = rng.gen_range_i32(-5000, max_start);
            let _ = t;
            (n, rot, start)
        }
    }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, rot, start) = pick_params(&mut rng, mode, t);
        // safety checks
        if n < 1 || n > 5000 { continue; }
        if rot >= n { continue; }
        if start < -5000 { continue; }
        if (start as i64) + (n as i64) - 1 > 5000 { continue; }
        let nums = generate_test_case(n, rot, start);
        print_json(&nums);
    }
}