use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    start: i32,
    len: usize,
    target: i32,
) -> (nums: Vec<i32>)
    requires
        1 <= len <= 10_000,
        -10_000 < target < 10_000,
        -9_999 <= start,
        start as int + len as int <= 9_999,
    ensures
        1 <= nums.len() <= 10_000,
        -10_000 < target < 10_000,
        forall |i: int| 0 <= i < nums.len() ==> -10_000 < #[trigger] nums[i] < 10_000,
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;

    while k < len
        invariant
            0 <= k <= len,
            len <= 10_000,
            nums.len() == k,
            -9_999 <= start,
            start as int + len as int <= 9_999,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == start as int + i,
        decreases len - k,
    {
        let v: i32 = start + (k as i32);
        nums.push(v);
        k = k + 1;
    }

    proof {
        assert forall |i: int| 0 <= i < nums.len() implies -10_000 < #[trigger] nums[i] < 10_000 by {
            assert(nums[i] == start as int + i);
        }
        assert forall|i: int, j: int| 0 <= i < j < nums.len() implies nums[i] < nums[j] by {
            assert(nums[i] == start as int + i);
            assert(nums[j] == start as int + j);
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_params(rng: &mut Rng, mode: usize) -> (i32, usize, i32) {
    // Returns (start, len, target) satisfying:
    //   1 <= len <= 10_000
    //   -10_000 < target < 10_000
    //   -9_999 <= start
    //   start + len <= 9_999
    match mode {
        0 => {
            // small array, target present
            let len = rng.gen_range_usize(1, 10);
            let start = rng.gen_range_i32(-100, 100 - len as i32);
            let idx = rng.gen_range_usize(0, len - 1);
            let target = start + idx as i32;
            (start, len, target)
        }
        1 => {
            // small array, target absent (too large)
            let len = rng.gen_range_usize(1, 10);
            let start = rng.gen_range_i32(-100, 100 - len as i32);
            let target_cand = start + len as i32 + rng.gen_range_i32(0, 50);
            let target = if target_cand >= 10_000 { 9_999 } else if target_cand <= -10_000 { -9_999 } else { target_cand };
            (start, len, target)
        }
        2 => {
            // single element
            let start = rng.gen_range_i32(-9_998, 9_997);
            let target = if rng.next_u64() % 2 == 0 { start } else {
                let t = start + 1;
                if t >= 10_000 { 9_999 } else { t }
            };
            (start, 1, target)
        }
        3 => {
            // max length
            let len: usize = 10_000;
            let start: i32 = -5_000;
            // start + len = 5000 <= 9999
            let idx = rng.gen_range_usize(0, len - 1);
            let target = start + idx as i32;
            (start, len, target)
        }
        4 => {
            // target at boundary index 0
            let len = rng.gen_range_usize(2, 100);
            let start = rng.gen_range_i32(-500, 500);
            let target = start;
            (start, len, target)
        }
        5 => {
            // target at last index
            let len = rng.gen_range_usize(2, 100);
            let start = rng.gen_range_i32(-500, 500 - len as i32);
            let target = start + (len as i32) - 1;
            (start, len, target)
        }
        6 => {
            // target below range
            let len = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(-500, 500);
            let target_cand = start - rng.gen_range_i32(1, 100);
            let target = if target_cand <= -10_000 { -9_999 } else if target_cand >= 10_000 { 9_999 } else { target_cand };
            (start, len, target)
        }
        7 => {
            // extreme negative start
            let len = rng.gen_range_usize(1, 1000);
            let start: i32 = -9_999;
            let idx = rng.gen_range_usize(0, len - 1);
            let target = start + idx as i32;
            (start, len, target)
        }
        8 => {
            // extreme positive end
            let len = rng.gen_range_usize(1, 1000);
            let start = 9_999 - len as i32;
            let idx = rng.gen_range_usize(0, len - 1);
            let target = start + idx as i32;
            (start, len, target)
        }
        9 => {
            // middle index, medium length
            let len = rng.gen_range_usize(100, 1000);
            let start = rng.gen_range_i32(-2000, 2000 - len as i32);
            let idx = len / 2;
            let target = start + idx as i32;
            (start, len, target)
        }
        _ => {
            // random
            let len = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(-5000, 5000 - len as i32);
            let target = rng.gen_range_i32(-9_999, 9_999);
            (start, len, target)
        }
    }
}

fn print_json(nums: &[i32], target: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{}}}", target);
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
        let (start, len, target) = pick_params(&mut rng, mode);
        // Validate bounds before calling verified function
        assert!(len >= 1 && len <= 10_000);
        assert!(target > -10_000 && target < 10_000);
        assert!(start >= -9_999);
        assert!(start as i64 + len as i64 <= 9_999);
        let nums = generate_test_case(start, len, target);
        print_json(&nums, target);
    }
}
