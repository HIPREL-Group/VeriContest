use vstd::prelude::*;

verus! {

pub open spec fn valid_partition_spec(nums: Seq<i32>, k: int) -> bool {
    1 <= k < nums.len()
    && (forall |a: int, b: int| #![trigger nums[a], nums[b]]
        0 <= a < k && k <= b < nums.len() ==> nums[a] <= nums[b])
}

pub fn generate_test_case(
    n_left: usize,
    n_right: usize,
    left_val: i32,
    right_val: i32,
) -> (nums: Vec<i32>)
    requires
        n_left >= 1,
        n_right >= 1,
        n_left + n_right <= 100_000,
        0 <= left_val <= 1_000_000,
        0 <= right_val <= 1_000_000,
        left_val <= right_val,
    ensures
        2 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000,
        exists |kk: int| valid_partition_spec(nums@, kk),
{
    let n: usize = n_left + n_right;
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n_left
        invariant
            0 <= i <= n_left,
            nums.len() == i,
            0 <= left_val <= 1_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == left_val,
        decreases n_left - i,
    {
        nums.push(left_val);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < n_right
        invariant
            0 <= j <= n_right,
            nums.len() == n_left + j,
            0 <= left_val <= 1_000_000,
            0 <= right_val <= 1_000_000,
            forall |k: int| 0 <= k < n_left as int ==> #[trigger] nums[k] == left_val,
            forall |k: int| n_left as int <= k < n_left as int + j as int ==> #[trigger] nums[k] == right_val,
        decreases n_right - j,
    {
        nums.push(right_val);
        j = j + 1;
    }

    proof {
        assert(nums.len() == n_left + n_right);
        assert(nums.len() >= 2);
        assert forall |idx: int| 0 <= idx < nums.len() implies 0 <= #[trigger] nums[idx] <= 1_000_000 by {
            if idx < n_left as int {
                assert(nums[idx] == left_val);
            } else {
                assert(nums[idx] == right_val);
            }
        }

        let kk: int = n_left as int;
        assert(1 <= kk);
        assert(kk < nums.len());
        assert forall |a: int, b: int|
            0 <= a < kk && kk <= b < nums.len() as int
            implies #[trigger] nums[a] <= #[trigger] nums[b]
        by {
            assert(nums[a] == left_val);
            assert(nums[b] == right_val);
        }
        assert(valid_partition_spec(nums@, kk));
        assert(exists |k: int| valid_partition_spec(nums@, k));
    }

    nums
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
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
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, usize, i32, i32) {
    match mode {
        0 => {
            // minimal
            (1, 1, 0, 0)
        }
        1 => {
            // boundary values
            (1, 1, 0, 1_000_000)
        }
        2 => {
            // maximum length
            let nl = 50_000;
            let nr = 50_000;
            (nl, nr, 5, 6)
        }
        3 => {
            // left very small
            let nr = rng.gen_range_usize(2, 1000);
            (1, nr, 3, 7)
        }
        4 => {
            // right very small
            let nl = rng.gen_range_usize(2, 1000);
            (nl, 1, 3, 7)
        }
        5 => {
            // equal values
            let nl = rng.gen_range_usize(1, 500);
            let nr = rng.gen_range_usize(1, 500);
            (nl, nr, 42, 42)
        }
        6 => {
            // all zeros vs max
            let nl = rng.gen_range_usize(1, 1000);
            let nr = rng.gen_range_usize(1, 1000);
            (nl, nr, 0, 1_000_000)
        }
        7 => {
            // close values (left == right - 1)
            let nl = rng.gen_range_usize(1, 500);
            let nr = rng.gen_range_usize(1, 500);
            let v = rng.gen_range_i32(0, 999_999);
            (nl, nr, v, v + 1)
        }
        8 => {
            // large-ish random
            let nl = rng.gen_range_usize(1, 5000);
            let nr = rng.gen_range_usize(1, 5000);
            let lv = rng.gen_range_i32(0, 500_000);
            let rv = rng.gen_range_i32(500_000, 1_000_000);
            (nl, nr, lv, rv)
        }
        9 => {
            // small random
            let nl = rng.gen_range_usize(1, 10);
            let nr = rng.gen_range_usize(1, 10);
            let lv = rng.gen_range_i32(0, 100);
            let rv = rng.gen_range_i32(lv, 1000);
            (nl, nr, lv, rv)
        }
        _ => {
            let nl = rng.gen_range_usize(1, 2000);
            let nr = rng.gen_range_usize(1, 2000);
            let lv = rng.gen_range_i32(0, 1_000_000);
            let rv_lo = lv;
            let rv = rng.gen_range_i32(rv_lo, 1_000_000);
            (nl, nr, lv, rv)
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
        let (nl, nr, lv, rv) = pick_params(&mut rng, mode);
        // safety clamps
        let nl = if nl < 1 { 1 } else { nl };
        let nr = if nr < 1 { 1 } else { nr };
        let (nl, nr) = if nl + nr > 100_000 {
            let half = 50_000usize;
            (half, half)
        } else {
            (nl, nr)
        };
        let lv = if lv < 0 { 0 } else if lv > 1_000_000 { 1_000_000 } else { lv };
        let rv = if rv < lv { lv } else if rv > 1_000_000 { 1_000_000 } else { rv };

        let nums = generate_test_case(nl, nr, lv, rv);
        print_json(&nums);
    }
}