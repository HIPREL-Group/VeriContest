use vstd::prelude::*;

verus! {


pub open spec fn suffix_len_at_most(nums: Seq<i32>, bound: int, n: int) -> int
    recommends
        0 <= n <= nums.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else if nums[n - 1] as int <= bound {
        suffix_len_at_most(nums, bound, n - 1) + 1
    } else {
        0
    }
}

pub open spec fn count_at_most(nums: Seq<i32>, bound: int, n: int) -> int
    recommends
        0 <= n <= nums.len(),
    decreases n,
{
    if n <= 0 {
        0
    } else {
        count_at_most(nums, bound, n - 1)
            + suffix_len_at_most(nums, bound, n)
    }
}

pub open spec fn count_bounded_max(nums: Seq<i32>, left: int, right: int, n: int) -> int
    recommends
        0 <= n <= nums.len(),
        left <= right,
{
    count_at_most(nums, right, n) - count_at_most(nums, left - 1, n)
}


proof fn count_prefix_append(nums: Seq<i32>, v: i32, bound: int, end: int)
    requires 0 <= end <= nums.len(),
    ensures suffix_len_at_most(nums.push(v), bound, end) == suffix_len_at_most(nums, bound, end),
        count_at_most(nums.push(v), bound, end) == count_at_most(nums, bound, end),
    decreases end,
{
    if end > 0 { count_prefix_append(nums, v, bound, end - 1); }
}
pub fn generate_test_case(raw: Vec<i32>, left: i32, right: i32) -> (result: (Vec<i32>, i32, i32))
    ensures 1 <= result.0.len() <= 100000, 0 <= result.1 <= result.2 <= 1000000000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000000000,
        count_bounded_max(result.0@, result.1 as int, result.2 as int, result.0.len() as int) <= i32::MAX,
{
    let n = if raw.len() == 0 { 1usize } else if raw.len() > 100000 { 100000usize } else { raw.len() };
    let left = if left < 0 { 0 } else if left > 1000000000 { 1000000000 } else { left };
    let right = if right < left { left } else if right > 1000000000 { 1000000000 } else { right };
    let mut nums: Vec<i32> = Vec::new();
    let mut lower_run = 0i64;
    let mut upper_run = 0i64;
    let mut lower_total = 0i64;
    let mut upper_total = 0i64;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 100000, nums.len() == i, 0 <= left <= right <= 1000000000,
            0 <= lower_run <= upper_run <= i,
            0 <= lower_total <= upper_total <= 100000 * i,
            upper_total - lower_total <= 2147483647,
            lower_run == suffix_len_at_most(nums@, left - 1, i as int),
            upper_run == suffix_len_at_most(nums@, right as int, i as int),
            lower_total == count_at_most(nums@, left - 1, i as int),
            upper_total == count_at_most(nums@, right as int, i as int),
            forall|j: int| 0 <= j < i ==> 0 <= #[trigger] nums[j] <= 1000000000,
        decreases n - i,
    {
        let v = if i < raw.len() { raw[i] } else { 0 };
        let v = if v < 0 { 0 } else if v > 1000000000 { 1000000000 } else { v };
        let next_lower = if v < left { lower_run + 1 } else { 0 };
        let next_upper = if v <= right { upper_run + 1 } else { 0 };
        if upper_total + next_upper - lower_total - next_lower > 2147483647 {
            assert(i > 0);
            return (nums, left, right);
        }
        proof {
            count_prefix_append(nums@, v, left - 1, i as int);
            count_prefix_append(nums@, v, right as int, i as int);
        }
        nums.push(v);
        lower_run = next_lower; upper_run = next_upper;
        lower_total += next_lower; upper_total += next_upper;
        i += 1;
    }
    (nums, left, right)
}


pub fn generate_candidate(
    n: usize,
    left: i32,
    right: i32,
    values: &Vec<i32>,
) -> (res: (Vec<i32>, i32, i32))
    requires
        1 <= n <= 100_000,
        values.len() == n,
        0 <= left <= right <= 1_000_000_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        ({
            let (nums, l, r) = res;
            &&& nums.len() == n
            &&& 1 <= nums.len() <= 100_000
            &&& l == left
            &&& r == right
            &&& 0 <= l <= r <= 1_000_000_000
            &&& forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1_000_000_000
            &&& forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == values[i]
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100_000,
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1_000_000_000,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }

    (nums, left, right)
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
        self.state = self
            .state
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

fn build_values(rng: &mut Rng, n: usize, mode: usize, left: i32, right: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all within [left, right]
            for _ in 0..n {
                let x = rng.gen_range_i32(left, right);
                v.push(x);
            }
        }
        1 => {
            // all below left
            let hi = if left > 0 { left - 1 } else { 0 };
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, hi));
            }
        }
        2 => {
            // all above right
            let lo = if right < 1_000_000_000 { right + 1 } else { 1_000_000_000 };
            for _ in 0..n {
                v.push(rng.gen_range_i32(lo, 1_000_000_000));
            }
        }
        3 => {
            // mix of in-range and above
            let lo_above = if right < 1_000_000_000 { right + 1 } else { 1_000_000_000 };
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(rng.gen_range_i32(left, right));
                } else {
                    v.push(rng.gen_range_i32(lo_above, 1_000_000_000));
                }
            }
        }
        4 => {
            // mix of below and in-range
            let hi_below = if left > 0 { left - 1 } else { 0 };
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(rng.gen_range_i32(0, hi_below));
                } else {
                    v.push(rng.gen_range_i32(left, right));
                }
            }
        }
        5 => {
            // fully random across full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
        6 => {
            // all equal to left
            for _ in 0..n {
                v.push(left);
            }
        }
        7 => {
            // all equal to right
            for _ in 0..n {
                v.push(right);
            }
        }
        8 => {
            // alternating below/in-range/above pattern
            let hi_below = if left > 0 { left - 1 } else { 0 };
            let lo_above = if right < 1_000_000_000 { right + 1 } else { 1_000_000_000 };
            for i in 0..n {
                match i % 3 {
                    0 => v.push(rng.gen_range_i32(0, hi_below)),
                    1 => v.push(rng.gen_range_i32(left, right)),
                    _ => v.push(rng.gen_range_i32(lo_above, 1_000_000_000)),
                }
            }
        }
        9 => {
            // boundary: zeros and 1e9
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(1_000_000_000);
                }
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000_000));
            }
        }
    }
    v
}

fn pick_bounds(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (0, 1_000_000_000),
        1 => {
            let l = rng.gen_range_i32(0, 1_000_000_000);
            (l, l)
        }
        2 => (0, 0),
        3 => (1_000_000_000, 1_000_000_000),
        4 => {
            let l = rng.gen_range_i32(100, 999_999_900);
            let r = rng.gen_range_i32(l, 1_000_000_000);
            (l, r)
        }
        5 => {
            let l = rng.gen_range_i32(0, 500_000_000);
            let r = rng.gen_range_i32(l, 1_000_000_000);
            (l, r)
        }
        _ => {
            let l = rng.gen_range_i32(0, 1_000_000_000);
            let r = rng.gen_range_i32(l, 1_000_000_000);
            (l, r)
        }
    }
}

fn print_json(nums: &[i32], left: i32, right: i32) {
    let (nums, left, right) = generate_test_case(nums.to_vec(), left, right);
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"left\":{},\"right\":{}}}", left, right);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 10;
        let bmode = t % 7;

        let n = match t % 8 {
            0 => 1,
            1 => 2,
            2 => 10,
            3 => 50,
            4 => 100,
            5 => 1000,
            6 => 10_000,
            _ => 100_000,
        };

        let (left, right) = pick_bounds(&mut rng, bmode);
        let values = build_values(&mut rng, n, mode, left, right);

        // Sanity clamp: ensure all in [0, 1e9]
        let mut clamped: Vec<i32> = Vec::with_capacity(n);
        for &x in &values {
            let y = if x < 0 { 0 } else if x > 1_000_000_000 { 1_000_000_000 } else { x };
            clamped.push(y);
        }

        let (nums, l, r) = generate_candidate(n, left, right, &clamped);
        print_json(&nums, l, r);
    }
}
