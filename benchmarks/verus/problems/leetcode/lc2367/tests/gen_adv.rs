use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    start: i32,
    diff: i32,
    n: usize,
) -> (nums: Vec<i32>)
    requires
        3 <= n <= 200,
        1 <= diff <= 50,
        0 <= start <= 200,
        (start as int) + (n as int - 1) * (diff as int) <= 200,
    ensures
        3 <= nums.len() <= 200,
        forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 200,
        1 <= diff <= 50,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] < nums[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            3 <= n <= 200,
            1 <= diff <= 50,
            0 <= start <= 200,
            (start as int) + (n as int - 1) * (diff as int) <= 200,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==>
                #[trigger] nums[k] as int == start as int + k * (diff as int),
            forall |k: int| 0 <= k < i as int ==>
                0 <= #[trigger] nums[k] <= 200,
        decreases n - i,
    {
        proof {
            // i < n, so start + i*diff <= start + (n-1)*diff <= 200
            assert(i as int <= n as int - 1);
            assert((i as int) * (diff as int) <= (n as int - 1) * (diff as int)) by (nonlinear_arith)
                requires i as int <= n as int - 1, diff as int >= 1, i as int >= 0;
            assert(start as int + (i as int) * (diff as int) <= 200);
            assert((i as int) * (diff as int) >= 0) by (nonlinear_arith)
                requires i as int >= 0, diff as int >= 1;
        }
        let v: i32 = start + (i as i32) * diff;
        nums.push(v);
        proof {
            assert(nums[i as int] as int == start as int + (i as int) * (diff as int));
            assert forall |k: int| 0 <= k < (i + 1) as int implies
                #[trigger] nums[k] as int == start as int + k * (diff as int)
            by {
                if k < i as int {
                    assert(nums[k] as int == start as int + k * (diff as int));
                } else {
                    assert(k == i as int);
                }
            }
        }
        i = i + 1;
    }

    proof {
        assert(nums.len() == n);
        assert forall |a: int, b: int| 0 <= a < b < nums.len() implies nums[a] < nums[b] by {
            assert(nums[a] as int == start as int + a * (diff as int));
            assert(nums[b] as int == start as int + b * (diff as int));
            assert((b - a) * (diff as int) > 0) by (nonlinear_arith)
                requires b > a, diff as int >= 1;
            assert(b * (diff as int) - a * (diff as int) == (b - a) * (diff as int)) by (nonlinear_arith);
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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_params(rng: &mut Rng, mode: usize) -> (i32, i32, usize) {
    // returns (start, diff, n) with 0 <= start, start + (n-1)*diff <= 200,
    // 1 <= diff <= 50, 3 <= n <= 200
    match mode {
        0 => {
            // minimum n
            let diff = rng.gen_range_i32(1, 50);
            let max_start = 200 - 2 * diff;
            let start = if max_start >= 0 { rng.gen_range_i32(0, max_start) } else { 0 };
            (start, diff, 3)
        }
        1 => {
            // diff = 1, many elements
            let n = rng.gen_range_usize(3, 200);
            let max_start = 200 - (n as i32 - 1);
            let start = rng.gen_range_i32(0, max_start);
            (start, 1, n)
        }
        2 => {
            // start = 0
            let diff = rng.gen_range_i32(1, 50);
            let max_n = (200 / diff) + 1;
            let n_upper = if max_n > 200 { 200 } else { max_n as usize };
            let n_upper = if n_upper < 3 { 3 } else { n_upper };
            let n = rng.gen_range_usize(3, n_upper);
            (0, diff, n)
        }
        3 => {
            // max diff
            let diff = 50;
            // start + (n-1)*50 <= 200 => n-1 <= (200-start)/50
            let start = rng.gen_range_i32(0, 50);
            let max_n = ((200 - start) / 50) + 1;
            let max_n = if max_n > 200 { 200 } else { max_n as usize };
            let max_n = if max_n < 3 { 3 } else { max_n };
            let n = rng.gen_range_usize(3, max_n);
            (start, diff, n)
        }
        4 => {
            // diff = 1, maximum span
            (0, 1, 200)
        }
        5 => {
            // medium diff
            let diff = rng.gen_range_i32(2, 10);
            let max_n_from_diff = (200 / diff) + 1;
            let max_n = if max_n_from_diff > 200 { 200 } else { max_n_from_diff as usize };
            let max_n = if max_n < 3 { 3 } else { max_n };
            let n = rng.gen_range_usize(3, max_n);
            let max_start = 200 - (n as i32 - 1) * diff;
            let start = if max_start >= 0 { rng.gen_range_i32(0, max_start) } else { 0 };
            (start, diff, n)
        }
        6 => {
            // small span: start near 200
            let diff = rng.gen_range_i32(1, 20);
            let n = 3;
            let max_start = 200 - (n as i32 - 1) * diff;
            let start = if max_start >= 0 { rng.gen_range_i32(max_start / 2, max_start) } else { 0 };
            (start, diff, n)
        }
        7 => {
            // diff = 3 (example from problem)
            let diff = 3;
            let n = rng.gen_range_usize(3, 60);
            let max_start = 200 - (n as i32 - 1) * diff;
            let start = rng.gen_range_i32(0, max_start);
            (start, diff, n)
        }
        8 => {
            // diff = 2 (example 2)
            let diff = 2;
            let n = rng.gen_range_usize(3, 100);
            let max_start = 200 - (n as i32 - 1) * diff;
            let start = rng.gen_range_i32(0, max_start);
            (start, diff, n)
        }
        9 => {
            // tight upper bound
            let diff = rng.gen_range_i32(1, 50);
            let max_n_from_diff = (200 / diff) + 1;
            let max_n = if max_n_from_diff > 200 { 200 } else { max_n_from_diff as usize };
            let max_n = if max_n < 3 { 3 } else { max_n };
            let n = max_n;
            let max_start = 200 - (n as i32 - 1) * diff;
            let start = if max_start >= 0 { rng.gen_range_i32(0, max_start) } else { 0 };
            (start, diff, n)
        }
        _ => {
            let diff = rng.gen_range_i32(1, 50);
            let max_n_from_diff = (200 / diff) + 1;
            let max_n = if max_n_from_diff > 200 { 200 } else { max_n_from_diff as usize };
            let max_n = if max_n < 3 { 3 } else { max_n };
            let n = rng.gen_range_usize(3, max_n);
            let max_start = 200 - (n as i32 - 1) * diff;
            let start = if max_start >= 0 { rng.gen_range_i32(0, max_start) } else { 0 };
            (start, diff, n)
        }
    }
}

fn print_json(nums: &[i32], diff: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"diff\":{}}}", diff);
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
        let (start, diff, n) = pick_params(&mut rng, mode);
        // safety checks
        let ok = n >= 3 && n <= 200 && diff >= 1 && diff <= 50
            && start >= 0 && start <= 200
            && (start as i64) + (n as i64 - 1) * (diff as i64) <= 200;
        if !ok {
            continue;
        }
        let nums = generate_test_case(start, diff, n);
        print_json(&nums, diff);
    }
}