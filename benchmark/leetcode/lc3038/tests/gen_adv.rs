use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    target: i32,
    first: i32,
    n: usize,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= n <= 100,
        n == fillers.len() + 2,
        1 <= first <= 1000,
        1 <= target - first <= 1000,
        2 <= target <= 2000,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
    ensures
        2 <= nums.len() <= 100,
        nums.len() == n,
        nums[0] == first,
        nums[0] as int + nums[1] as int == target as int,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1000,
{
    let second: i32 = target - first;
    let mut nums: Vec<i32> = Vec::new();
    nums.push(first);
    nums.push(second);

    let mut i: usize = 0;
    while i < fillers.len()
        invariant
            0 <= i <= fillers.len(),
            nums.len() == 2 + i,
            nums[0] == first,
            nums[1] == second,
            second as int == target as int - first as int,
            1 <= second <= 1000,
            1 <= first <= 1000,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1000,
            forall |k: int| 2 <= k < nums.len() ==> nums[k] == fillers[k - 2],
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 1000,
        decreases fillers.len() - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }

    assert(nums.len() == n);
    assert(nums[0] as int + nums[1] as int == first as int + second as int);
    assert(first as int + second as int == target as int);

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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (i32, i32, usize, Vec<i32>) {
    match mode {
        0 => {
            // Small size
            let n = 2 + (rng.next_u64() as usize % 4);
            let first = rng.gen_range_i32(1, 1000);
            let target_max = 1000 + first.min(1000);
            let target_min = first + 1;
            let target = if target_min > target_max { first + 1 } else { rng.gen_range_i32(target_min, target_max) };
            let mut fillers = Vec::new();
            for _ in 0..(n - 2) {
                fillers.push(rng.gen_range_i32(1, 1000));
            }
            (target, first, n, fillers)
        }
        1 => {
            // All pairs equal same target - many operations possible
            let n = 2 + (rng.next_u64() as usize % 99);
            let first = rng.gen_range_i32(1, 500);
            let second = rng.gen_range_i32(1, 500);
            let target = first + second;
            // fill with alternating first/second to maximize operations
            let mut fillers = Vec::new();
            // first filler becomes nums[2], second nums[3], etc.
            for k in 0..(n - 2) {
                if k % 2 == 0 {
                    fillers.push(first);
                } else {
                    fillers.push(second);
                }
            }
            (target, first, n, fillers)
        }
        2 => {
            // n = 2
            let first = rng.gen_range_i32(1, 1000);
            let second = rng.gen_range_i32(1, 1000);
            let target = first + second;
            (target, first, 2, Vec::new())
        }
        3 => {
            // n = 100 (max)
            let first = rng.gen_range_i32(1, 500);
            let second = rng.gen_range_i32(1, 500);
            let target = first + second;
            let mut fillers = Vec::new();
            for k in 0..98 {
                if k % 2 == 0 {
                    fillers.push(first);
                } else {
                    fillers.push(second);
                }
            }
            (target, first, 100, fillers)
        }
        4 => {
            // Min values
            let n = 2 + (rng.next_u64() as usize % 20);
            let mut fillers = Vec::new();
            for _ in 0..(n - 2) {
                fillers.push(1);
            }
            (2, 1, n, fillers)
        }
        5 => {
            // Max values
            let n = 2 + (rng.next_u64() as usize % 20);
            let mut fillers = Vec::new();
            for _ in 0..(n - 2) {
                fillers.push(1000);
            }
            (2000, 1000, n, fillers)
        }
        6 => {
            // Second pair breaks the pattern
            let n = 2 + (rng.next_u64() as usize % 20).max(2);
            let first = rng.gen_range_i32(100, 500);
            let second = rng.gen_range_i32(100, 500);
            let target = first + second;
            let mut fillers = Vec::new();
            // First filler mismatch
            if n >= 4 {
                fillers.push(rng.gen_range_i32(1, 50));
                fillers.push(rng.gen_range_i32(1, 50));
                for _ in 2..(n - 2) {
                    fillers.push(rng.gen_range_i32(1, 1000));
                }
            } else {
                for _ in 0..(n - 2) {
                    fillers.push(rng.gen_range_i32(1, 1000));
                }
            }
            (target, first, n, fillers)
        }
        7 => {
            // All same value
            let n = 2 + (rng.next_u64() as usize % 98);
            let v = rng.gen_range_i32(1, 1000);
            let mut fillers = Vec::new();
            for _ in 0..(n - 2) {
                fillers.push(v);
            }
            (v + v, v, n, fillers)
        }
        8 => {
            // Target = 2 (minimum)
            let n = 2 + (rng.next_u64() as usize % 20);
            let mut fillers = Vec::new();
            for _ in 0..(n - 2) {
                fillers.push(1);
            }
            (2, 1, n, fillers)
        }
        9 => {
            // First pair matches, then breaks
            let n = 6 + (rng.next_u64() as usize % 20);
            let first = rng.gen_range_i32(200, 500);
            let second = rng.gen_range_i32(200, 500);
            let target = first + second;
            let mut fillers = Vec::new();
            fillers.push(first);
            fillers.push(second);
            // now something different
            fillers.push(1);
            fillers.push(1);
            for _ in 4..(n - 2) {
                fillers.push(rng.gen_range_i32(1, 1000));
            }
            (target, first, n, fillers)
        }
        _ => {
            // Fully random
            let n = 2 + (rng.next_u64() as usize % 99);
            let first = rng.gen_range_i32(1, 1000);
            let target_min = first + 1;
            let target_max = 1000 + first;
            let target = rng.gen_range_i32(target_min, target_max);
            let mut fillers = Vec::new();
            for _ in 0..(n - 2) {
                fillers.push(rng.gen_range_i32(1, 1000));
            }
            (target, first, n, fillers)
        }
    }
}

fn validate_and_fix(target: i32, first: i32, n: usize, fillers: Vec<i32>) -> (i32, i32, usize, Vec<i32>) {
    let mut first = first;
    let mut target = target;
    let mut fillers = fillers;

    if first < 1 { first = 1; }
    if first > 1000 { first = 1000; }

    let second = target - first;
    let mut second = second;
    if second < 1 {
        second = 1;
        target = first + second;
    }
    if second > 1000 {
        second = 1000;
        target = first + second;
    }

    let mut fixed = Vec::new();
    for v in fillers.drain(..) {
        let mut vv = v;
        if vv < 1 { vv = 1; }
        if vv > 1000 { vv = 1000; }
        fixed.push(vv);
    }

    let mut nn = n;
    if nn < 2 { nn = 2; }
    if nn > 100 { nn = 100; }
    while fixed.len() + 2 < nn {
        fixed.push(1);
    }
    while fixed.len() + 2 > nn {
        fixed.pop();
    }

    (target, first, nn, fixed)
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
        let (target, first, n, fillers) = gen_mode(&mut rng, mode);
        let (target, first, n, fillers) = validate_and_fix(target, first, n, fillers);

        // Sanity check
        if n < 2 || n > 100 { continue; }
        if first < 1 || first > 1000 { continue; }
        let second = target - first;
        if second < 1 || second > 1000 { continue; }
        if fillers.len() + 2 != n { continue; }
        let mut ok = true;
        for &v in &fillers {
            if v < 1 || v > 1000 { ok = false; break; }
        }
        if !ok { continue; }

        let nums = generate_test_case(target, first, n, &fillers);
        print_json(&nums);
    }
}