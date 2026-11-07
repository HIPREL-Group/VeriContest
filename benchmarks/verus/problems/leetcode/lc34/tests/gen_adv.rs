use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    sorted_vals: &Vec<i32>,
    target: i32,
) -> (nums: Vec<i32>)
    requires
        0 <= sorted_vals.len() <= 100_000,
        forall |i: int| 0 <= i < sorted_vals.len() ==> -1_000_000_000 <= #[trigger] sorted_vals[i] <= 1_000_000_000,
        forall |i: int, j: int| 0 <= i <= j < sorted_vals.len() ==> sorted_vals[i] <= sorted_vals[j],
        -1_000_000_000 <= target <= 1_000_000_000,
    ensures
        nums.len() == sorted_vals.len(),
        0 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        forall |i: int, j: int| 0 <= i <= j < nums.len() ==> nums[i] <= nums[j],
        -1_000_000_000 <= target <= 1_000_000_000,
{
    let n = sorted_vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            0 <= pos <= n,
            n == sorted_vals.len(),
            nums.len() == pos,
            forall |k: int| 0 <= k < pos as int ==> #[trigger] nums[k] == sorted_vals[k],
            forall |i: int| 0 <= i < sorted_vals.len() ==> -1_000_000_000 <= #[trigger] sorted_vals[i] <= 1_000_000_000,
            forall |i: int, j: int| 0 <= i <= j < sorted_vals.len() ==> sorted_vals[i] <= sorted_vals[j],
        decreases n - pos,
    {
        nums.push(sorted_vals[pos]);
        pos = pos + 1;
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
        if lo >= hi { return lo; }
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        if lo >= hi { return lo; }
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_sorted(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v.sort();
    v
}

fn make_constant(val: i32, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn make_with_run(rng: &mut Rng, n: usize, target: i32, run_start: usize, run_len: usize, lo: i32, hi: i32) -> Vec<i32> {
    // build array with a contiguous run of `target` at positions [run_start, run_start+run_len)
    // values before are < target, values after are > target
    let mut v: Vec<i32> = Vec::with_capacity(n);
    // before: sorted, all < target
    let mut before: Vec<i32> = Vec::new();
    for _ in 0..run_start {
        let val = if target > lo {
            rng.gen_range_i32(lo, target - 1)
        } else {
            lo
        };
        before.push(val);
    }
    before.sort();
    for x in before { v.push(x); }
    for _ in 0..run_len {
        v.push(target);
    }
    let after_len = n - run_start - run_len;
    let mut after: Vec<i32> = Vec::new();
    for _ in 0..after_len {
        let val = if target < hi {
            rng.gen_range_i32(target + 1, hi)
        } else {
            hi
        };
        after.push(val);
    }
    after.sort();
    for x in after { v.push(x); }
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
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let (sorted_vals, target): (Vec<i32>, i32) = match mode {
            0 => {
                // empty array
                (Vec::new(), rng.gen_range_i32(-1_000_000_000, 1_000_000_000))
            }
            1 => {
                // single element matching
                let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                (vec![x], x)
            }
            2 => {
                // single element not matching
                let x = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                let t = if x < 1_000_000_000 { x + 1 } else { x - 1 };
                (vec![x], t)
            }
            3 => {
                // all same, equal target
                let n = rng.gen_range_usize(2, 50);
                let x = rng.gen_range_i32(-1000, 1000);
                (make_constant(x, n), x)
            }
            4 => {
                // all same, target different
                let n = rng.gen_range_usize(2, 50);
                let x = rng.gen_range_i32(-1000, 1000);
                (make_constant(x, n), x + 1)
            }
            5 => {
                // random small, random target
                let n = rng.gen_range_usize(0, 20);
                let v = make_sorted(&mut rng, n, -10, 10);
                let tgt = rng.gen_range_i32(-10, 10);
                (v, tgt)
            }
            6 => {
                // contiguous run at start
                let n = rng.gen_range_usize(5, 50);
                let run_len = rng.gen_range_usize(1, n);
                let tgt = rng.gen_range_i32(-100, 100);
                (make_with_run(&mut rng, n, tgt, 0, run_len, -1_000_000_000, 1_000_000_000), tgt)
            }
            7 => {
                // contiguous run at end
                let n = rng.gen_range_usize(5, 50);
                let run_len = rng.gen_range_usize(1, n);
                let tgt = rng.gen_range_i32(-100, 100);
                (make_with_run(&mut rng, n, tgt, n - run_len, run_len, -1_000_000_000, 1_000_000_000), tgt)
            }
            8 => {
                // contiguous run in middle
                let n = rng.gen_range_usize(5, 100);
                let run_len = rng.gen_range_usize(1, n - 2);
                let run_start = rng.gen_range_usize(1, n - run_len - 1);
                let tgt = rng.gen_range_i32(-100, 100);
                (make_with_run(&mut rng, n, tgt, run_start, run_len, -1_000_000_000, 1_000_000_000), tgt)
            }
            9 => {
                // target not in array
                let n = rng.gen_range_usize(1, 50);
                let v = make_sorted(&mut rng, n, 0, 100);
                (v, 1000)
            }
            _ => {
                // large array
                let n = if t == 10 { 100_000 } else { rng.gen_range_usize(100, 1000) };
                let v = make_sorted(&mut rng, n, -1_000_000_000, 1_000_000_000);
                let tgt = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
                (v, tgt)
            }
        };

        let nums = generate_test_case(&sorted_vals, target);
        print_json(&nums, target);
    }
}