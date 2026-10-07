use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    target_idx: usize,
    start: usize,
    target: i32,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= n <= 1000,
        target_idx < n,
        start < n,
        1 <= target <= 10000,
        fillers.len() + 1 == n,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 10000,
    ensures
        ({
            let nums = result.0;
            let t = result.1;
            let s = result.2;
            &&& 1 <= nums.len() <= 1000
            &&& nums.len() == n
            &&& t == target
            &&& s == start as i32
            &&& 0 <= s < nums.len()
            &&& (forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 10000)
            &&& (exists |i: int| 0 <= i < nums.len() && #[trigger] nums[i] == t)
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    let mut fi: usize = 0;

    while pos < n
        invariant
            1 <= n <= 1000,
            target_idx < n,
            start < n,
            1 <= target <= 10000,
            fillers.len() + 1 == n,
            forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 10000,
            0 <= pos <= n,
            nums.len() == pos,
            fi == pos - (if target_idx < pos { 1usize } else { 0usize }),
            0 <= fi <= fillers.len(),
            (target_idx < pos ==> nums[target_idx as int] == target),
            forall |k: int| 0 <= k < pos as int ==> 1 <= #[trigger] nums[k] <= 10000,
        decreases n - pos,
    {
        if pos == target_idx {
            nums.push(target);
        } else {
            assert(fi < fillers.len());
            let v = fillers[fi];
            nums.push(v);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    assert(nums[target_idx as int] == target);
    assert(exists |i: int| 0 <= i < nums.len() && #[trigger] nums[i] == target) by {
        assert(0 <= target_idx < nums.len() && nums[target_idx as int] == target);
    }

    (nums, target, start as i32)
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

fn make_fillers(rng: &mut Rng, count: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(count);
    for _ in 0..count {
        v.push(rng.gen_range_i32(1, 10000));
    }
    v
}

fn print_json(nums: &[i32], target: i32, start: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"target\":{},\"start\":{}}}", target, start);
}

fn gen_case(rng: &mut Rng, mode: usize, idx: usize) -> (Vec<i32>, i32, i32) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 1000,
        3 => 1000,
        4 => rng.gen_range_usize(1, 20),
        5 => rng.gen_range_usize(50, 200),
        6 => rng.gen_range_usize(500, 1000),
        7 => 10 + (idx % 100),
        8 => 1,
        9 => 1000,
        _ => rng.gen_range_usize(1, 1000),
    };

    let start = match mode {
        0 => 0,
        1 => if idx % 2 == 0 { 0 } else { n - 1 },
        2 => 0,
        3 => n - 1,
        5 => n / 2,
        8 => 0,
        9 => rng.gen_range_usize(0, n - 1),
        _ => rng.gen_range_usize(0, n - 1),
    };

    let target: i32 = match mode {
        0 => rng.gen_range_i32(1, 10000),
        1 => 1,
        2 => 10000,
        3 => rng.gen_range_i32(1, 10000),
        4 => 1,
        5 => rng.gen_range_i32(1, 10000),
        6 => rng.gen_range_i32(1, 100),
        _ => rng.gen_range_i32(1, 10000),
    };

    let target_idx = match mode {
        2 => n - 1,
        3 => 0,
        6 => if n > 1 { n / 2 } else { 0 },
        9 => {
            let s = start;
            if s == 0 { n - 1 } else { 0 }
        }
        _ => rng.gen_range_usize(0, n - 1),
    };

    let fillers = make_fillers(rng, n - 1);
    let (nums, t, s) = generate_test_case(n, target_idx, start, target, &fillers);
    (nums, t, s)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220;
    let modes = 11;

    for t in 0..total {
        let mode = t % modes;
        let (nums, target, start) = gen_case(&mut rng, mode, t);
        print_json(&nums, target, start);
    }
}