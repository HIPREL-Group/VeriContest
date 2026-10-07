use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100,
        forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
{
    let n = vals.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            1 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == vals[k],
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        nums.push(vals[i]);
        i = i + 1;
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
        lo + (self.next_u64() % span) as i32
    }
}

fn make_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 100));
    }
    v
}

fn make_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let x = 100 - (i as i32 % 100);
        let x = if x < 1 { 1 } else { x };
        v.push(x);
    }
    v
}

fn make_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let x = 1 + (i as i32 % 100);
        v.push(x);
    }
    v
}

fn make_all_same(n: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(val);
    }
    v
}

fn make_spike_first(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    v.push(100);
    for _ in 1..n {
        v.push(1);
    }
    v
}

fn make_spike_last(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..(n.saturating_sub(1)) {
        v.push(1);
    }
    if n >= 1 {
        v.push(100);
    }
    v
}

fn make_alternating(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { 100 } else { 1 });
    }
    v
}

fn make_two_vals(rng: &mut Rng, n: usize) -> Vec<i32> {
    let a = rng.gen_range_i32(1, 100);
    let b = rng.gen_range_i32(1, 100);
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { a } else { b });
    }
    v
}

fn make_small_range(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(1, 3));
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;

    for t in 0..total {
        let mode = t % 10;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 100,
            4 => rng.gen_range_usize(1, 100),
            5 => rng.gen_range_usize(1, 100),
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(1, 100),
            8 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 100),
        };

        let vals = match mode {
            0 => make_random(&mut rng, n),
            1 => make_decreasing(n),
            2 => make_increasing(n),
            3 => make_all_same(n, rng.gen_range_i32(1, 100)),
            4 => make_spike_first(n),
            5 => make_spike_last(n),
            6 => make_alternating(n),
            7 => make_two_vals(&mut rng, n),
            8 => make_small_range(&mut rng, n),
            _ => make_random(&mut rng, n),
        };

        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}