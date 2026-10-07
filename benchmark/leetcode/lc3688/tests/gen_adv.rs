use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
        decreases n - i,
    {
        nums.push(values[i]);
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
}

fn gen_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_usize(1, 100) as i32);
    }
    v
}

fn gen_all_odd(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let x = rng.gen_range_usize(1, 100) as i32;
        let x = if x % 2 == 0 { if x == 100 { 99 } else { x + 1 } } else { x };
        v.push(x);
    }
    v
}

fn gen_all_even(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let x = rng.gen_range_usize(1, 50) as i32 * 2;
        v.push(x);
    }
    v
}

fn gen_single(val: i32) -> Vec<i32> {
    vec![val]
}

fn gen_pow2(rng: &mut Rng, n: usize) -> Vec<i32> {
    let pows = [1, 2, 4, 8, 16, 32, 64];
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(pows[rng.gen_range_usize(0, 6)]);
    }
    v
}

fn gen_all_same(val: i32, n: usize) -> Vec<i32> {
    vec![val; n]
}

fn gen_max_vals(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(if rng.next_u64() % 2 == 0 { 100 } else { 99 });
    }
    v
}

fn gen_small(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_usize(1, 4) as i32);
    }
    v
}

fn gen_one_even(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = gen_all_odd(rng, n);
    if n > 0 {
        let idx = rng.gen_range_usize(0, n - 1);
        v[idx] = 2 * (rng.gen_range_usize(1, 50) as i32);
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
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let n = match mode {
            0 => 1,
            1 => 100,
            2 => rng.gen_range_usize(1, 10),
            3 => rng.gen_range_usize(50, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let values = match mode {
            0 => gen_single(if t % 2 == 0 { 2 } else { 7 }),
            1 => gen_random(&mut rng, n),
            2 => gen_all_odd(&mut rng, n),
            3 => gen_all_even(&mut rng, n),
            4 => gen_pow2(&mut rng, n),
            5 => gen_all_same(2, n),
            6 => gen_all_same(7, n),
            7 => gen_max_vals(&mut rng, n),
            8 => gen_small(&mut rng, n),
            9 => gen_one_even(&mut rng, n),
            _ => gen_random(&mut rng, n),
        };
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}