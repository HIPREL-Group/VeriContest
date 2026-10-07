use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        3 <= values.len() <= 100000,
        forall |i: int| 0 <= i < values.len() ==> (#[trigger] values[i] == 0 || values[i] == 1),
    ensures
        3 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            3 <= n <= 100000,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> (#[trigger] values[k] == 0 || values[k] == 1),
            forall |k: int| 0 <= k < i as int ==> (#[trigger] nums[k] == 0 || nums[k] == 1),
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
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

    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() % 2) as i32
    }
}

fn build_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_bit());
    }
    v
}

fn build_all_ones(n: usize) -> Vec<i32> {
    vec![1i32; n]
}

fn build_all_zeros(n: usize) -> Vec<i32> {
    vec![0i32; n]
}

fn build_alternating(n: usize, start: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { start } else { 1 - start });
    }
    v
}

fn build_single_zero(n: usize, pos: usize) -> Vec<i32> {
    let mut v = vec![1i32; n];
    v[pos] = 0;
    v
}

fn build_single_one(n: usize, pos: usize) -> Vec<i32> {
    let mut v = vec![0i32; n];
    v[pos] = 1;
    v
}

fn build_blocks_of_three(n: usize, zeros: bool) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let block = i / 3;
        let on = block % 2 == 0;
        let base = if on { 1 } else { 0 };
        v.push(if zeros { base } else { 1 - base });
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
        let n: usize = match mode {
            0 => 3,
            1 => 4,
            2 => 5,
            3 => 6,
            4 => 100,
            5 => 1000,
            6 => 100000,
            7 => rng.gen_range_usize(3, 50),
            8 => rng.gen_range_usize(3, 500),
            9 => rng.gen_range_usize(3, 10000),
            _ => rng.gen_range_usize(3, 100000),
        };

        let sub = (t / 11) % 10;
        let values = match sub {
            0 => build_random(&mut rng, n),
            1 => build_all_ones(n),
            2 => build_all_zeros(n),
            3 => build_alternating(n, 0),
            4 => build_alternating(n, 1),
            5 => build_single_zero(n, 0),
            6 => build_single_zero(n, n - 1),
            7 => build_single_one(n, n / 2),
            8 => build_blocks_of_three(n, false),
            _ => build_blocks_of_three(n, true),
        };

        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}