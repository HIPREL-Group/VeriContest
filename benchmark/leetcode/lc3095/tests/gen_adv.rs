use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    k: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= values.len() <= 50,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 50,
        0 <= k < 64,
    ensures
        1 <= result.0.len() <= 50,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 50,
        0 <= result.1 < 64,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            nums.len() == i,
            forall |j: int| 0 <= j < values.len() ==> 0 <= #[trigger] values[j] <= 50,
            forall |j: int| 0 <= j < i as int ==> 0 <= #[trigger] nums[j] <= 50,
            forall |j: int| 0 <= j < i as int ==> nums[j] == values[j],
        decreases n - i,
    {
        let v = values[i];
        assert(0 <= v <= 50);
        nums.push(v);
        i = i + 1;
    }
    (nums, k)
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

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    let n = match mode {
        0 => 1,
        1 => 50,
        2 => rng.gen_range_usize(1, 5),
        3 => rng.gen_range_usize(1, 50),
        4 => rng.gen_range_usize(1, 50),
        5 => rng.gen_range_usize(1, 50),
        6 => rng.gen_range_usize(1, 10),
        7 => rng.gen_range_usize(2, 50),
        8 => rng.gen_range_usize(1, 50),
        _ => rng.gen_range_usize(1, 50),
    };

    let mut values: Vec<i32> = Vec::with_capacity(n);
    let k: i32 = match mode {
        0 => 0,
        1 => 63,
        2 => rng.gen_range_i32(0, 63),
        3 => 0,
        4 => 63,
        5 => rng.gen_range_i32(0, 63),
        6 => rng.gen_range_i32(0, 63),
        7 => rng.gen_range_i32(0, 63),
        8 => rng.gen_range_i32(50, 63),
        _ => rng.gen_range_i32(0, 63),
    };

    for _ in 0..n {
        let v = match mode {
            0 => rng.gen_range_i32(0, 50),
            1 => rng.gen_range_i32(0, 50),
            2 => rng.gen_range_i32(0, 50),
            3 => 0,
            4 => 50,
            5 => {
                if rng.next_u64() % 2 == 0 { 0 } else { rng.gen_range_i32(0, 50) }
            }
            6 => rng.gen_range_i32(0, 3),
            7 => rng.gen_range_i32(0, 50),
            8 => rng.gen_range_i32(0, 50),
            _ => rng.gen_range_i32(0, 50),
        };
        values.push(v);
    }
    (values, k)
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (values, k) = build_case(&mut rng, mode);
        let (nums, k_out) = generate_test_case(&values, k);
        print_json(&nums, k_out);
    }
}