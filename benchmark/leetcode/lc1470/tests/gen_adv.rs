use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, fillers: &Vec<i32>) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 500,
        fillers.len() == 2 * n,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
    ensures
        1 <= result.1 <= 500,
        result.0.len() == 2 * result.1,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000,
{
    let len: usize = (2 * n) as usize;
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            len == 2 * n,
            1 <= n <= 500,
            fillers.len() == len,
            0 <= i <= len,
            nums.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 1000,
        decreases len - i,
    {
        nums.push(fillers[i]);
        i = i + 1;
    }
    (nums, n)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn make_fillers(rng: &mut Rng, n: i32, mode: usize) -> Vec<i32> {
    let len = (2 * n) as usize;
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        let x = match mode {
            0 => rng.gen_range_i32(1, 1000),
            1 => 1,
            2 => 1000,
            3 => if i < (n as usize) { rng.gen_range_i32(1, 10) } else { rng.gen_range_i32(991, 1000) },
            4 => if i < (n as usize) { 1 } else { 1000 },
            5 => if i < (n as usize) { 1000 } else { 1 },
            6 => ((i % 1000) + 1) as i32,
            7 => if i % 2 == 0 { 1 } else { 2 },
            8 => rng.gen_range_i32(1, 5),
            9 => rng.gen_range_i32(500, 510),
            _ => rng.gen_range_i32(1, 1000),
        };
        v.push(x);
    }
    v
}

fn print_json(nums: &[i32], n: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"n\":{}}}", n);
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
        let n: i32 = match mode {
            0 => 1,
            1 => 500,
            2 => 2,
            3 => 250,
            4 => rng.gen_range_i32(1, 500),
            5 => rng.gen_range_i32(1, 50),
            6 => rng.gen_range_i32(400, 500),
            7 => 10,
            8 => 100,
            9 => rng.gen_range_i32(1, 500),
            _ => rng.gen_range_i32(1, 500),
        };

        let fillers = make_fillers(&mut rng, n, mode);
        let (nums, nn) = generate_test_case(n, &fillers);
        print_json(&nums, nn);
    }
}