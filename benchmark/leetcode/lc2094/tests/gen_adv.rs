use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
    extra_digit: i32,
) -> (result: (Vec<i32>, i32))
    requires
        3 <= fillers.len() + 1 <= 100,
        0 <= extra_digit <= 9,
        forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 9,
    ensures
        3 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 9,
        0 <= result.1 <= 9,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = fillers.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == fillers.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < fillers.len() ==> 0 <= #[trigger] fillers[k] <= 9,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 9,
            forall|k: int| 0 <= k < i as int ==> nums[k] == fillers[k],
        decreases n - i,
    {
        nums.push(fillers[i]);
        i += 1;
    }
    nums.push(extra_digit);

    proof {
        assert(nums.len() == fillers.len() + 1);
        assert forall|k: int| 0 <= k < nums.len() implies 0 <= #[trigger] nums[k] <= 9 by {
            if k < fillers.len() as int {
                assert(nums[k] == fillers[k]);
            } else {
                assert(nums[k] == extra_digit);
            }
        }
    }

    (nums, extra_digit)
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

fn build_fillers(rng: &mut Rng, len: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    for i in 0..len {
        let d = match mode {
            0 => rng.gen_range_i32(0, 9),
            1 => 0,
            2 => rng.gen_range_i32(0, 1),
            3 => if i % 2 == 0 { 2 } else { 8 },
            4 => rng.gen_range_i32(1, 9) * 2 % 10, // all even
            5 => {
                let odds = [1, 3, 5, 7, 9];
                odds[(rng.next_u64() as usize) % 5]
            }
            6 => rng.gen_range_i32(0, 4),
            7 => rng.gen_range_i32(5, 9),
            8 => {
                if rng.next_u64() % 3 == 0 { 0 } else { rng.gen_range_i32(1, 9) }
            }
            9 => 9,
            _ => rng.gen_range_i32(0, 9),
        };
        v.push(d);
    }
    v
}

fn print_json(digits: &[i32]) {
    print!("{{\"digits\":[");
    for i in 0..digits.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", digits[i]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        // nums length: between 3 and 100 (so fillers.len() + 1 in that range)
        let n = match mode {
            0 => 3 + (t % 8),
            1 => 100,
            2 => 3,
            3 => 4,
            4 => 50,
            5 => 10 + (t % 20),
            6 => 99,
            7 => 3 + (rng.gen_range_usize(0, 97)),
            8 => 25,
            _ => 7 + (t % 30),
        };
        let filler_len = n - 1;
        let fillers = build_fillers(&mut rng, filler_len, mode);
        let extra = rng.gen_range_i32(0, 9);
        let (nums, _digit) = generate_test_case(&fillers, extra);
        print_json(&nums);
    }
}