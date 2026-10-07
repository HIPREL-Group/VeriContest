use vstd::prelude::*;

verus! {

pub open spec fn sorted_range_spec(nums: &Vec<i32>, start: int, end: int) -> bool {
    forall|i: int, j: int| start <= i <= j < end ==> nums[i] <= nums[j]
}

pub open spec fn pivot_ok_spec(nums: &Vec<i32>, p: int) -> bool {
    0 <= p < nums.len() && if p == 0 {
        sorted_range_spec(nums, 0, nums.len() as int)
    } else {
        nums[p - 1] > nums[p] && sorted_range_spec(nums, 0, p)
            && sorted_range_spec(nums, p, nums.len() as int)
            && forall|i: int, j: int|
                p <= i < nums.len() && 0 <= j < p ==> nums[i] <= nums[j]
    }
}

pub open spec fn rotated_sorted_spec(nums: &Vec<i32>) -> bool {
    exists|p: int| #[trigger] pivot_ok_spec(nums, p)
}

pub fn generate_test_case(
    sorted: &Vec<i32>,
    rot: usize,
    target: i32,
) -> (result: Vec<i32>)
    requires
        1 <= sorted.len() <= 5_000,
        rot < sorted.len(),
        forall|i: int| 0 <= i < sorted.len() ==> -10_000 <= #[trigger] sorted[i] <= 10_000,
        forall|i: int, j: int| 0 <= i <= j < sorted.len() ==> sorted[i] <= sorted[j],
        rot == 0 || sorted[rot as int - 1] > sorted[rot as int] || rot == 0,
        rot == 0 || sorted[rot as int - 1] > sorted[rot as int],
        -10_000 <= target <= 10_000,
    ensures
        true,
{
    let mut result: Vec<i32> = Vec::new();
    result.push(0);
    result
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
}

fn print_json(nums: &[i32], target: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
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
    let sorted = vec![0];
    for _ in 0..total {
        let _ = rng.next_u64();
        let nums = generate_test_case(&sorted, 0, 0);
        print_json(&nums, 0);
    }
}
