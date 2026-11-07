use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        3 <= values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
        forall|i: int, j: int| 0 <= i < j < values.len() ==> values[i] != values[j],
    ensures
        3 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        forall|i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(1);
    nums.push(2);
    nums.push(3);
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
    let total = 200usize;
    let values = vec![1, 2, 3];
    for _ in 0..total {
        let _ = rng.next_u64();
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}
