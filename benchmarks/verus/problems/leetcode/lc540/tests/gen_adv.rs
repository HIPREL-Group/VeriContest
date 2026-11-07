use vstd::prelude::*;

verus! {

pub open spec fn count_occ(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occ(s.drop_last(), value)
            + if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

pub fn generate_test_case(
    n_pairs: usize,
    single_pos: usize,
) -> (nums: Vec<i32>)
    requires
        n_pairs <= 49_999,
        single_pos <= n_pairs,
    ensures
        true,
{
    let mut nums: Vec<i32> = Vec::new();
    nums.push(0);
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
    let total = 220usize;
    for _ in 0..total {
        let _ = rng.next_u64();
        let nums = generate_test_case(0, 0);
        print_json(&nums);
    }
}
