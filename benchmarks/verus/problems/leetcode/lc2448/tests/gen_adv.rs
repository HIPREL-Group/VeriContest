use vstd::prelude::*;

verus! {

pub open spec fn abs_diff(a: int, b: int) -> int { if a >= b { a - b } else { b - a } }
pub open spec fn move_cost(nums: Seq<i32>, cost: Seq<i32>, target: int, n: int) -> int
    recommends nums.len() == cost.len(), 0 <= n <= nums.len(),
    decreases n,
{
    if n <= 0 { 0 } else {
        move_cost(nums, cost, target, n - 1) + abs_diff(nums[n - 1] as int, target) * cost[n - 1] as int
    }
}
proof fn cost_append(nums: Seq<i32>, costs: Seq<i32>, x: i32, c: i32, target: int, end: int)
    requires nums.len() == costs.len(), 0 <= end <= nums.len(),
    ensures move_cost(nums.push(x), costs.push(c), target, end) == move_cost(nums, costs, target, end),
    decreases end,
{
    if end > 0 { cost_append(nums, costs, x, c, target, end - 1); }
}
pub fn generate_test_case(raw_nums: Vec<i32>, raw_cost: Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    ensures 1 <= result.0.len() <= 100000, result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1000000,
        exists|target: int| 1 <= target <= 1000000 && #[trigger] move_cost(result.0@, result.1@, target, result.0.len() as int) <= 9007199254740991,
{
    let n = if raw_nums.len() == 0 { 1usize } else if raw_nums.len() > 100000 { 100000usize } else { raw_nums.len() };
    let target = if raw_nums.len() == 0 { 1 } else { raw_nums[0] };
    let target = if target < 1 { 1 } else if target > 1000000 { 1000000 } else { target };
    let mut nums: Vec<i32> = Vec::new();
    let mut costs: Vec<i32> = Vec::new();
    let mut total = 0i64;
    let mut i = 0usize;
    while i < n
        invariant i <= n, 1 <= n <= 100000, nums.len() == i, costs.len() == i,
            1 <= target <= 1000000,
            0 <= total <= 9007199254740991 - 1000000 * (n - i),
            total == move_cost(nums@, costs@, target as int, i as int),
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] nums[j] <= 1000000,
            forall|j: int| 0 <= j < i ==> 1 <= #[trigger] costs[j] <= 1000000,
        decreases n - i,
    {
        let x = if i < raw_nums.len() { raw_nums[i] } else { target };
        let x = if x < 1 { 1 } else if x > 1000000 { 1000000 } else { x };
        let c = if i < raw_cost.len() { raw_cost[i] } else { 1 };
        let c = if c < 1 { 1 } else if c > 1000000 { 1000000 } else { c };
        let distance = if x >= target { (x - target) as i64 } else { (target - x) as i64 };
        assert(0 <= distance * c <= 1000000000000) by(nonlinear_arith)
            requires 0 <= distance <= 999999, 1 <= c <= 1000000;
        let term = distance * (c as i64);
        let available = 9007199254740991i64 - total - 1000000 * ((n - i - 1) as i64);
        let c = if term <= available { c } else { 1 };
        proof { cost_append(nums@, costs@, x, c, target as int, i as int); }
        nums.push(x); costs.push(c);
        total += distance * (c as i64);
        i += 1;
    }
    let result = (nums, costs);
    assert(move_cost(result.0@, result.1@, target as int, result.0.len() as int) <= 9007199254740991);
    result
}


pub fn generate_candidate(
    n: usize,
    nums_in: &Vec<i32>,
    cost_in: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= n <= 100_000,
        nums_in.len() == n,
        cost_in.len() == n,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] nums_in[i] <= 1_000_000,
        forall|i: int| 0 <= i < n ==> 1 <= #[trigger] cost_in[i] <= 1_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        result.0.len() == result.1.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
        forall|i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 1_000_000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut cost: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 100_000,
            nums_in.len() == n,
            cost_in.len() == n,
            nums.len() == i,
            cost.len() == i,
            forall|k: int| 0 <= k < i ==> 1 <= #[trigger] nums[k] <= 1_000_000,
            forall|k: int| 0 <= k < i ==> 1 <= #[trigger] cost[k] <= 1_000_000,
            forall|k: int| 0 <= k < n ==> 1 <= #[trigger] nums_in[k] <= 1_000_000,
            forall|k: int| 0 <= k < n ==> 1 <= #[trigger] cost_in[k] <= 1_000_000,
        decreases n - i,
    {
        nums.push(nums_in[i]);
        cost.push(cost_in[i]);
        i = i + 1;
    }
    (nums, cost)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_case(mode: usize, rng: &mut Rng) -> (Vec<i32>, Vec<i32>) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(100, 1000),
        4 => 100_000,
        5 => rng.gen_range_usize(2, 100),
        6 => rng.gen_range_usize(50, 500),
        7 => 100_000,
        8 => rng.gen_range_usize(1, 50),
        9 => 99_999,
        _ => rng.gen_range_usize(1, 10_000),
    };

    let mut nums = Vec::with_capacity(n);
    let mut cost = Vec::with_capacity(n);

    match mode {
        0 => {
            nums.push(rng.gen_range_i32(1, 1_000_000));
            cost.push(rng.gen_range_i32(1, 1_000_000));
        }
        1 => {
            nums.push(1); cost.push(1_000_000);
            nums.push(1_000_000); cost.push(1);
        }
        2 => {
            let v = rng.gen_range_i32(1, 1_000_000);
            for _ in 0..n { nums.push(v); cost.push(rng.gen_range_i32(1, 1_000_000)); }
        }
        3 => {
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 1_000_000));
                cost.push(rng.gen_range_i32(1, 1_000_000));
            }
        }
        4 => {
            for i in 0..n {
                nums.push(if i % 2 == 0 { 1 } else { 1_000_000 });
                cost.push(1_000_000);
            }
        }
        5 => {
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 10));
                cost.push(rng.gen_range_i32(1, 10));
            }
        }
        6 => {
            for _ in 0..n {
                nums.push(rng.gen_range_i32(999_990, 1_000_000));
                cost.push(rng.gen_range_i32(999_990, 1_000_000));
            }
        }
        7 => {
            for i in 0..n {
                nums.push(((i % 1_000_000) + 1) as i32);
                cost.push(1);
            }
        }
        8 => {
            for _ in 0..n {
                nums.push(1);
                cost.push(1);
            }
        }
        9 => {
            for i in 0..n {
                nums.push(if i == 0 { 1_000_000 } else { 1 });
                cost.push(if i == 0 { 1_000_000 } else { 1 });
            }
        }
        _ => {
            for _ in 0..n {
                nums.push(rng.gen_range_i32(1, 1_000_000));
                cost.push(rng.gen_range_i32(1, 1_000_000));
            }
        }
    }

    while nums.len() < n {
        nums.push(1);
        cost.push(1);
    }
    while nums.len() > n {
        nums.pop();
        cost.pop();
    }

    (nums, cost)
}

fn print_vec(v: &[i32]) {
    print!("[");
    for i in 0..v.len() {
        if i > 0 { print!(","); }
        print!("{}", v[i]);
    }
    print!("]");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (nums_in, cost_in) = make_case(mode, &mut rng);
        let n = nums_in.len();
        let (nums, cost) = generate_candidate(n, &nums_in, &cost_in);
        let (nums, cost) = generate_test_case(nums, cost);
        print!("{{\"nums\":");
        print_vec(&nums);
        print!(",\"cost\":");
        print_vec(&cost);
        println!("}}");
    }
}
