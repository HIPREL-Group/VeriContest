use vstd::prelude::*;

verus! {

pub open spec fn seq_sum(s: Seq<i32>) -> int
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        seq_sum(s.subrange(0, s.len() - 1)) + s[s.len() - 1] as int
    }
}

pub open spec fn abs_int(x: int) -> int {
    if x >= 0 { x } else { -x }
}

pub open spec fn min_elements_spec(diff: int, limit: int) -> int {
    (diff + limit - 1) / limit
}

pub fn generate_test_case(
    n: usize,
    limit: i32,
    goal: i32,
    fill_val: i32,
) -> (result: (Vec<i32>, i32, i32))
    requires
        1 <= n <= 100_000,
        1 <= limit <= 1_000_000,
        -limit <= fill_val <= limit,
        -1_000_000_000 <= goal <= 1_000_000_000,
    ensures
        ({
            let (nums, lim, g) = result;
            &&& 1 <= nums@.len() <= 100_000
            &&& 1 <= lim <= 1_000_000
            &&& -1_000_000_000 <= g <= 1_000_000_000
            &&& (forall |i: int| 0 <= i < nums@.len() ==> -lim <= (#[trigger] nums@[i]) && nums@[i] <= lim)
            &&& min_elements_spec(abs_int(seq_sum(nums@) - g as int), lim as int) <= i32::MAX as int
        }),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            1 <= n <= 100_000,
            1 <= limit <= 1_000_000,
            forall |k: int| 0 <= k < nums@.len() ==> #[trigger] nums@[k] == 0i32,
        decreases n - i,
    {
        nums.push(0i32);
        i = i + 1;
    }

    // Prove bounds on each element.
    assert forall |k: int| 0 <= k < nums@.len() implies
        -limit <= (#[trigger] nums@[k]) && nums@[k] <= limit
    by {
        assert(nums@[k] == 0i32);
        assert(-limit <= 0i32 <= limit) by (nonlinear_arith)
            requires
                limit >= 1;
    }

    proof {
        lemma_sum_zero(nums@);
        let ss = seq_sum(nums@);
        assert(ss == 0);

        let diff = abs_int(ss - goal as int);
        assert(ss - goal as int == -(goal as int)) by (nonlinear_arith)
            requires
                ss == 0;
        if goal as int >= 0 {
            assert(diff == goal as int);
        } else {
            assert(diff == -(goal as int));
        }
        assert(diff <= 1_000_000_000) by (nonlinear_arith)
            requires
                -1_000_000_000 <= goal as int <= 1_000_000_000,
                diff == if goal as int >= 0 { goal as int } else { -(goal as int) };
        assert(diff >= 0);
        assert(diff + limit as int - 1 >= 0) by (nonlinear_arith)
            requires
                diff >= 0,
                limit as int >= 1;
        assert(diff + limit as int - 1 <= 1_000_999_999) by (nonlinear_arith)
            requires
                diff <= 1_000_000_000,
                1 <= limit as int <= 1_000_000;
        assert(min_elements_spec(diff, limit as int) <= diff + limit as int - 1) by (nonlinear_arith)
            requires
                diff + limit as int - 1 >= 0,
                limit as int >= 1;
        assert(1_000_999_999 <= i32::MAX as int);
        assert(min_elements_spec(diff, limit as int) <= i32::MAX as int) by (nonlinear_arith)
            requires
                min_elements_spec(diff, limit as int) <= diff + limit as int - 1,
                diff + limit as int - 1 <= 1_000_999_999,
                1_000_999_999 <= i32::MAX as int;
    }

    (nums, limit, goal)
}

pub proof fn lemma_sum_zero(s: Seq<i32>)
    requires
        forall |i: int| 0 <= i < s.len() ==> s[i] == 0i32,
    ensures
        seq_sum(s) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
        assert(seq_sum(s) == 0);
    } else {
        let sub = s.subrange(0, s.len() - 1);
        assert forall |i: int| 0 <= i < sub.len() implies sub[i] == 0i32 by {
            assert(sub[i] == s[i]);
        }
        lemma_sum_zero(sub);
        assert(seq_sum(s) == seq_sum(sub) + s[s.len() - 1] as int);
        assert(s[s.len() - 1] == 0i32);
        assert(seq_sum(s) == 0);
    }
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, i32, i32, i32) {
    // returns (n, limit, goal, fill_val) where fill_val is 0 to keep sum=0
    // (we'll use fill_val = 0 always for safety)
    match mode {
        0 => {
            // minimum sizes
            (1, 1, 0, 0)
        }
        1 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let limit = rng.gen_range_i32(1, 10);
            let goal = rng.gen_range_i32(-20, 20);
            (n, limit, goal, 0)
        }
        2 => {
            // goal = 0
            let n = rng.gen_range_usize(1, 1000);
            let limit = rng.gen_range_i32(1, 1000);
            (n, limit, 0, 0)
        }
        3 => {
            // large goal extremes
            let n = rng.gen_range_usize(1, 100);
            let limit = rng.gen_range_i32(1, 1_000_000);
            let goal = 1_000_000_000;
            (n, limit, goal, 0)
        }
        4 => {
            let n = rng.gen_range_usize(1, 100);
            let limit = rng.gen_range_i32(1, 1_000_000);
            let goal = -1_000_000_000;
            (n, limit, goal, 0)
        }
        5 => {
            // max n
            (100_000, rng.gen_range_i32(1, 1_000_000), rng.gen_range_i32(-1_000_000_000, 1_000_000_000), 0)
        }
        6 => {
            // limit = 1
            let n = rng.gen_range_usize(1, 1000);
            (n, 1, rng.gen_range_i32(-1000, 1000), 0)
        }
        7 => {
            // limit = max
            let n = rng.gen_range_usize(1, 100);
            (n, 1_000_000, rng.gen_range_i32(-1_000_000_000, 1_000_000_000), 0)
        }
        8 => {
            // divisible case
            let limit = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_usize(1, 100);
            let goal = limit * (rng.gen_range_i32(-10, 10));
            (n, limit, goal, 0)
        }
        9 => {
            // off-by-one: diff = limit - 1
            let limit = rng.gen_range_i32(2, 1000);
            let n = rng.gen_range_usize(1, 100);
            let goal = limit - 1;
            (n, limit, goal, 0)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100_000);
            let limit = rng.gen_range_i32(1, 1_000_000);
            let goal = rng.gen_range_i32(-1_000_000_000, 1_000_000_000);
            (n, limit, goal, 0)
        }
    }
}

fn print_json(nums: &[i32], limit: i32, goal: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"limit\":{},\"goal\":{}}}", limit, goal);
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
        let (n, limit, goal, fill_val) = gen_mode(&mut rng, mode);
        let (nums, lim, g) = generate_test_case(n, limit, goal, fill_val);
        print_json(&nums, lim, g);
    }
}
