use vstd::prelude::*;

verus! {

pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 0 {
        0
    } else {
        seq_sum(s, end - 1) + s[end - 1] as int
    }
}

pub open spec fn seq_min(s: Seq<i32>, end: int) -> int
    decreases end,
{
    if end <= 1 {
        if end <= 0 { 0 } else { s[0] as int }
    } else {
        let prev = seq_min(s, end - 1);
        let cur = s[end - 1] as int;
        if prev <= cur { prev } else { cur }
    }
}

pub proof fn lemma_all_equal_sum(s: Seq<i32>, end: int, v: i32)
    requires
        end >= 0,
        end <= s.len(),
        forall |i: int| 0 <= i < end ==> s[i] == v,
    ensures
        seq_sum(s, end) == end * (v as int),
    decreases end,
{
    if end <= 0 {
        assert(seq_sum(s, end) == 0);
        assert(end * (v as int) == 0);
    } else {
        lemma_all_equal_sum(s, end - 1, v);
        assert(s[end - 1] == v);
        assert(seq_sum(s, end) == seq_sum(s, end - 1) + v as int);
        assert(seq_sum(s, end - 1) == (end - 1) * (v as int));
        assert(end * (v as int) == (end - 1) * (v as int) + (v as int)) by (nonlinear_arith);
    }
}

pub proof fn lemma_all_equal_min(s: Seq<i32>, end: int, v: i32)
    requires
        end >= 1,
        end <= s.len(),
        forall |i: int| 0 <= i < end ==> s[i] == v,
    ensures
        seq_min(s, end) == v as int,
    decreases end,
{
    if end == 1 {
        assert(s[0] == v);
    } else {
        lemma_all_equal_min(s, end - 1, v);
        assert(s[end - 1] == v);
    }
}

pub fn generate_test_case(n: usize, v: i32) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100_000,
        -1_000_000_000 <= v <= 1_000_000_000,
    ensures
        nums.len() == n,
        1 <= nums.len() <= 100_000,
        forall |i: int| 0 <= i < nums.len() ==>
            -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        seq_sum(nums@, nums.len() as int) == (n as int) * (v as int),
        seq_min(nums@, nums.len() as int) == v as int,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            nums.len() == i,
            -1_000_000_000 <= v <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == v,
        decreases n - i,
    {
        nums.push(v);
        i = i + 1;
    }

    proof {
        assert(nums.len() == n);
        assert(forall |k: int| 0 <= k < nums.len() as int ==> nums[k] == v);
        lemma_all_equal_sum(nums@, n as int, v);
        lemma_all_equal_min(nums@, n as int, v);
    }

    nums
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
        (lo as i64 + v as i64) as i32
    }
}

fn pick_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32) {
    match mode {
        0 => (1, 0),
        1 => (1, rng.gen_range_i32(-1_000_000_000, 1_000_000_000)),
        2 => (2, rng.gen_range_i32(-1_000_000_000, 1_000_000_000)),
        3 => (100_000, 0),
        4 => (100_000, rng.gen_range_i32(-1_000, 1_000)),
        5 => (100_000, 1_000_000_000),
        6 => (100_000, -1_000_000_000),
        7 => {
            let n = rng.gen_range_usize(2, 100);
            (n, rng.gen_range_i32(-1_000_000_000, 1_000_000_000))
        }
        8 => {
            let n = rng.gen_range_usize(1000, 10_000);
            (n, rng.gen_range_i32(-1000, 1000))
        }
        9 => {
            let n = rng.gen_range_usize(1, 100_000);
            (n, 0)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100_000);
            let v = if t % 2 == 0 {
                rng.gen_range_i32(-1_000_000, 1_000_000)
            } else {
                rng.gen_range_i32(-1_000_000_000, 1_000_000_000)
            };
            (n, v)
        }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, v) = pick_params(&mut rng, mode, t);
        let nums = generate_test_case(n, v);
        print_json(&nums);
    }
}