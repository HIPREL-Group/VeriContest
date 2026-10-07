use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    nums_vals: &Vec<i32>,
    req_starts: &Vec<i32>,
    req_ends: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= n <= 100_000,
        nums_vals.len() == n,
        forall|i: int| 0 <= i < nums_vals.len() ==>
            0 <= #[trigger] nums_vals[i] <= 100_000,
        req_starts.len() == req_ends.len(),
        1 <= req_starts.len() <= 100_000,
        forall|i: int| 0 <= i < req_starts.len() ==>
            0 <= #[trigger] req_starts[i] && req_starts[i] <= req_ends[i]
            && (req_ends[i] as int) < n as int,
    ensures
        1 <= result.0@.len() <= 100_000,
        forall|i: int| 0 <= i < result.0@.len() ==>
            0 <= #[trigger] result.0@[i] <= 100_000,
        1 <= result.1@.len() <= 100_000,
        forall|i: int| 0 <= i < result.1@.len() ==> (
            (#[trigger] result.1@[i])@.len() == 2
                && 0 <= result.1@[i]@[0]
                && result.1@[i]@[0] <= result.1@[i]@[1]
                && (result.1@[i]@[1] as int) < result.0@.len() as int
        ),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums_vals.len()
        invariant
            0 <= i <= nums_vals.len(),
            nums.len() == i,
            nums_vals.len() == n,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == nums_vals[k],
            forall|k: int| 0 <= k < nums_vals.len() ==>
                0 <= #[trigger] nums_vals[k] <= 100_000,
        decreases nums_vals.len() - i,
    {
        nums.push(nums_vals[i]);
        i = i + 1;
    }

    assert(nums.len() == n);
    assert(forall|k: int| 0 <= k < nums.len() ==> 0 <= #[trigger] nums[k] <= 100_000);

    let mut requests: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    while j < req_starts.len()
        invariant
            0 <= j <= req_starts.len(),
            requests.len() == j,
            req_starts.len() == req_ends.len(),
            nums.len() == n,
            forall|k: int| 0 <= k < req_starts.len() ==>
                0 <= #[trigger] req_starts[k] && req_starts[k] <= req_ends[k]
                && (req_ends[k] as int) < n as int,
            forall|k: int| 0 <= k < j as int ==> (
                (#[trigger] requests[k])@.len() == 2
                && requests[k]@[0] == req_starts[k]
                && requests[k]@[1] == req_ends[k]
            ),
        decreases req_starts.len() - j,
    {
        let mut pair: Vec<i32> = Vec::new();
        pair.push(req_starts[j]);
        pair.push(req_ends[j]);
        assert(pair@.len() == 2);
        assert(pair@[0] == req_starts[j as int]);
        assert(pair@[1] == req_ends[j as int]);
        requests.push(pair);
        j = j + 1;
    }

    assert forall|i: int| 0 <= i < requests@.len() implies (
        (#[trigger] requests@[i])@.len() == 2
            && 0 <= requests@[i]@[0]
            && requests@[i]@[0] <= requests@[i]@[1]
            && (requests@[i]@[1] as int) < nums@.len() as int
    ) by {
        assert(requests[i]@[0] == req_starts[i]);
        assert(requests[i]@[1] == req_ends[i]);
    }

    (nums, requests)
}

}

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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_case(mode: usize, rng: &mut Rng) -> (usize, Vec<i32>, Vec<i32>, Vec<i32>) {
    let (n, m) = match mode {
        0 => (1usize, 1usize),
        1 => (2, 1),
        2 => (rng.gen_range_usize(1, 10), rng.gen_range_usize(1, 10)),
        3 => (rng.gen_range_usize(50, 200), rng.gen_range_usize(50, 200)),
        4 => (100_000, 1),
        5 => (1, 100_000),
        6 => (1000, 1000),
        7 => (100_000, 100),
        8 => (100, 100_000),
        9 => (rng.gen_range_usize(1, 100), rng.gen_range_usize(1, 100)),
        _ => (rng.gen_range_usize(1, 500), rng.gen_range_usize(1, 500)),
    };

    let mut nums: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let v = match mode {
            4 => rng.gen_range_i32(0, 100_000),
            5 => 100_000,
            6 => rng.gen_range_i32(0, 100),
            _ => rng.gen_range_i32(0, 100_000),
        };
        nums.push(v);
    }

    let mut starts: Vec<i32> = Vec::with_capacity(m);
    let mut ends: Vec<i32> = Vec::with_capacity(m);
    for _ in 0..m {
        let s = rng.gen_range_usize(0, n - 1);
        let e = rng.gen_range_usize(s, n - 1);
        // Some modes force full-range or single-point
        let (s, e) = match mode {
            1 => (0, n - 1),
            6 => {
                let len = rng.gen_range_usize(1, n);
                let st = rng.gen_range_usize(0, n - len);
                (st, st + len - 1)
            }
            _ => (s, e),
        };
        starts.push(s as i32);
        ends.push(e as i32);
    }

    (n, nums, starts, ends)
}

fn print_json(nums: &Vec<i32>, requests: &Vec<Vec<i32>>) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"requests\":[");
    for i in 0..requests.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", requests[i][0], requests[i][1]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, nums_vals, starts, ends) = build_case(mode, &mut rng);
        let (nums, requests) = generate_test_case(n, &nums_vals, &starts, &ends);
        print_json(&nums, &requests);
    }
}