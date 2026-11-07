use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums_in: &Vec<i32>,
    queries_in: &Vec<i32>,
    x: i32,
) -> (result: (Vec<i32>, Vec<i32>, i32))
    requires
        1 <= nums_in.len() <= 100000,
        1 <= queries_in.len() <= 100000,
        forall |i: int| 0 <= i < nums_in.len() ==> 1 <= #[trigger] nums_in[i] <= 10000,
        forall |i: int| 0 <= i < queries_in.len() ==> 1 <= #[trigger] queries_in[i] <= 100000,
        1 <= x <= 10000,
    ensures
        1 <= result.0.len() <= 100000,
        1 <= result.1.len() <= 100000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100000,
        1 <= result.2 <= 10000,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums_in.len()
        invariant
            0 <= i <= nums_in.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == nums_in[k],
            forall |k: int| 0 <= k < nums_in.len() ==> 1 <= #[trigger] nums_in[k] <= 10000,
        decreases nums_in.len() - i,
    {
        nums.push(nums_in[i]);
        i += 1;
    }

    let mut queries: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < queries_in.len()
        invariant
            0 <= j <= queries_in.len(),
            queries.len() == j,
            forall |k: int| 0 <= k < j as int ==> #[trigger] queries[k] == queries_in[k],
            forall |k: int| 0 <= k < queries_in.len() ==> 1 <= #[trigger] queries_in[k] <= 100000,
        decreases queries_in.len() - j,
    {
        queries.push(queries_in[j]);
        j += 1;
    }

    (nums, queries, x)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_nums(rng: &mut Rng, n: usize, x: i32, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all x
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // no x
            for _ in 0..n {
                let mut r = rng.gen_range_i32(1, 10000);
                if r == x { r = if x == 1 { 2 } else { x - 1 }; }
                v.push(r);
            }
        }
        2 => {
            // single x at start
            v.push(x);
            for _ in 1..n {
                let mut r = rng.gen_range_i32(1, 10000);
                if r == x { r = if x == 1 { 2 } else { x - 1 }; }
                v.push(r);
            }
        }
        3 => {
            // single x at end
            for _ in 0..(n-1) {
                let mut r = rng.gen_range_i32(1, 10000);
                if r == x { r = if x == 1 { 2 } else { x - 1 }; }
                v.push(r);
            }
            v.push(x);
        }
        4 => {
            // alternating
            for i in 0..n {
                if i % 2 == 0 { v.push(x); } else {
                    let mut r = rng.gen_range_i32(1, 10000);
                    if r == x { r = if x == 1 { 2 } else { x - 1 }; }
                    v.push(r);
                }
            }
        }
        5 => {
            // random with heavy x
            for _ in 0..n {
                if rng.next_u64() % 3 == 0 {
                    v.push(x);
                } else {
                    v.push(rng.gen_range_i32(1, 10000));
                }
            }
        }
        6 => {
            // all same non-x
            let c = if x == 1 { 2 } else { 1 };
            for _ in 0..n { v.push(c); }
        }
        7 => {
            // x clumped at start half
            let half = n / 2;
            for _ in 0..half { v.push(x); }
            for _ in half..n {
                let mut r = rng.gen_range_i32(1, 10000);
                if r == x { r = if x == 1 { 2 } else { x - 1 }; }
                v.push(r);
            }
        }
        8 => {
            // x clumped at end half
            let half = n / 2;
            for _ in 0..half {
                let mut r = rng.gen_range_i32(1, 10000);
                if r == x { r = if x == 1 { 2 } else { x - 1 }; }
                v.push(r);
            }
            for _ in half..n { v.push(x); }
        }
        _ => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10000));
            }
        }
    }
    while v.len() < n {
        v.push(rng.gen_range_i32(1, 10000));
    }
    v.truncate(n);
    v
}

fn make_queries(rng: &mut Rng, q: usize, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(q);
    let cap = (n as i32).max(1).min(100000);
    match mode {
        0 => {
            for i in 0..q { v.push(((i as i32) % cap) + 1); }
        }
        1 => {
            for _ in 0..q { v.push(rng.gen_range_i32(1, 100000)); }
        }
        2 => {
            for _ in 0..q { v.push(1); }
        }
        3 => {
            for _ in 0..q { v.push(100000); }
        }
        4 => {
            for _ in 0..q { v.push(rng.gen_range_i32(1, cap)); }
        }
        5 => {
            for _ in 0..q { v.push(rng.gen_range_i32(cap, 100000)); }
        }
        _ => {
            for _ in 0..q { v.push(rng.gen_range_i32(1, 100)); }
        }
    }
    v
}

fn print_json(nums: &[i32], queries: &[i32], x: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"queries\":[");
    for i in 0..queries.len() {
        if i > 0 { print!(","); }
        print!("{}", queries[i]);
    }
    println!("],\"x\":{}}}", x);
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
    let nmodes = 10;
    let qmodes = 7;

    for t in 0..total {
        let nmode = t % nmodes;
        let qmode = (t / nmodes) % qmodes;

        let n = match t % 8 {
            0 => 1,
            1 => 2,
            2 => 10,
            3 => rng.gen_range_usize(1, 50),
            4 => rng.gen_range_usize(50, 500),
            5 => rng.gen_range_usize(500, 5000),
            6 => 100000,
            _ => rng.gen_range_usize(1, 1000),
        };

        let q = match t % 6 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(1, 100),
            3 => rng.gen_range_usize(100, 1000),
            4 => 100000,
            _ => rng.gen_range_usize(1, 500),
        };

        let x = rng.gen_range_i32(1, 10000);

        let nums = make_nums(&mut rng, n, x, nmode);
        let queries = make_queries(&mut rng, q, n, qmode);

        let nums_v: Vec<i32> = nums.iter().map(|&v| {
            let vv = if v < 1 { 1 } else if v > 10000 { 10000 } else { v };
            vv
        }).collect();
        let queries_v: Vec<i32> = queries.iter().map(|&v| {
            let vv = if v < 1 { 1 } else if v > 100000 { 100000 } else { v };
            vv
        }).collect();

        let (nums_out, queries_out, x_out) = generate_test_case(&nums_v, &queries_v, x);
        print_json(&nums_out, &queries_out, x_out);
    }
}