use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums_in: &Vec<i32>,
    queries_in: &Vec<Vec<i32>>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>))
    requires
        1 <= nums_in.len() <= 100_000,
        forall |i: int| 0 <= i < nums_in.len() ==> 1 <= #[trigger] nums_in[i] <= 100_000,
        1 <= queries_in.len() <= 100_000,
        forall |i: int| 0 <= i < queries_in.len() ==>
            (#[trigger] queries_in[i]).len() == 2
            && 0 <= queries_in[i][0] <= queries_in[i][1] < nums_in.len(),
    ensures
        1 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall |i: int| 0 <= i < result.1.len() ==>
            (#[trigger] result.1[i]).len() == 2
            && 0 <= result.1[i][0] <= result.1[i][1] < result.0.len(),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < nums_in.len()
        invariant
            0 <= i <= nums_in.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i ==> #[trigger] nums[k] == nums_in[k],
        decreases nums_in.len() - i,
    {
        nums.push(nums_in[i]);
        i += 1;
    }

    let mut queries: Vec<Vec<i32>> = Vec::new();
    let mut j: usize = 0;
    while j < queries_in.len()
        invariant
            0 <= j <= queries_in.len(),
            queries.len() == j,
            nums.len() == nums_in.len(),
            forall |k: int| 0 <= k < j ==> (#[trigger] queries[k]).len() == 2
                && queries[k][0] == queries_in[k][0]
                && queries[k][1] == queries_in[k][1],
            forall |i: int| 0 <= i < queries_in.len() ==>
                (#[trigger] queries_in[i]).len() == 2
                && 0 <= queries_in[i][0] <= queries_in[i][1] < nums_in.len(),
        decreases queries_in.len() - j,
    {
        let q_in = &queries_in[j];
        let mut q: Vec<i32> = Vec::new();
        q.push(q_in[0]);
        q.push(q_in[1]);
        assert(q.len() == 2);
        assert(q[0] == queries_in[j as int][0]);
        assert(q[1] == queries_in[j as int][1]);
        queries.push(q);
        j += 1;
    }

    (nums, queries)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn build_nums(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // random small
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
        }
        1 => {
            // alternating parity (fully special)
            for i in 0..n {
                if i % 2 == 0 { v.push(2); } else { v.push(1); }
            }
        }
        2 => {
            // all same parity (even)
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 50_000) * 2);
            }
        }
        3 => {
            // all same (odd)
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 49_999) * 2 + 1);
            }
        }
        4 => {
            // alternating but with some glitches
            for i in 0..n {
                let base = if i % 2 == 0 { 2 } else { 1 };
                if rng.gen_range_usize(0, 9) == 0 {
                    v.push(if base == 2 { 4 } else { 3 });
                } else {
                    v.push(if base == 2 { 3 } else { 2 });
                }
            }
        }
        5 => {
            // boundaries only
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(100_000); }
            }
        }
        6 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        7 => {
            // long runs of even followed by odd
            let half = n / 2;
            for i in 0..n {
                if i < half { v.push(2); } else { v.push(3); }
            }
        }
        8 => {
            // strictly increasing
            for i in 0..n {
                v.push(((i as i32) % 100_000) + 1);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
        }
    }
    // ensure constraints
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 100_000 { *x = 100_000; }
    }
    v
}

fn build_queries(rng: &mut Rng, n: usize, q: usize, mode: usize) -> Vec<Vec<i32>> {
    let mut res: Vec<Vec<i32>> = Vec::with_capacity(q);
    for _ in 0..q {
        let (l, r) = match mode {
            0 => {
                // random
                let a = rng.gen_range_usize(0, n - 1);
                let b = rng.gen_range_usize(0, n - 1);
                if a <= b { (a, b) } else { (b, a) }
            }
            1 => (0, n - 1), // full range
            2 => {
                let a = rng.gen_range_usize(0, n - 1);
                (a, a)
            }
            3 => {
                // adjacent pair
                if n >= 2 {
                    let a = rng.gen_range_usize(0, n - 2);
                    (a, a + 1)
                } else {
                    (0, 0)
                }
            }
            4 => {
                // small ranges from 0
                let r = rng.gen_range_usize(0, n - 1);
                (0, r)
            }
            _ => {
                let a = rng.gen_range_usize(0, n - 1);
                let b = rng.gen_range_usize(0, n - 1);
                if a <= b { (a, b) } else { (b, a) }
            }
        };
        let mut qv = Vec::new();
        qv.push(l as i32);
        qv.push(r as i32);
        res.push(qv);
    }
    res
}

fn print_json(nums: &[i32], queries: &[Vec<i32>]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    print!("],\"queries\":[");
    for i in 0..queries.len() {
        if i > 0 { print!(","); }
        print!("[{},{}]", queries[i][0], queries[i][1]);
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
    for t in 0..total {
        let nmode = t % 9;
        let qmode = (t / 9) % 6;

        let n = match t % 10 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(1, 10),
            4 => rng.gen_range_usize(10, 100),
            5 => rng.gen_range_usize(100, 1000),
            6 => rng.gen_range_usize(1000, 5000),
            7 => 100_000,
            8 => rng.gen_range_usize(50, 500),
            _ => rng.gen_range_usize(5, 200),
        };
        let q = match t % 7 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(1, 10),
            3 => rng.gen_range_usize(10, 100),
            4 => rng.gen_range_usize(100, 1000),
            5 => 1000.min(100_000),
            _ => rng.gen_range_usize(1, 50),
        };

        let nums_in = build_nums(&mut rng, n, nmode);
        let queries_in = build_queries(&mut rng, n, q, qmode);

        let (nums, queries) = generate_test_case(&nums_in, &queries_in);
        print_json(&nums, &queries);
    }
}