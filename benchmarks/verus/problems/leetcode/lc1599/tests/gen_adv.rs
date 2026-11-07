use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw: &Vec<i32>,
    boarding_cost: i32,
    running_cost: i32,
) -> (res: (Vec<i32>, i32, i32))
    requires
        1 <= raw.len() <= 100_000,
        1 <= boarding_cost <= 100,
        1 <= running_cost <= 100,
    ensures
        1 <= res.0.len() <= 100_000,
        forall |i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 50,
        1 <= res.1 <= 100,
        1 <= res.2 <= 100,
        res.1 == boarding_cost,
        res.2 == running_cost,
{
    let n = raw.len();
    let mut customers: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == raw.len(),
            0 <= i <= n,
            customers.len() == i,
            forall |k: int| 0 <= k < i as int ==> 0 <= #[trigger] customers[k] <= 50,
        decreases n - i,
    {
        let v = raw[i];
        let clamped: i32 = if v < 0 {
            0
        } else if v > 50 {
            50
        } else {
            v
        };
        customers.push(clamped);
        i = i + 1;
    }
    (customers, boarding_cost, running_cost)
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

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32, i32) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            let bc = rng.gen_range_i32(1, 100);
            let rc = rng.gen_range_i32(1, 100);
            (v, bc, rc)
        }
        1 => {
            // Example 1
            (vec![8, 3], 5, 6)
        }
        2 => {
            // Example 2
            (vec![10, 9, 6], 6, 4)
        }
        3 => {
            // Example 3
            (vec![3, 4, 0, 5, 1], 1, 92)
        }
        4 => {
            // all zeros - no profit
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(0); }
            (v, rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100))
        }
        5 => {
            // all 50s - maximum flow
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::new();
            for _ in 0..n { v.push(50); }
            (v, rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100))
        }
        6 => {
            // high boarding cost
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            (v, 100, 1)
        }
        7 => {
            // low boarding, high running - likely -1
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            (v, 1, 100)
        }
        8 => {
            // bc*4 == rc boundary
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            (v, 25, 100)
        }
        9 => {
            // single element
            let v = vec![rng.gen_range_i32(0, 50)];
            (v, rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100))
        }
        10 => {
            // large n
            let n = 100_000;
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            (v, rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100))
        }
        11 => {
            // bursty: big numbers followed by zeros
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::new();
            v.push(50);
            for _ in 1..n { v.push(0); }
            (v, rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100))
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            let bc = rng.gen_range_i32(1, 100);
            let rc = rng.gen_range_i32(1, 100);
            let _ = t;
            (v, bc, rc)
        }
    }
}

fn print_json(customers: &[i32], bc: i32, rc: i32) {
    print!("{{\"customers\":[");
    for i in 0..customers.len() {
        if i > 0 { print!(","); }
        print!("{}", customers[i]);
    }
    println!("],\"boarding_cost\":{},\"running_cost\":{}}}", bc, rc);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 13usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let (raw, bc, rc) = build(&mut rng, mode, t);
        let (customers, boarding_cost, running_cost) = generate_test_case(&raw, bc, rc);
        print_json(&customers, boarding_cost, running_cost);
    }
}