use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (cost: Vec<i32>)
    requires
        2 <= values.len() <= 1000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 999,
    ensures
        2 <= cost.len() <= 1000,
        forall|i: int| 0 <= i < cost.len() ==> 0 <= #[trigger] cost[i] <= 999,
{
    let n = values.len();
    let mut cost: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            cost.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] cost[k] <= 999,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 999,
        decreases n - i,
    {
        cost.push(values[i]);
        i = i + 1;
    }
    cost
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
        let span = (hi - lo + 1) as u32;
        lo + (self.next_u64() as u32 % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n: usize = match mode {
        0 => 2,
        1 => 3,
        2 => 1000,
        3 => 999,
        4 => rng.gen_range_usize(2, 10),
        5 => rng.gen_range_usize(2, 100),
        6 => rng.gen_range_usize(2, 1000),
        7 => rng.gen_range_usize(2, 50),
        8 => 2 + (t % 8),
        9 => rng.gen_range_usize(2, 500),
        _ => rng.gen_range_usize(2, 1000),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 | 1 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 999));
            }
        }
        2 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        3 => {
            // all max
            for _ in 0..n { v.push(999); }
        }
        4 => {
            // alternating 0 and 999
            for i in 0..n {
                v.push(if i % 2 == 0 { 0 } else { 999 });
            }
        }
        5 => {
            // alternating 999 and 0
            for i in 0..n {
                v.push(if i % 2 == 0 { 999 } else { 0 });
            }
        }
        6 => {
            // first and last are cheap, middle is expensive
            for i in 0..n {
                if i == 0 || i == n - 1 {
                    v.push(rng.gen_range_i32(0, 5));
                } else {
                    v.push(rng.gen_range_i32(900, 999));
                }
            }
        }
        7 => {
            // mostly ones with occasional big values
            for _ in 0..n {
                if rng.next_u64() % 5 == 0 {
                    v.push(rng.gen_range_i32(100, 999));
                } else {
                    v.push(1);
                }
            }
        }
        8 => {
            // small arrays with boundary values
            for _ in 0..n {
                let choice = rng.next_u64() % 4;
                v.push(match choice {
                    0 => 0,
                    1 => 999,
                    2 => 1,
                    _ => rng.gen_range_i32(0, 999),
                });
            }
        }
        9 => {
            // ascending pattern mod 1000
            for i in 0..n {
                v.push((i % 1000) as i32 % 1000);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 999));
            }
        }
    }
    v
}

fn print_json(cost: &[i32]) {
    print!("{{\"cost\":[");
    for i in 0..cost.len() {
        if i > 0 { print!(","); }
        print!("{}", cost[i]);
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
        let v = build_case(&mut rng, mode, t);
        // sanity clamp (should already be in range)
        let mut clamped: Vec<i32> = Vec::with_capacity(v.len());
        for &x in &v {
            let y = if x < 0 { 0 } else if x > 999 { 999 } else { x };
            clamped.push(y);
        }
        let cost = generate_test_case(&clamped);
        print_json(&cost);
    }
}