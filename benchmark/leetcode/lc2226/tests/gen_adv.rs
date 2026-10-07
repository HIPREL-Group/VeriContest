use vstd::prelude::*;

verus! {

pub open spec fn all_in_range(v: Seq<i32>) -> bool {
    forall |i: int| 0 <= i < v.len() ==> 1 <= #[trigger] v[i] <= 10000000
}

pub fn generate_test_case(
    candies: &Vec<i32>,
    k: i64,
) -> (result: (Vec<i32>, i32, i64))
    requires
        1 <= candies.len() <= 100000,
        forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 10000000,
        1 <= k <= 1000000000000,
    ensures
        1 <= result.0.len() <= 100000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000000,
        1 <= result.2 <= 1000000000000,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < candies.len()
        invariant
            0 <= i <= candies.len(),
            out.len() == i,
            forall |j: int| 0 <= j < i ==> 1 <= #[trigger] out[j] <= 10000000,
            forall |j: int| 0 <= j < candies.len() ==> 1 <= #[trigger] candies[j] <= 10000000,
            forall |j: int| 0 <= j < i ==> out[j] == candies[j],
        decreases candies.len() - i,
    {
        out.push(candies[i]);
        i += 1;
    }
    (out, 0i32, k)
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i64
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        self.gen_i64(lo as i64, hi as i64) as i32
    }
}

fn make_candies(rng: &mut Rng, mode: usize, size: usize) -> (Vec<i32>, i64) {
    let mut v: Vec<i32> = Vec::with_capacity(size);
    match mode {
        0 => {
            // small random
            for _ in 0..size { v.push(rng.gen_i32(1, 20)); }
            let k = rng.gen_i64(1, 50);
            (v, k)
        }
        1 => {
            // all ones
            for _ in 0..size { v.push(1); }
            (v, rng.gen_i64(1, size as i64))
        }
        2 => {
            // all max
            for _ in 0..size { v.push(10_000_000); }
            (v, rng.gen_i64(1, 1_000_000_000_000))
        }
        3 => {
            // k very large (impossible)
            for _ in 0..size { v.push(rng.gen_i32(1, 100)); }
            (v, 1_000_000_000_000)
        }
        4 => {
            // k=1
            for _ in 0..size { v.push(rng.gen_i32(1, 10_000_000)); }
            (v, 1)
        }
        5 => {
            // single pile
            v.push(rng.gen_i32(1, 10_000_000));
            (v, rng.gen_i64(1, 100))
        }
        6 => {
            // identical values
            let val = rng.gen_i32(1, 10_000_000);
            for _ in 0..size { v.push(val); }
            (v, rng.gen_i64(1, size as i64 * 10))
        }
        7 => {
            // one large, rest small
            v.push(10_000_000);
            for _ in 1..size { v.push(1); }
            (v, rng.gen_i64(1, 100))
        }
        8 => {
            // sum equals k exactly
            let base: i32 = rng.gen_i32(1, 1000);
            for _ in 0..size { v.push(base); }
            (v, (base as i64) * (size as i64))
        }
        9 => {
            // k just exceeds total
            let base: i32 = rng.gen_i32(1, 100);
            for _ in 0..size { v.push(base); }
            let total = (base as i64) * (size as i64);
            (v, total + 1)
        }
        _ => {
            for _ in 0..size { v.push(rng.gen_i32(1, 10_000_000)); }
            (v, rng.gen_i64(1, 1_000_000_000_000))
        }
    }
}

fn print_json(candies: &[i32], x: i32, k: i64) {
    print!("{{\"candies\":[");
    for i in 0..candies.len() {
        if i > 0 { print!(","); }
        print!("{}", candies[i]);
    }
    println!("],\"x\":{},\"k\":{}}}", x, k);
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
        let size = match mode {
            1 => 100_000,
            2 => 1000,
            5 => 1,
            _ => {
                let r = rng.gen_usize(1, 500);
                r
            }
        };
        let (candies, k) = make_candies(&mut rng, mode, size);
        let (c2, x, k2) = generate_test_case(&candies, k);
        print_json(&c2, x, k2);
    }
}