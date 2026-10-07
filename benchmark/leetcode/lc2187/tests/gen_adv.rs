use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    fill_val: i32,
    total_trips: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100000,
        1 <= fill_val <= 10000000,
        1 <= total_trips <= 10000000,
    ensures
        1 <= result.0.len() <= 100000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 10000000,
        1 <= result.1 <= 10000000,
        result.1 == total_trips,
{
    let mut time: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 100000,
            1 <= fill_val <= 10000000,
            time.len() == i,
            forall |k: int| 0 <= k < time.len() ==> 1 <= #[trigger] time[k] <= 10000000,
        decreases n - i,
    {
        time.push(fill_val);
        i = i + 1;
    }
    (time, total_trips)
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn print_case(time: &Vec<i32>, total_trips: i32) {
    print!("{{\"time\":[");
    for i in 0..time.len() {
        if i > 0 { print!(","); }
        print!("{}", time[i]);
    }
    println!("],\"total_trips\":{}}}", total_trips);
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (usize, i32, i32) {
    match mode {
        0 => (1, 1, 1),                                    // smallest
        1 => (1, 10_000_000, 10_000_000),                  // max values small n
        2 => (100_000, 1, 10_000_000),                     // max n, trivial time
        3 => (100_000, 10_000_000, 10_000_000),            // max everything
        4 => (rng.gen_range_usize(1, 10), rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 10)),
        5 => (rng.gen_range_usize(1, 1000), rng.gen_range_i32(1, 1000), rng.gen_range_i32(1, 1000)),
        6 => (rng.gen_range_usize(1, 100000), rng.gen_range_i32(1, 10000000), rng.gen_range_i32(1, 10000000)),
        7 => (2, 10_000_000, 1),                           // two buses slow, 1 trip
        8 => (1, 1, 10_000_000),                           // one bus, many trips
        9 => (rng.gen_range_usize(1, 50), 1, 10_000_000),
        _ => (rng.gen_range_usize(1, 100), rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)),
    }
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
    let total_cases = 220usize;

    for t in 0..total_cases {
        let mode = t % modes;
        let (n, fill_val, total_trips) = gen_mode(&mut rng, mode);
        let n = if n < 1 { 1 } else if n > 100000 { 100000 } else { n };
        let fill_val = if fill_val < 1 { 1 } else if fill_val > 10000000 { 10000000 } else { fill_val };
        let total_trips = if total_trips < 1 { 1 } else if total_trips > 10000000 { 10000000 } else { total_trips };
        let (time, total) = generate_test_case(n, fill_val, total_trips);
        print_case(&time, total);
    }
}