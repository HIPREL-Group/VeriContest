use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    candies: Vec<i32>,
    extra_candies: i32,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= candies.len() <= 100,
        forall |i: int| 0 <= i < candies.len() ==> 1 <= #[trigger] candies[i] <= 100,
        1 <= extra_candies <= 50,
    ensures
        2 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 50,
{
    (candies, extra_candies)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
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

fn build_candies(values: Vec<i32>) -> Vec<i32> {
    // Sanity clamp (should already be valid) to ensure preconditions hold.
    values.into_iter().map(|v| {
        let v = if v < 1 { 1 } else { v };
        let v = if v > 100 { 100 } else { v };
        v
    }).collect()
}

fn mode_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // Smallest size, all same
            let x = rng.gen_range_i32(1, 100);
            (vec![x, x], rng.gen_range_i32(1, 50))
        }
        1 => {
            // All max
            let n = rng.gen_range_usize(2, 100);
            (vec![100; n], rng.gen_range_i32(1, 50))
        }
        2 => {
            // All min
            let n = rng.gen_range_usize(2, 100);
            (vec![1; n], rng.gen_range_i32(1, 50))
        }
        3 => {
            // Single max at front
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![1i32; n];
            v[0] = 100;
            (v, rng.gen_range_i32(1, 50))
        }
        4 => {
            // Single max at back
            let n = rng.gen_range_usize(2, 100);
            let mut v = vec![1i32; n];
            v[n - 1] = 100;
            (v, rng.gen_range_i32(1, 50))
        }
        5 => {
            // Two candidates tied just under max
            let n = rng.gen_range_usize(3, 100);
            let mut v = vec![10i32; n];
            let hi = rng.gen_range_i32(50, 100);
            v[0] = hi;
            v[n - 1] = hi;
            let extra = rng.gen_range_i32(1, 50);
            (v, extra)
        }
        6 => {
            // extra_candies tiny so only current max qualifies
            let n = rng.gen_range_usize(2, 100);
            let mut v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 50)).collect();
            v[0] = 100;
            (v, 1)
        }
        7 => {
            // Large extra_candies making many possible
            let n = rng.gen_range_usize(2, 100);
            let v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(50, 100)).collect();
            (v, 50)
        }
        8 => {
            // Increasing values
            let n = rng.gen_range_usize(2, 100);
            let v: Vec<i32> = (0..n).map(|i| ((i % 100) as i32 + 1)).collect();
            (v, rng.gen_range_i32(1, 50))
        }
        9 => {
            // Example 1
            (vec![2, 3, 5, 1, 3], 3)
        }
        _ => {
            let n = rng.gen_range_usize(2, 100);
            let v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
            (v, rng.gen_range_i32(1, 50))
        }
    }
}

fn print_json(candies: &[i32], extra: i32) {
    print!("{{\"candies\":[");
    for i in 0..candies.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", candies[i]);
    }
    println!("],\"extra_candies\":{}}}", extra);
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
        let (raw, extra) = mode_case(&mut rng, mode);
        let candies = build_candies(raw);
        let extra = if extra < 1 { 1 } else if extra > 50 { 50 } else { extra };
        let (c, e) = generate_test_case(candies, extra);
        print_json(&c, e);
    }
}