use vstd::prelude::*;

verus! {

pub fn generate_test_case(n_val: i32, time_val: i32) -> (res: (i32, i32))
    requires
        2 <= n_val <= 1000,
        1 <= time_val <= 1000,
    ensures
        2 <= res.0 <= 1000,
        1 <= res.1 <= 1000,
{
    (n_val, time_val)
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick(mode: usize, rng: &mut Rng, t: usize) -> (i32, i32) {
    match mode {
        0 => (2, 1),
        1 => (2, 1000),
        2 => (1000, 1),
        3 => (1000, 1000),
        4 => (2, 2),
        5 => {
            // time exactly n-1 (pillow reaches end)
            let n = rng.gen_range_i32(2, 1000);
            (n, n - 1)
        }
        6 => {
            // time exactly 2*(n-1) (pillow returns to start)
            let n = rng.gen_range_i32(2, 500);
            (n, 2 * (n - 1))
        }
        7 => {
            // time multiple of n-1
            let n = rng.gen_range_i32(2, 100);
            let k = rng.gen_range_i32(1, 1000 / (n - 1).max(1));
            let time = (k * (n - 1)).min(1000).max(1);
            (n, time)
        }
        8 => {
            // small n
            let n = rng.gen_range_i32(2, 5);
            let time = rng.gen_range_i32(1, 1000);
            (n, time)
        }
        9 => {
            // n == time
            let v = rng.gen_range_i32(2, 1000);
            (v, v)
        }
        _ => {
            let _ = t;
            let n = rng.gen_range_i32(2, 1000);
            let time = rng.gen_range_i32(1, 1000);
            (n, time)
        }
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let (mut n, mut time) = pick(mode, &mut rng, t);
        if n < 2 {
            n = 2;
        }
        if n > 1000 {
            n = 1000;
        }
        if time < 1 {
            time = 1;
        }
        if time > 1000 {
            time = 1000;
        }
        let (nn, tt) = generate_test_case(n, time);
        println!("{{\"n\": {}, \"time\": {}}}", nn, tt);
    }
}