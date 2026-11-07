use vstd::prelude::*;

verus! {

pub fn generate_test_case(nb: i32, ne: i32) -> (result: (i32, i32))
    requires
        1 <= nb <= 100,
        2 <= ne <= 100,
    ensures
        1 <= result.0 <= 100,
        2 <= result.1 <= 100,
{
    (nb, ne)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 2),
        1 => (1, 100),
        2 => (100, 2),
        3 => (100, 100),
        4 => (rng.gen_range_i32(1, 100), 2),
        5 => (rng.gen_range_i32(1, 100), 100),
        6 => (1, rng.gen_range_i32(2, 100)),
        7 => (100, rng.gen_range_i32(2, 100)),
        8 => {
            let ne = rng.gen_range_i32(2, 100);
            (ne - 1, ne)
        }
        9 => {
            let ne = rng.gen_range_i32(2, 100);
            let nb = if ne <= 100 { ne } else { 100 };
            (nb, ne)
        }
        _ => (rng.gen_range_i32(1, 100), rng.gen_range_i32(2, 100)),
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (nb, ne) = pick(&mut rng, mode);
        let (num_bottles, num_exchange) = generate_test_case(nb, ne);
        println!("{{\"num_bottles\":{},\"num_exchange\":{}}}", num_bottles, num_exchange);
    }
}