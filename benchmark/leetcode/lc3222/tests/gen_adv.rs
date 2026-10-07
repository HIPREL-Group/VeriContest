use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32, y: i32) -> (result: (i32, i32))
    requires
        1 <= x <= 100,
        1 <= y <= 100,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
{
    (x, y)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => (1, 1),
        1 => (100, 100),
        2 => (1, 100),
        3 => (100, 1),
        4 => {
            // x <= y/4 boundary, y/4 odd -> Alice
            let x = rng.gen_range_i32(1, 100);
            let y_div4 = x;
            let y = (y_div4 * 4).min(100).max(4);
            (x.min(y / 4), y)
        }
        5 => {
            // y/4 is bottleneck, odd
            let y = rng.gen_range_i32(4, 100);
            let x = rng.gen_range_i32(y / 4 + 1, 100).max(1);
            (x, y)
        }
        6 => {
            // small y, y/4 = 0 -> Bob
            let x = rng.gen_range_i32(1, 100);
            (x, rng.gen_range_i32(1, 3))
        }
        7 => {
            // x = 1, y large -> Alice
            (1, rng.gen_range_i32(4, 100))
        }
        8 => {
            // x = 2 -> Bob
            (2, rng.gen_range_i32(8, 100))
        }
        9 => {
            // equal x and y/4
            let x = rng.gen_range_i32(1, 25);
            (x, x * 4)
        }
        _ => (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100)),
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (mut x, mut y) = pick_for_mode(&mut rng, mode);
        if x < 1 { x = 1; }
        if x > 100 { x = 100; }
        if y < 1 { y = 1; }
        if y > 100 { y = 100; }
        let (xx, yy) = generate_test_case(x, y);
        println!("{{\"x\": {}, \"y\": {}}}", xx, yy);
    }
}