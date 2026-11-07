use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32, y: i32, z: i32) -> (result: (i32, i32, i32))
    requires
        1 <= x <= 50,
        1 <= y <= 50,
        1 <= z <= 50,
    ensures
        ({
            let (a, b, c) = result;
            &&& 1 <= a <= 50
            &&& 1 <= b <= 50
            &&& 1 <= c <= 50
            &&& a == x
            &&& b == y
            &&& c == z
        }),
{
    (x, y, z)
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
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => (1, 1, 1),
        1 => (50, 50, 50),
        2 => (1, 50, 1),
        3 => (50, 1, 1),
        4 => (1, 1, 50),
        5 => (50, 50, 1),
        6 => (1, 50, 50),
        7 => (50, 1, 50),
        8 => {
            let v = rng.gen_range_i32(1, 50);
            (v, v, v)
        }
        9 => {
            let x = rng.gen_range_i32(1, 50);
            let y = rng.gen_range_i32(1, 50);
            (x, y, 1)
        }
        10 => {
            let x = rng.gen_range_i32(1, 50);
            let y = rng.gen_range_i32(1, 50);
            (x, y, 50)
        }
        11 => {
            // x = y
            let v = rng.gen_range_i32(1, 50);
            let z = rng.gen_range_i32(1, 50);
            (v, v, z)
        }
        12 => {
            // x = y + 1
            let y = rng.gen_range_i32(1, 49);
            let z = rng.gen_range_i32(1, 50);
            (y + 1, y, z)
        }
        13 => {
            // y = x + 1
            let x = rng.gen_range_i32(1, 49);
            let z = rng.gen_range_i32(1, 50);
            (x, x + 1, z)
        }
        _ => {
            let x = rng.gen_range_i32(1, 50);
            let y = rng.gen_range_i32(1, 50);
            let z = rng.gen_range_i32(1, 50);
            (x, y, z)
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
    let modes = 15usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (x, y, z) = pick_for_mode(&mut rng, mode);
        let (a, b, c) = generate_test_case(x, y, z);
        // Print as {"a":..,"b":..} per requested format but we have 3 values.
        // The instructions say {"a": <value>, "b": <value>} but the problem has 3 inputs.
        // We'll emit x, y, z as JSON.
        println!("{{\"x\":{},\"y\":{},\"z\":{}}}", a, b, c);
    }
}