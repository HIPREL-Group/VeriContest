use vstd::prelude::*;

verus! {

pub fn generate_test_case(x: i32, y: i32, z: i32) -> (result: (i32, i32, i32))
    requires
        1 <= x <= 100,
        1 <= y <= 100,
        1 <= z <= 100,
    ensures
        1 <= result.0 <= 100,
        1 <= result.1 <= 100,
        1 <= result.2 <= 100,
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
        lo + (self.next_u64() % span) as i32
    }
}

fn pick(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => {
            // Person 1 closer
            let z = rng.gen_range_i32(1, 100);
            let x = rng.gen_range_i32(1, 100);
            let y = rng.gen_range_i32(1, 100);
            let dx = (x - z).abs();
            let dy = (y - z).abs();
            if dx < dy { (x, y, z) } else if dx > dy { (y, x, z) } else { (x, if y < 100 { y + 1 } else { y - 1 }, z) }
        }
        1 => {
            // Tie case
            let z = rng.gen_range_i32(10, 90);
            let d = rng.gen_range_i32(0, 10);
            let x = if z + d <= 100 { z + d } else { z - d };
            let y = if z - d >= 1 { z - d } else { z + d };
            (x, y, z)
        }
        2 => {
            // All equal
            let v = rng.gen_range_i32(1, 100);
            (v, v, v)
        }
        3 => {
            // Boundaries
            (1, 100, rng.gen_range_i32(1, 100))
        }
        4 => {
            (100, 1, rng.gen_range_i32(1, 100))
        }
        5 => {
            // x == z
            let z = rng.gen_range_i32(1, 100);
            let y = rng.gen_range_i32(1, 100);
            (z, y, z)
        }
        6 => {
            // y == z
            let z = rng.gen_range_i32(1, 100);
            let x = rng.gen_range_i32(1, 100);
            (x, z, z)
        }
        7 => {
            // x == y
            let v = rng.gen_range_i32(1, 100);
            let z = rng.gen_range_i32(1, 100);
            (v, v, z)
        }
        8 => {
            // z = 1
            (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100), 1)
        }
        9 => {
            // z = 100
            (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100), 100)
        }
        _ => {
            (rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100), rng.gen_range_i32(1, 100))
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % 11;
        let (x, y, z) = pick(&mut rng, mode);
        // Clamp to be safe
        let x = if x < 1 { 1 } else if x > 100 { 100 } else { x };
        let y = if y < 1 { 1 } else if y > 100 { 100 } else { y };
        let z = if z < 1 { 1 } else if z > 100 { 100 } else { z };
        let (xx, yy, zz) = generate_test_case(x, y, z);
        println!("{{\"x\": {}, \"y\": {}, \"z\": {}}}", xx, yy, zz);
    }
}