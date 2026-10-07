use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    radius: i32,
    x_center: i32,
    y_center: i32,
    x1: i32,
    y1: i32,
    x2: i32,
    y2: i32,
) -> (res: (i32, i32, i32, i32, i32, i32, i32))
    requires
        1 <= radius <= 2000,
        -10_000 <= x_center <= 10_000,
        -10_000 <= y_center <= 10_000,
        -10_000 <= x1 <= 10_000,
        -10_000 <= y1 <= 10_000,
        -10_000 <= x2 <= 10_000,
        -10_000 <= y2 <= 10_000,
        x1 < x2,
        y1 < y2,
    ensures
        1 <= res.0 <= 2000,
        -10_000 <= res.1 <= 10_000,
        -10_000 <= res.2 <= 10_000,
        -10_000 <= res.3 <= 10_000,
        -10_000 <= res.4 <= 10_000,
        -10_000 <= res.5 <= 10_000,
        -10_000 <= res.6 <= 10_000,
        res.3 < res.5,
        res.4 < res.6,
        res.0 == radius,
        res.1 == x_center,
        res.2 == y_center,
        res.3 == x1,
        res.4 == y1,
        res.5 == x2,
        res.6 == y2,
{
    (radius, x_center, y_center, x1, y1, x2, y2)
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
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }
}

fn clamp_i32(v: i32, lo: i32, hi: i32) -> i32 {
    if v < lo { lo } else if v > hi { hi } else { v }
}

fn build(rng: &mut Rng, mode: usize) -> (i32, i32, i32, i32, i32, i32, i32) {
    match mode {
        0 => {
            // fully random
            let radius = rng.gen_i32(1, 2000);
            let xc = rng.gen_i32(-10_000, 10_000);
            let yc = rng.gen_i32(-10_000, 10_000);
            let a = rng.gen_i32(-10_000, 9_999);
            let b = rng.gen_i32(a + 1, 10_000);
            let c = rng.gen_i32(-10_000, 9_999);
            let d = rng.gen_i32(c + 1, 10_000);
            (radius, xc, yc, a, c, b, d)
        }
        1 => {
            // center inside rectangle
            let x1 = rng.gen_i32(-10_000, 9_999);
            let x2 = rng.gen_i32(x1 + 1, 10_000);
            let y1 = rng.gen_i32(-10_000, 9_999);
            let y2 = rng.gen_i32(y1 + 1, 10_000);
            let xc = rng.gen_i32(x1, x2);
            let yc = rng.gen_i32(y1, y2);
            let radius = rng.gen_i32(1, 2000);
            (radius, xc, yc, x1, y1, x2, y2)
        }
        2 => {
            // circle far away
            let radius = rng.gen_i32(1, 10);
            let xc = 10_000;
            let yc = 10_000;
            let x1 = -10_000; let y1 = -10_000;
            let x2 = -9_000; let y2 = -9_000;
            (radius, xc, yc, x1, y1, x2, y2)
        }
        3 => {
            // circle just touches rectangle (tangent)
            let x1 = rng.gen_i32(-5000, 0);
            let x2 = rng.gen_i32(x1 + 1, 5000);
            let y1 = rng.gen_i32(-5000, 0);
            let y2 = rng.gen_i32(y1 + 1, 5000);
            let radius = rng.gen_i32(1, 2000);
            let xc = clamp_i32(x2 + radius, -10_000, 10_000);
            let yc = rng.gen_i32(y1, y2);
            (radius, xc, yc, x1, y1, x2, y2)
        }
        4 => {
            // circle just outside by 1
            let x1 = rng.gen_i32(-5000, 0);
            let x2 = rng.gen_i32(x1 + 1, 5000);
            let y1 = rng.gen_i32(-5000, 0);
            let y2 = rng.gen_i32(y1 + 1, 5000);
            let radius = rng.gen_i32(1, 1000);
            let xc = clamp_i32(x2 + radius + 1, -10_000, 10_000);
            let yc = rng.gen_i32(y1, y2);
            (radius, xc, yc, x1, y1, x2, y2)
        }
        5 => {
            // corner case: near a rectangle corner
            let x1 = rng.gen_i32(-5000, 0);
            let x2 = rng.gen_i32(x1 + 1, 5000);
            let y1 = rng.gen_i32(-5000, 0);
            let y2 = rng.gen_i32(y1 + 1, 5000);
            let radius = rng.gen_i32(1, 2000);
            let off = rng.gen_i32(-3, 3);
            let xc = clamp_i32(x2 + off, -10_000, 10_000);
            let yc = clamp_i32(y2 + off, -10_000, 10_000);
            (radius, xc, yc, x1, y1, x2, y2)
        }
        6 => {
            // tiny rectangle 1x1
            let x1 = rng.gen_i32(-10_000, 9_999);
            let x2 = x1 + 1;
            let y1 = rng.gen_i32(-10_000, 9_999);
            let y2 = y1 + 1;
            let radius = rng.gen_i32(1, 2000);
            let xc = rng.gen_i32(-10_000, 10_000);
            let yc = rng.gen_i32(-10_000, 10_000);
            (radius, xc, yc, x1, y1, x2, y2)
        }
        7 => {
            // max radius
            let radius = 2000;
            let xc = rng.gen_i32(-10_000, 10_000);
            let yc = rng.gen_i32(-10_000, 10_000);
            let x1 = rng.gen_i32(-10_000, 9_999);
            let x2 = rng.gen_i32(x1 + 1, 10_000);
            let y1 = rng.gen_i32(-10_000, 9_999);
            let y2 = rng.gen_i32(y1 + 1, 10_000);
            (radius, xc, yc, x1, y1, x2, y2)
        }
        8 => {
            // min radius = 1
            let radius = 1;
            let xc = rng.gen_i32(-10_000, 10_000);
            let yc = rng.gen_i32(-10_000, 10_000);
            let x1 = rng.gen_i32(-10_000, 9_999);
            let x2 = rng.gen_i32(x1 + 1, 10_000);
            let y1 = rng.gen_i32(-10_000, 9_999);
            let y2 = rng.gen_i32(y1 + 1, 10_000);
            (radius, xc, yc, x1, y1, x2, y2)
        }
        9 => {
            // extreme coordinates
            let radius = rng.gen_i32(1, 2000);
            let xc = if rng.next_u64() % 2 == 0 { -10_000 } else { 10_000 };
            let yc = if rng.next_u64() % 2 == 0 { -10_000 } else { 10_000 };
            let x1 = -10_000; let x2 = 10_000;
            let y1 = -10_000; let y2 = 10_000;
            (radius, xc, yc, x1, y1, x2, y2)
        }
        _ => {
            // radius just barely reaches corner
            let x1 = rng.gen_i32(-3000, 0);
            let x2 = rng.gen_i32(x1 + 1, 3000);
            let y1 = rng.gen_i32(-3000, 0);
            let y2 = rng.gen_i32(y1 + 1, 3000);
            // place center diagonally from corner
            let dx = rng.gen_i32(1, 40);
            let dy = rng.gen_i32(1, 40);
            let xc = clamp_i32(x2 + dx, -10_000, 10_000);
            let yc = clamp_i32(y2 + dy, -10_000, 10_000);
            // radius close to sqrt(dx^2+dy^2)
            let d2 = (dx as i32) * (dx as i32) + (dy as i32) * (dy as i32);
            let mut r: i32 = 1;
            while (r + 1) * (r + 1) <= d2 && r < 2000 {
                r += 1;
            }
            let r = clamp_i32(r, 1, 2000);
            (r, xc, yc, x1, y1, x2, y2)
        }
    }
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
        let (radius, xc, yc, x1, y1, x2, y2) = build(&mut rng, mode);
        // safety clamp (should already be valid)
        let radius = clamp_i32(radius, 1, 2000);
        let xc = clamp_i32(xc, -10_000, 10_000);
        let yc = clamp_i32(yc, -10_000, 10_000);
        let x1c = clamp_i32(x1, -10_000, 10_000);
        let y1c = clamp_i32(y1, -10_000, 10_000);
        let x2c = clamp_i32(x2, -10_000, 10_000);
        let y2c = clamp_i32(y2, -10_000, 10_000);
        // ensure x1 < x2 and y1 < y2
        let (x1c, x2c) = if x1c >= x2c {
            if x1c < 10_000 { (x1c, x1c + 1) } else { (x1c - 1, x1c) }
        } else { (x1c, x2c) };
        let (y1c, y2c) = if y1c >= y2c {
            if y1c < 10_000 { (y1c, y1c + 1) } else { (y1c - 1, y1c) }
        } else { (y1c, y2c) };

        let (r, xc, yc, a, b, c, d) = generate_test_case(radius, xc, yc, x1c, y1c, x2c, y2c);
        println!(
            "{{\"radius\": {}, \"x_center\": {}, \"y_center\": {}, \"x1\": {}, \"y1\": {}, \"x2\": {}, \"y2\": {}}}",
            r, xc, yc, a, b, c, d
        );
    }
}