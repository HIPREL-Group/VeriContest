use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    x1a: i32, y1a: i32, x2a: i32, y2a: i32,
    x1b: i32, y1b: i32, x2b: i32, y2b: i32,
) -> (res: (Vec<i32>, Vec<i32>))
    requires
        -1_000_000_000 <= x1a <= 1_000_000_000,
        -1_000_000_000 <= y1a <= 1_000_000_000,
        -1_000_000_000 <= x2a <= 1_000_000_000,
        -1_000_000_000 <= y2a <= 1_000_000_000,
        -1_000_000_000 <= x1b <= 1_000_000_000,
        -1_000_000_000 <= y1b <= 1_000_000_000,
        -1_000_000_000 <= x2b <= 1_000_000_000,
        -1_000_000_000 <= y2b <= 1_000_000_000,
        x2a > x1a,
        y2a > y1a,
        x2b > x1b,
        y2b > y1b,
    ensures
        res.0.len() == 4,
        res.1.len() == 4,
        forall |i: int| 0 <= i < res.0.len()
            ==> -1_000_000_000 <= #[trigger] res.0[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < res.1.len()
            ==> -1_000_000_000 <= #[trigger] res.1[i] <= 1_000_000_000,
        res.0[2] > res.0[0],
        res.0[3] > res.0[1],
        res.1[2] > res.1[0],
        res.1[3] > res.1[1],
{
    let mut rec1: Vec<i32> = Vec::new();
    rec1.push(x1a);
    rec1.push(y1a);
    rec1.push(x2a);
    rec1.push(y2a);

    let mut rec2: Vec<i32> = Vec::new();
    rec2.push(x1b);
    rec2.push(y1b);
    rec2.push(x2b);
    rec2.push(y2b);

    assert(rec1.len() == 4);
    assert(rec1[0] == x1a);
    assert(rec1[1] == y1a);
    assert(rec1[2] == x2a);
    assert(rec1[3] == y2a);
    assert(rec2[0] == x1b);
    assert(rec2[1] == y1b);
    assert(rec2[2] == x2b);
    assert(rec2[3] == y2b);

    (rec1, rec2)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        (lo as i64 + v as i64) as i32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn random_valid_rect(rng: &mut Rng) -> (i32, i32, i32, i32) {
    let lo: i32 = -1_000_000_000;
    let hi: i32 = 1_000_000_000;
    let x1 = rng.gen_range_i32(lo, hi - 1);
    let x2 = rng.gen_range_i32(x1 + 1, hi);
    let y1 = rng.gen_range_i32(lo, hi - 1);
    let y2 = rng.gen_range_i32(y1 + 1, hi);
    (x1, y1, x2, y2)
}

fn small_rect(rng: &mut Rng) -> (i32, i32, i32, i32) {
    let x1 = rng.gen_range_i32(-10, 9);
    let x2 = rng.gen_range_i32(x1 + 1, 10);
    let y1 = rng.gen_range_i32(-10, 9);
    let y2 = rng.gen_range_i32(y1 + 1, 10);
    (x1, y1, x2, y2)
}

fn build_case(rng: &mut Rng, mode: usize) -> ((i32, i32, i32, i32), (i32, i32, i32, i32)) {
    let lo: i32 = -1_000_000_000;
    let hi: i32 = 1_000_000_000;
    match mode {
        0 => {
            // Both random
            (random_valid_rect(rng), random_valid_rect(rng))
        }
        1 => {
            // Both small (high collision chance)
            (small_rect(rng), small_rect(rng))
        }
        2 => {
            // Edge touching horizontally (should NOT overlap)
            let r1 = (0, 0, 5, 5);
            let r2 = (5, rng.gen_range_i32(-3, 3), rng.gen_range_i32(6, 10), rng.gen_range_i32(4, 10));
            let r2 = (r2.0, r2.1, r2.2, if r2.3 > r2.1 { r2.3 } else { r2.1 + 1 });
            (r1, r2)
        }
        3 => {
            // Edge touching vertically (should NOT overlap)
            let r1 = (0, 0, 5, 5);
            let y2 = rng.gen_range_i32(6, 10);
            let x1v = rng.gen_range_i32(-3, 3);
            let x2v = rng.gen_range_i32(x1v + 1, 10);
            let r2 = (x1v, 5, x2v, y2);
            (r1, r2)
        }
        4 => {
            // Corner touching (should NOT overlap)
            let r1 = (0, 0, 5, 5);
            let r2 = (5, 5, 10, 10);
            (r1, r2)
        }
        5 => {
            // Rec2 fully inside Rec1 (overlap)
            let r1 = (-100, -100, 100, 100);
            let x1v = rng.gen_range_i32(-50, 0);
            let x2v = rng.gen_range_i32(x1v + 1, 50);
            let y1v = rng.gen_range_i32(-50, 0);
            let y2v = rng.gen_range_i32(y1v + 1, 50);
            (r1, (x1v, y1v, x2v, y2v))
        }
        6 => {
            // Identical
            let r = small_rect(rng);
            (r, r)
        }
        7 => {
            // Extreme bounds
            (( lo, lo, hi, hi ), ( lo + 1, lo + 1, hi - 1, hi - 1 ))
        }
        8 => {
            // Far apart (no overlap)
            let r1 = (-1_000_000_000, -1_000_000_000, -999_999_000, -999_999_000);
            let r2 = (999_999_000, 999_999_000, 1_000_000_000, 1_000_000_000);
            (r1, r2)
        }
        9 => {
            // Partial overlap
            let r1 = (0, 0, 10, 10);
            let x1v = rng.gen_range_i32(5, 9);
            let y1v = rng.gen_range_i32(5, 9);
            let x2v = rng.gen_range_i32(x1v + 1, 20);
            let y2v = rng.gen_range_i32(y1v + 1, 20);
            (r1, (x1v, y1v, x2v, y2v))
        }
        _ => {
            // Overlap on one axis only (x overlaps, y doesn't)
            let r1 = (0, 0, 10, 10);
            let x1v = rng.gen_range_i32(2, 8);
            let x2v = rng.gen_range_i32(x1v + 1, 12);
            let r2 = (x1v, 10, x2v, 20);
            (r1, r2)
        }
    }
}

fn print_json(r1: (i32, i32, i32, i32), r2: (i32, i32, i32, i32)) {
    println!(
        "{{\"rec1\":[{},{},{},{}],\"rec2\":[{},{},{},{}]}}",
        r1.0, r1.1, r1.2, r1.3, r2.0, r2.1, r2.2, r2.3
    );
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
        let mode = if t < 22 { t % modes } else { rng.gen_range_usize(0, modes - 1) };
        let (r1, r2) = build_case(&mut rng, mode);
        // Call verified generator
        let (v1, v2) = generate_test_case(r1.0, r1.1, r1.2, r1.3, r2.0, r2.1, r2.2, r2.3);
        let a = (v1[0], v1[1], v1[2], v1[3]);
        let b = (v2[0], v2[1], v2[2], v2[3]);
        print_json(a, b);
    }
}