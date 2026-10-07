use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    ax1: i32, ay1_delta: i32, ax2_delta: i32, ay2_delta_extra: i32,
    bx1: i32, by1_delta: i32, bx2_delta: i32, by2_delta_extra: i32,
) -> (res: (i32, i32, i32, i32, i32, i32, i32, i32))
    requires
        -10_000 <= ax1 <= 10_000,
        -10_000 <= bx1 <= 10_000,
        0 <= ay1_delta,
        ay1_delta as int + ax1 as int <= 10_000,
        0 <= ax2_delta,
        ax2_delta as int + ax1 as int <= 10_000,
        0 <= ay2_delta_extra,
        ay2_delta_extra as int + ax1 as int + ay1_delta as int <= 10_000,
        0 <= by1_delta,
        by1_delta as int + bx1 as int <= 10_000,
        0 <= bx2_delta,
        bx2_delta as int + bx1 as int <= 10_000,
        0 <= by2_delta_extra,
        by2_delta_extra as int + bx1 as int + by1_delta as int <= 10_000,
    ensures ({
        let (ax1r, ay1r, ax2r, ay2r, bx1r, by1r, bx2r, by2r) = res;
        &&& -10_000 <= ax1r <= ax2r <= 10_000
        &&& -10_000 <= ay1r <= ay2r <= 10_000
        &&& -10_000 <= bx1r <= bx2r <= 10_000
        &&& -10_000 <= by1r <= by2r <= 10_000
    }),
{
    let ay1: i32 = ax1 + ay1_delta;
    let ax2: i32 = ax1 + ax2_delta;
    let ay2: i32 = ay1 + ay2_delta_extra;
    let by1: i32 = bx1 + by1_delta;
    let bx2: i32 = bx1 + bx2_delta;
    let by2: i32 = by1 + by2_delta_extra;

    // Now we need ay1 >= -10000 and ay2 <= 10000 etc. But ay1 = ax1+ay1_delta could be < -10000? 
    // ax1 >= -10000, ay1_delta >= 0, so ay1 >= -10000. ay1 <= 10000 from requires.
    // Similar for others.
    
    (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2)
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

// Given desired x1, x2, y1, y2 with x1<=x2, y1<=y2 in [-10000, 10000],
// compute decomposed parameters. Here ax1=x1, ay1_delta = y1 - x1 (must be >=0),
// but that's not always >=0. Instead, we have the freedom: encode as
// ax1 is the x1 value, and ay1 = ax1 + ay1_delta => ay1_delta = ay1 - ax1.
// This requires ay1 >= ax1. Not always.
//
// Let me change strategy: just use the decomposition but ensure we can
// satisfy it. Pick ax1 = min(x1, y1_desired) so deltas are >=0? No, better:
// Let me use ax1 as-is, and treat ay1_delta as nonneg offset from ax1.
// Since we want ay1 in [-10000, 10000] and ax1 in [-10000, 10000], and
// ay1_delta >=0 forces ay1 >= ax1. So generator must satisfy ay1 >= ax1.
//
// Simplest: just pick ax1 = -10000 as the base, then generate ay1, ax2, ay2 as offsets.

fn gen_rect(rng: &mut Rng) -> (i32, i32, i32, i32, i32, i32, i32, i32) {
    // For rectangle A: pick ax1, then ay1 >= ax1, ax2 >= ax1, ay2 >= ay1.
    // This works because we set ax1 low enough.
    let ax1 = rng.gen_range_i32(-10_000, -5_000);
    let ay1_delta = rng.gen_range_i32(0, 10_000 - ax1);
    let ax2_delta = rng.gen_range_i32(0, 10_000 - ax1);
    let ay1 = ax1 + ay1_delta;
    let ay2_delta_extra = rng.gen_range_i32(0, 10_000 - ay1);

    let bx1 = rng.gen_range_i32(-10_000, -5_000);
    let by1_delta = rng.gen_range_i32(0, 10_000 - bx1);
    let bx2_delta = rng.gen_range_i32(0, 10_000 - bx1);
    let by1 = bx1 + by1_delta;
    let by2_delta_extra = rng.gen_range_i32(0, 10_000 - by1);

    generate_test_case(ax1, ay1_delta, ax2_delta, ay2_delta_extra, bx1, by1_delta, bx2_delta, by2_delta_extra)
}

fn gen_adversarial(rng: &mut Rng, mode: usize) -> (i32, i32, i32, i32, i32, i32, i32, i32) {
    match mode {
        0 => {
            // Both rectangles degenerate points
            let ax1 = rng.gen_range_i32(-10_000, 10_000);
            let bx1 = rng.gen_range_i32(-10_000, 10_000);
            generate_test_case(ax1, 0, 0, 0, bx1, 0, 0, 0)
        }
        1 => {
            // Identical rectangles at max extent
            generate_test_case(-10_000, 0, 20_000, 20_000, -10_000, 0, 20_000, 20_000)
        }
        2 => {
            // Disjoint
            generate_test_case(-10_000, 0, 5_000, 5_000, 0, 0, 10_000, 10_000)
        }
        3 => {
            // One contained in other
            generate_test_case(-10_000, 0, 20_000, 20_000, -5_000, 0, 5_000, 5_000)
        }
        4 => {
            // Edge-touching
            generate_test_case(-10_000, 0, 5_000, 5_000, -5_000, 0, 5_000, 5_000)
        }
        5 => {
            // Corner-touching
            generate_test_case(-10_000, 0, 5_000, 5_000, -5_000, 5_000, 5_000, 5_000)
        }
        6 => {
            // Thin strip
            generate_test_case(-10_000, 0, 20_000, 0, -10_000, 0, 20_000, 20_000)
        }
        7 => {
            // Both degenerate (lines)
            generate_test_case(-5_000, 0, 10_000, 0, -5_000, 10_000, 10_000, 0)
        }
        8 => {
            // Maximum area
            generate_test_case(-10_000, 0, 20_000, 20_000, -10_000, 0, 20_000, 20_000)
        }
        9 => {
            // Partial overlap
            let _ = rng.next_u64();
            generate_test_case(-10_000, 5_000, 10_000, 5_000, -5_000, 0, 10_000, 10_000)
        }
        _ => gen_rect(rng),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let (ax1, ay1, ax2, ay2, bx1, by1, bx2, by2) = if t < 10 {
            gen_adversarial(&mut rng, t)
        } else if t % 7 == 0 {
            gen_adversarial(&mut rng, t % 10)
        } else {
            gen_rect(&mut rng)
        };
        println!(
            "{{\"ax1\":{},\"ay1\":{},\"ax2\":{},\"ay2\":{},\"bx1\":{},\"by1\":{},\"bx2\":{},\"by2\":{}}}",
            ax1, ay1, ax2, ay2, bx1, by1, bx2, by2
        );
    }
}