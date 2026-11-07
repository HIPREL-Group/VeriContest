use vstd::prelude::*;

verus! {

pub fn generate_test_case(low: i32, high: i32) -> (res: (i32, i32))
    requires
        0 <= low <= high <= 1_000_000_000,
    ensures
        0 <= res.0 <= res.1 <= 1_000_000_000,
{
    (low, high)
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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    const MAXV: i32 = 1_000_000_000;
    match mode {
        0 => (0, 0),
        1 => (1, 1),
        2 => (0, MAXV),
        3 => (MAXV, MAXV),
        4 => (MAXV - 1, MAXV),
        5 => {
            // small range
            let l = rng.gen_range_i32(0, 20);
            let h = rng.gen_range_i32(l, 20);
            (l, h)
        }
        6 => {
            // equal values
            let v = rng.gen_range_i32(0, MAXV);
            (v, v)
        }
        7 => {
            // both even boundary
            let l = rng.gen_range_i32(0, MAXV / 2) * 2;
            let lc = if l > MAXV { MAXV } else { l };
            let h = rng.gen_range_i32(lc, MAXV);
            let hc = (h / 2) * 2;
            let hc2 = if hc < lc { lc } else { hc };
            (lc, hc2)
        }
        8 => {
            // both odd boundary
            let l0 = rng.gen_range_i32(0, MAXV - 1);
            let l = if l0 % 2 == 0 { l0 + 1 } else { l0 };
            let l = if l > MAXV { MAXV } else { l };
            let h0 = rng.gen_range_i32(l, MAXV);
            let h = if h0 % 2 == 0 {
                if h0 == 0 { 1 } else { h0 - 1 }
            } else {
                h0
            };
            let h = if h < l { l } else { h };
            (l, h)
        }
        9 => {
            // large near max
            let l = rng.gen_range_i32(MAXV - 100, MAXV);
            let h = rng.gen_range_i32(l, MAXV);
            (l, h)
        }
        _ => {
            let l = rng.gen_range_i32(0, MAXV);
            let h = rng.gen_range_i32(l, MAXV);
            (l, h)
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (low, high) = pick_case(&mut rng, mode);
        // Clamp just in case
        let low = if low < 0 { 0 } else if low > 1_000_000_000 { 1_000_000_000 } else { low };
        let high = if high < low { low } else if high > 1_000_000_000 { 1_000_000_000 } else { high };
        let (l, h) = generate_test_case(low, high);
        println!("{{\"low\": {}, \"high\": {}}}", l, h);
    }
}