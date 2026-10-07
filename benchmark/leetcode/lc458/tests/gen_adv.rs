use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    buckets: i32,
    minutes_to_die: i32,
    minutes_to_test_extra: i32,
) -> (result: (i32, i32, i32))
    requires
        1 <= buckets <= 1000,
        1 <= minutes_to_die <= 100,
        0 <= minutes_to_test_extra,
        minutes_to_die as int + minutes_to_test_extra as int <= 100,
    ensures
        1 <= result.0 <= 1000,
        1 <= result.1 <= result.2 <= 100,
        1 <= result.2 as int / result.1 as int,
{
    let mtt: i32 = minutes_to_die + minutes_to_test_extra;
    assert(mtt >= minutes_to_die);
    assert(mtt <= 100);
    assert(mtt >= 1);
    assert(minutes_to_die >= 1);
    assert(mtt / minutes_to_die >= 1) by (nonlinear_arith)
        requires mtt >= minutes_to_die, minutes_to_die >= 1;
    (buckets, minutes_to_die, mtt)
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
    // returns (buckets, minutes_to_die, minutes_to_test_extra)
    match mode {
        0 => (1, 1, 0),
        1 => (1000, 1, 99),
        2 => (1000, 100, 0),
        3 => (1, 100, 0),
        4 => (4, 15, 0),   // example 1: mtt=15
        5 => {
            // example 2: buckets=4, mtd=15, mtt=30 -> extra=15
            (4, 15, 15)
        }
        6 => {
            let mtd = rng.gen_range_i32(1, 50);
            let extra = rng.gen_range_i32(0, 100 - mtd);
            let b = rng.gen_range_i32(1, 1000);
            (b, mtd, extra)
        }
        7 => {
            // mtd == mtt
            let mtd = rng.gen_range_i32(1, 100);
            let b = rng.gen_range_i32(1, 1000);
            (b, mtd, 0)
        }
        8 => {
            // mtt is large multiple of mtd
            let mtd = rng.gen_range_i32(1, 10);
            let mtt = rng.gen_range_i32(mtd, 100);
            let b = rng.gen_range_i32(1, 1000);
            (b, mtd, mtt - mtd)
        }
        9 => {
            // small buckets
            let mtd = rng.gen_range_i32(1, 100);
            let extra = rng.gen_range_i32(0, 100 - mtd);
            let b = rng.gen_range_i32(1, 5);
            (b, mtd, extra)
        }
        _ => {
            let mtd = rng.gen_range_i32(1, 100);
            let extra = rng.gen_range_i32(0, 100 - mtd);
            let b = rng.gen_range_i32(1, 1000);
            (b, mtd, extra)
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
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (b, mtd, extra) = pick(&mut rng, mode);
        let (buckets, minutes_to_die, minutes_to_test) = generate_test_case(b, mtd, extra);
        println!(
            "{{\"buckets\": {}, \"minutes_to_die\": {}, \"minutes_to_test\": {}}}",
            buckets, minutes_to_die, minutes_to_test
        );
    }
}