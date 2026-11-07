use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    raw_plants: &Vec<i32>,
    capacity: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= raw_plants.len() <= 1000,
        1 <= capacity <= 1000000000,
        forall|j: int| 0 <= j < raw_plants.len() ==> 1 <= #[trigger] raw_plants[j] <= 1000000,
        forall|j: int| 0 <= j < raw_plants.len() ==> #[trigger] raw_plants[j] <= capacity,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1 <= 1000000000,
        forall|j: int| 0 <= j < result.0.len() ==> 1 <= #[trigger] result.0[j] <= 1000000,
        forall|j: int| 0 <= j < result.0.len() ==> #[trigger] result.0[j] <= result.1,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < raw_plants.len()
        invariant
            0 <= i <= raw_plants.len(),
            out.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] out[k] == raw_plants[k],
            forall|j: int| 0 <= j < raw_plants.len() ==> 1 <= #[trigger] raw_plants[j] <= 1000000,
            forall|j: int| 0 <= j < raw_plants.len() ==> #[trigger] raw_plants[j] <= capacity,
        decreases raw_plants.len() - i,
    {
        out.push(raw_plants[i]);
        i += 1;
    }
    assert(out.len() == raw_plants.len());
    assert forall|j: int| 0 <= j < out.len() implies 1 <= #[trigger] out[j] <= 1000000 by {
        assert(out[j] == raw_plants[j]);
    }
    assert forall|j: int| 0 <= j < out.len() implies #[trigger] out[j] <= capacity by {
        assert(out[j] == raw_plants[j]);
    }
    (out, capacity)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_plants(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // small n=1
            let p = rng.gen_range_i32(1, 1000);
            let cap = rng.gen_range_i32(p, 1_000_000_000);
            (vec![p], cap)
        }
        1 => {
            // n=1000 max size, capacity tight (== max plant)
            let n = 1000;
            let mut v = Vec::with_capacity(n);
            let mut mx = 1;
            for _ in 0..n {
                let p = rng.gen_range_i32(1, 1_000_000);
                if p > mx { mx = p; }
                v.push(p);
            }
            (v, mx)
        }
        2 => {
            // capacity exactly max
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            let mut mx = 1;
            for _ in 0..n {
                let p = rng.gen_range_i32(1, 1_000_000);
                if p > mx { mx = p; }
                v.push(p);
            }
            (v, mx)
        }
        3 => {
            // capacity huge
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000));
            }
            (v, 1_000_000_000)
        }
        4 => {
            // all same value
            let n = rng.gen_range_usize(1, 1000);
            let p = rng.gen_range_i32(1, 1_000_000);
            let v = vec![p; n];
            let cap = rng.gen_range_i32(p, p.max(1_000_000));
            (v, cap)
        }
        5 => {
            // alternating small/large
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(1_000_000); }
            }
            (v, 1_000_000)
        }
        6 => {
            // capacity = 1 (requires all plants = 1)
            let n = rng.gen_range_usize(1, 1000);
            let v = vec![1i32; n];
            (v, 1)
        }
        7 => {
            // increasing
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            let mut cur = 1;
            for _ in 0..n {
                v.push(cur);
                if cur < 1_000_000 { cur += 1; }
            }
            (v, 1_000_000)
        }
        8 => {
            // force refill every plant: plants[i] > capacity/2 ish
            let cap = rng.gen_range_i32(2, 1_000_000);
            let half = cap / 2 + 1;
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(half, cap));
            }
            (v, cap)
        }
        9 => {
            // never refill: plants all tiny vs capacity
            let n = rng.gen_range_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
            (v, 1_000_000_000)
        }
        _ => {
            // fully random
            let n = rng.gen_range_usize(1, 1000);
            let mut v = Vec::with_capacity(n);
            let mut mx = 1;
            for _ in 0..n {
                let p = rng.gen_range_i32(1, 1_000_000);
                if p > mx { mx = p; }
                v.push(p);
            }
            let cap = rng.gen_range_i32(mx, 1_000_000_000);
            let _ = t;
            (v, cap)
        }
    }
}

fn print_json(plants: &[i32], capacity: i32) {
    print!("{{\"plants\":[");
    for i in 0..plants.len() {
        if i > 0 { print!(","); }
        print!("{}", plants[i]);
    }
    println!("],\"capacity\":{}}}", capacity);
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
        let (raw, cap) = build_plants(&mut rng, mode, t);
        let (plants, capacity) = generate_test_case(&raw, cap);
        print_json(&plants, capacity);
    }
}