use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    hours: Vec<i32>,
    target: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= hours.len() <= 50,
        0 <= target <= 100_000,
        forall |i: int| 0 <= i < hours.len() ==> 0 <= #[trigger] hours[i] <= 100_000,
    ensures
        1 <= res.0.len() <= 50,
        0 <= res.1 <= 100_000,
        forall |i: int| 0 <= i < res.0.len() ==> 0 <= #[trigger] res.0[i] <= 100_000,
{
    (hours, target)
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

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // all zeros, target 0
            let n = rng.gen_range_usize(1, 50);
            let h = vec![0i32; n];
            (h, 0)
        }
        1 => {
            // all zeros, target > 0
            let n = rng.gen_range_usize(1, 50);
            let h = vec![0i32; n];
            let t = rng.gen_range_i32(1, 100_000);
            (h, t)
        }
        2 => {
            // all at max, target max
            let n = rng.gen_range_usize(1, 50);
            let h = vec![100_000i32; n];
            (h, 100_000)
        }
        3 => {
            // all equal to target
            let n = rng.gen_range_usize(1, 50);
            let t = rng.gen_range_i32(0, 100_000);
            let h = vec![t; n];
            (h, t)
        }
        4 => {
            // all equal target-1 (none meets) when t>0
            let n = rng.gen_range_usize(1, 50);
            let t = rng.gen_range_i32(1, 100_000);
            let h = vec![t - 1; n];
            (h, t)
        }
        5 => {
            // single element
            let t = rng.gen_range_i32(0, 100_000);
            let v = rng.gen_range_i32(0, 100_000);
            (vec![v], t)
        }
        6 => {
            // max length, random
            let n = 50usize;
            let t = rng.gen_range_i32(0, 100_000);
            let mut h = Vec::with_capacity(n);
            for _ in 0..n {
                h.push(rng.gen_range_i32(0, 100_000));
            }
            (h, t)
        }
        7 => {
            // boundary values mix
            let n = rng.gen_range_usize(1, 50);
            let mut h = Vec::with_capacity(n);
            for _ in 0..n {
                let pick = rng.next_u64() % 3;
                let v = match pick { 0 => 0, 1 => 100_000, _ => rng.gen_range_i32(0, 100_000) };
                h.push(v);
            }
            let t = rng.gen_range_i32(0, 100_000);
            (h, t)
        }
        8 => {
            // target = 0 (everyone meets)
            let n = rng.gen_range_usize(1, 50);
            let mut h = Vec::with_capacity(n);
            for _ in 0..n {
                h.push(rng.gen_range_i32(0, 100_000));
            }
            (h, 0)
        }
        9 => {
            // target = 100_000, various values
            let n = rng.gen_range_usize(1, 50);
            let mut h = Vec::with_capacity(n);
            for _ in 0..n {
                let pick = rng.next_u64() % 2;
                let v = if pick == 0 { 100_000 } else { rng.gen_range_i32(0, 100_000) };
                h.push(v);
            }
            (h, 100_000)
        }
        _ => {
            let n = rng.gen_range_usize(1, 50);
            let mut h = Vec::with_capacity(n);
            for _ in 0..n {
                h.push(rng.gen_range_i32(0, 100_000));
            }
            let t = rng.gen_range_i32(0, 100_000);
            (h, t)
        }
    }
}

fn print_json(hours: &[i32], target: i32) {
    print!("{{\"hours\":[");
    for i in 0..hours.len() {
        if i > 0 { print!(","); }
        print!("{}", hours[i]);
    }
    println!("],\"target\":{}}}", target);
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
        let (hours, target) = build_case(&mut rng, mode);
        // sanity check constraints before calling verified generator
        let n = hours.len();
        if n < 1 || n > 50 { continue; }
        if target < 0 || target > 100_000 { continue; }
        let mut ok = true;
        for &v in &hours {
            if v < 0 || v > 100_000 { ok = false; break; }
        }
        if !ok { continue; }
        let (h, tt) = generate_test_case(hours, target);
        print_json(&h, tt);
    }
}