use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32) -> (res: i32)
    requires
        1 <= n <= i32::MAX,
    ensures
        1 <= res <= i32::MAX,
        res == n,
{
    n
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => i32::MAX,
        3 => i32::MAX - 1,
        4 => {
            // perfect triangular numbers: k*(k+1)/2
            let k = rng.gen_range_i32(1, 65535) as i64;
            let tri = k * (k + 1) / 2;
            if tri > i32::MAX as i64 { i32::MAX } else { tri as i32 }
        }
        5 => {
            // one less than triangular
            let k = rng.gen_range_i32(2, 65535) as i64;
            let tri = k * (k + 1) / 2 - 1;
            if tri < 1 { 1 } else if tri > i32::MAX as i64 { i32::MAX } else { tri as i32 }
        }
        6 => {
            // one more than triangular
            let k = rng.gen_range_i32(1, 65534) as i64;
            let tri = k * (k + 1) / 2 + 1;
            if tri > i32::MAX as i64 { i32::MAX } else { tri as i32 }
        }
        7 => rng.gen_range_i32(1, 100),
        8 => rng.gen_range_i32(1, 10000),
        9 => rng.gen_range_i32(1_000_000_000, i32::MAX),
        _ => {
            let small = [1, 2, 3, 5, 6, 8, 10, 15, 21, 28, 36, 45, 55];
            small[t % small.len()]
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_for_mode(&mut rng, mode, t);
        let v = generate_test_case(n);
        println!("{{\"n\": {}}}", v);
    }
}