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
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => i32::MAX,
        3 => i32::MAX - 1,
        4 => {
            // powers of 2
            let k = (t % 30) as u32 + 1;
            1i32 << k
        }
        5 => {
            // powers of 2 minus 1 (odd, tricky)
            let k = (t % 30) as u32 + 2;
            (1i32 << k) - 1
        }
        6 => {
            // powers of 2 plus 1
            let k = (t % 30) as u32 + 2;
            (1i32 << k) + 1
        }
        7 => {
            // small values
            rng.gen_range_i32(1, 20)
        }
        8 => {
            // medium odd values
            let v = rng.gen_range_i32(1, 100000);
            if v % 2 == 0 { v + 1 } else { v }
        }
        9 => {
            // large odd values
            let v = rng.gen_range_i32(1_000_000, 2_000_000_000);
            if v % 2 == 0 { v.saturating_add(1).min(i32::MAX) } else { v }
        }
        10 => {
            // trailing 1s pattern: ...0111
            let k = (t % 28) as u32 + 3;
            (1i32 << k) - 1
        }
        11 => {
            // specific known tricky: 2147483647
            2147483647
        }
        _ => {
            rng.gen_range_i32(1, i32::MAX)
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
    let modes = 13usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = pick_for_mode(&mut rng, mode, t);
        let n = if n < 1 { 1 } else { n };
        let n = generate_test_case(n);
        println!("{{\"n\":{}}}", n);
    }
}