use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: i32, first_player: i32, second_player: i32) -> (result: (i32, i32, i32))
    requires
        2 <= n <= 28,
        1 <= first_player < second_player <= n,
    ensures
        result.0 == n && result.1 == first_player && result.2 == second_player,
{
    (n, first_player, second_player)
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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_case(rng: &mut Rng, mode: usize, idx: usize) -> (i32, i32, i32) {
    // returns (n, first, second)
    match mode {
        0 => {
            // smallest n
            let n = 2;
            (n, 1, 2)
        }
        1 => {
            // largest n, first=1, second=n
            let n = 28;
            (n, 1, n)
        }
        2 => {
            // adjacent players
            let n = rng.gen_range_i32(3, 28);
            let first = rng.gen_range_i32(1, n - 1);
            (n, first, first + 1)
        }
        3 => {
            // first and last
            let n = rng.gen_range_i32(2, 28);
            (n, 1, n)
        }
        4 => {
            // symmetric: first+second = n+1 (mirror pair)
            let n = rng.gen_range_i32(2, 28);
            let first = rng.gen_range_i32(1, n / 2);
            (n, first, n + 1 - first)
        }
        5 => {
            // both near the front
            let n = rng.gen_range_i32(4, 28);
            let first = 1;
            let second = rng.gen_range_i32(2, 4.min(n));
            (n, first, second)
        }
        6 => {
            // both near the back
            let n = rng.gen_range_i32(4, 28);
            let second = n;
            let lo = if n - 3 > 1 { n - 3 } else { 1 };
            let first = rng.gen_range_i32(lo, n - 1);
            (n, first, second)
        }
        7 => {
            // middle of row
            let n = rng.gen_range_i32(6, 28);
            let mid = n / 2;
            let first = mid;
            let second = mid + 1;
            (n, first, second)
        }
        8 => {
            // n = 11 example
            let n = 11;
            let first = rng.gen_range_i32(1, 10);
            let s_lo = first + 1;
            let second = rng.gen_range_i32(s_lo, 11);
            (n, first, second)
        }
        9 => {
            // n is power-of-two-ish
            let choices = [2i32, 4, 8, 16];
            let n = choices[idx % 4];
            let first = rng.gen_range_i32(1, n - 1);
            let s_lo = first + 1;
            let second = rng.gen_range_i32(s_lo, n);
            (n, first, second)
        }
        _ => {
            // fully random
            let n = rng.gen_range_i32(2, 28);
            let first = rng.gen_range_i32(1, n - 1);
            let s_lo = first + 1;
            let second = rng.gen_range_i32(s_lo, n);
            (n, first, second)
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
        let (n, first, second) = pick_case(&mut rng, mode, t);

        // Validate bounds for safety before calling.
        if !(2 <= n && n <= 28 && 1 <= first && first < second && second <= n) {
            continue;
        }

        let (n_out, fp_out, sp_out) = generate_test_case(n, first, second);
        println!(
            "{{\"n\":{},\"first_player\":{},\"second_player\":{}}}",
            n_out, fp_out, sp_out
        );
    }
}