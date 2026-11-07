use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    num_ones: i32,
    num_zeros: i32,
    num_neg_ones: i32,
    k: i32,
) -> (result: (i32, i32, i32, i32))
    requires
        0 <= num_ones <= 50,
        0 <= num_zeros <= 50,
        0 <= num_neg_ones <= 50,
        0 <= k,
        k as int <= num_ones as int + num_zeros as int + num_neg_ones as int,
    ensures
        ({
            let (a, b, c, d) = result;
            &&& 0 <= a <= 50
            &&& 0 <= b <= 50
            &&& 0 <= c <= 50
            &&& 0 <= d
            &&& d as int <= a as int + b as int + c as int
            &&& a == num_ones
            &&& b == num_zeros
            &&& c == num_neg_ones
            &&& d == k
        }),
{
    (num_ones, num_zeros, num_neg_ones, k)
}

}

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32, i32, i32) {
    match mode {
        0 => (0, 0, 0, 0),
        1 => (50, 50, 50, 0),
        2 => (50, 50, 50, 150),
        3 => {
            let n1 = rng.gen_range_i32(0, 50);
            (n1, 0, 0, n1)
        }
        4 => {
            let n1 = rng.gen_range_i32(1, 50);
            let k = rng.gen_range_i32(0, n1);
            (n1, 0, 0, k)
        }
        5 => {
            let n1 = rng.gen_range_i32(0, 50);
            let n0 = rng.gen_range_i32(0, 50);
            let k = rng.gen_range_i32(0, n1 + n0);
            (n1, n0, 0, k)
        }
        6 => {
            let nn = rng.gen_range_i32(1, 50);
            let k = rng.gen_range_i32(0, nn);
            (0, 0, nn, k)
        }
        7 => {
            let n1 = rng.gen_range_i32(0, 50);
            let nn = rng.gen_range_i32(0, 50);
            let k = rng.gen_range_i32(0, n1 + nn);
            (n1, 0, nn, k)
        }
        8 => {
            // k exactly at boundary num_ones
            let n1 = rng.gen_range_i32(1, 50);
            let n0 = rng.gen_range_i32(0, 50);
            let nn = rng.gen_range_i32(0, 50);
            (n1, n0, nn, n1)
        }
        9 => {
            // k at boundary num_ones + num_zeros
            let n1 = rng.gen_range_i32(0, 50);
            let n0 = rng.gen_range_i32(0, 50);
            let nn = rng.gen_range_i32(0, 50);
            (n1, n0, nn, n1 + n0)
        }
        10 => {
            // k = total
            let n1 = rng.gen_range_i32(0, 50);
            let n0 = rng.gen_range_i32(0, 50);
            let nn = rng.gen_range_i32(0, 50);
            (n1, n0, nn, n1 + n0 + nn)
        }
        _ => {
            let n1 = rng.gen_range_i32(0, 50);
            let n0 = rng.gen_range_i32(0, 50);
            let nn = rng.gen_range_i32(0, 50);
            let total = n1 + n0 + nn;
            let k = if total == 0 { 0 } else { rng.gen_range_i32(0, total) };
            (n1, n0, nn, k)
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
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = if t < modes { t } else { (rng.next_u64() as usize) % modes };
        let (n1, n0, nn, k) = pick_case(&mut rng, mode);
        let (a, b, c, d) = generate_test_case(n1, n0, nn, k);
        println!(
            "{{\"num_ones\": {}, \"num_zeros\": {}, \"num_neg_ones\": {}, \"k\": {}}}",
            a, b, c, d
        );
    }
}