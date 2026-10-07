use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_base: i32,
    k_base: i32,
    target_bias: i32,
    choose_upper: bool,
    _filler: &Vec<i32>,
) -> (triple: (i32, i32, i32))
    ensures
        1 <= triple.0 <= 30,
        1 <= triple.1 <= 30,
        1 <= triple.2 <= 1000,
        1 <= triple.0 <= 30,
        1 <= triple.1 <= 30,
        1 <= triple.2 <= 1000,
{
    let n_base = if n_base < 0 { 0 } else if n_base > 29 { 29 } else { n_base };
    let k_base = if k_base < 0 { 0 } else if k_base > 29 { 29 } else { k_base };
    let target_bias = if target_bias < 0 { 0 } else if target_bias > 969 { 969 } else { target_bias };
        let n = n_base + 1;
        let k = k_base + 1;
        let target =
            if choose_upper {
                1000 - target_bias
            } else {
                target_bias + 1
            };

        assert(1 <= n <= 30);
        assert(1 <= k <= 30);
        assert(1 <= target <= 1000);

        (n, k, target)
    }
}

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

    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as u32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 1
    }
}

fn make_filler(len: usize, seed: u64) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    let mut x = seed.wrapping_add(17);
    while v.len() < len {
        x = x.wrapping_mul(1103515245).wrapping_add(12345);
        v.push((x % 1024) as i32);
    }
    v
}

fn adversarial_case(rng: &mut Rng, mode: usize, idx: usize) -> (i32, i32, i32, Vec<i32>) {
    match mode {
        0 => (1, 1, 1, make_filler(0, idx as u64)),
        1 => (30, 30, 1000, make_filler(1, idx as u64)),
        2 => (1, 30, 1000, make_filler(2, idx as u64)),
        3 => (30, 1, 1, make_filler(3, idx as u64)),
        4 => (29, 29, 969, make_filler(4, idx as u64)),
        5 => (0, 0, 0, make_filler(5, idx as u64)),
        6 => (29, 0, 999, make_filler(6, idx as u64)),
        7 => (0, 29, 500, make_filler(7, idx as u64)),
        8 => {
            let b = (idx % 970) as i32;
            (15, 15, b, make_filler(8, idx as u64))
        }
        9 => {
            let b = (idx % 970) as i32;
            (rng.gen_range_u32(0, 29) as i32, rng.gen_range_u32(0, 29) as i32, b, make_filler(9, idx as u64))
        }
        _ => {
            let nb = rng.gen_range_u32(0, 29) as i32;
            let kb = rng.gen_range_u32(0, 29) as i32;
            let tb = rng.gen_range_u32(0, 969) as i32;
            (nb, kb, tb, make_filler(10, idx as u64))
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
    let modes = 10usize;

    let mut i = 0usize;
    while i < total {
        let mode = i % modes;
        let (n_base, k_base, target_bias, filler) = if i < 120 {
            adversarial_case(&mut rng, mode, i)
        } else {
            (
                rng.gen_range_u32(0, 29) as i32,
                rng.gen_range_u32(0, 29) as i32,
                rng.gen_range_u32(0, 969) as i32,
                make_filler((i % 11) + 1, i as u64),
            )
        };

        let choose_upper = match mode {
            0 => false,
            1 => true,
            2 => true,
            3 => false,
            4 => true,
            5 => false,
            6 => true,
            7 => false,
            8 => rng.gen_bool(),
            _ => rng.gen_bool(),
        };

        let (n, k, target) =
            generate_test_case(n_base, k_base, target_bias, choose_upper, &filler);

        println!("{{\"n\":{},\"k\":{},\"target\":{}}}", n, k, target);
        i += 1;
    }
}
