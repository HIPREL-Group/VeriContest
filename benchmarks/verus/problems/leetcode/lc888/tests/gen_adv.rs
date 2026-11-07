use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    idx: usize,
    value: bool,
) -> (result: (Vec<bool>, usize, bool))
    requires
        1 <= len <= 10_000,
        idx < len,
    ensures
        result.0.len() == len,
        result.1 < result.0.len(),
        result.1 == idx,
{
    let mut flags: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            flags.len() == i,
        decreases len - i,
    {
        flags.push(false);
        i = i + 1;
    }
    (flags, idx, value)
}

} // verus!

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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_bool(&mut self) -> bool {
        self.next_u64() % 2 == 0
    }
}

fn pick_test(rng: &mut Rng, mode: usize) -> (usize, usize, bool) {
    match mode {
        0 => (1, 0, rng.gen_bool()),
        1 => {
            let n = rng.gen_range_usize(1, 10);
            (n, 0, rng.gen_bool())
        }
        2 => {
            let n = rng.gen_range_usize(2, 100);
            (n, n - 1, rng.gen_bool())
        }
        3 => {
            let n = 10_000;
            (n, 0, rng.gen_bool())
        }
        4 => {
            let n = 10_000;
            (n, n - 1, rng.gen_bool())
        }
        5 => {
            let n = 10_000;
            (n, rng.gen_range_usize(0, n - 1), rng.gen_bool())
        }
        6 => {
            let n = rng.gen_range_usize(1, 10_000);
            (n, n / 2, rng.gen_bool())
        }
        7 => {
            let n = rng.gen_range_usize(100, 1000);
            (n, rng.gen_range_usize(0, n - 1), true)
        }
        8 => {
            let n = rng.gen_range_usize(100, 1000);
            (n, rng.gen_range_usize(0, n - 1), false)
        }
        _ => {
            let n = rng.gen_range_usize(1, 10_000);
            (n, rng.gen_range_usize(0, n - 1), rng.gen_bool())
        }
    }
}

fn print_json(flags: &[bool], idx: usize, value: bool) {
    print!("{{\"flags\":[");
    for i in 0..flags.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", if flags[i] { "true" } else { "false" });
    }
    println!("],\"idx\":{},\"value\":{}}}", idx, if value { "true" } else { "false" });
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (len, idx, value) = pick_test(&mut rng, mode);
        let (flags, idx_out, value_out) = generate_test_case(len, idx, value);
        print_json(&flags, idx_out, value_out);
    }
}