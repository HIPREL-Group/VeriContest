use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    energies: &Vec<i32>,
    current_energy: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= energies.len() <= 100000,
        0 <= current_energy <= 1000000000,
        forall |i: int| 0 <= i < energies.len() ==> 1 <= #[trigger] energies[i] <= 1000000000,
    ensures
        1 <= result.0.len() <= 100000,
        0 <= result.1 <= 1000000000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1000000000,
{
    let mut out: Vec<i32> = Vec::new();
    let n = energies.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == energies.len(),
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] out[k] <= 1000000000,
            forall |k: int| 0 <= k < energies.len() ==> 1 <= #[trigger] energies[k] <= 1000000000,
        decreases n - i,
    {
        out.push(energies[i]);
        i = i + 1;
    }
    (out, current_energy)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            let ce = rng.gen_range_i32(0, 100);
            (v, ce)
        }
        1 => {
            // single enemy, large energy
            (vec![rng.gen_range_i32(1, 1_000_000_000)], rng.gen_range_i32(0, 1_000_000_000))
        }
        2 => {
            // current_energy = 0
            let n = rng.gen_range_usize(1, 20);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            (v, 0)
        }
        3 => {
            // all enemies have energy 1
            let n = rng.gen_range_usize(1, 100);
            let v = vec![1i32; n];
            (v, rng.gen_range_i32(0, 1_000_000_000))
        }
        4 => {
            // all max energy
            let n = rng.gen_range_usize(1, 100);
            let v = vec![1_000_000_000i32; n];
            (v, rng.gen_range_i32(0, 1_000_000_000))
        }
        5 => {
            // current_energy smaller than min enemy
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(100, 1_000_000_000));
            }
            (v, rng.gen_range_i32(0, 99))
        }
        6 => {
            // sorted ascending
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            let mut cur = 1i32;
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_add(rng.gen_range_i32(1, 1000));
                if cur > 1_000_000_000 { cur = 1_000_000_000; }
            }
            (v, rng.gen_range_i32(0, 1_000_000_000))
        }
        7 => {
            // large size
            let n = 100_000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            (v, rng.gen_range_i32(0, 1_000_000_000))
        }
        8 => {
            // two enemies
            let a = rng.gen_range_i32(1, 1_000_000_000);
            let b = rng.gen_range_i32(1, 1_000_000_000);
            (vec![a, b], rng.gen_range_i32(0, 1_000_000_000))
        }
        9 => {
            // min enemy exactly equals current_energy
            let n = rng.gen_range_usize(2, 30);
            let ce = rng.gen_range_i32(1, 1000);
            let mut v = vec![ce];
            for _ in 1..n {
                v.push(rng.gen_range_i32(ce, 1_000_000_000));
            }
            (v, ce)
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000_000));
            }
            (v, rng.gen_range_i32(0, 1_000_000_000))
        }
    }
}

fn print_json(energies: &[i32], ce: i32) {
    print!("{{\"enemy_energies\":[");
    for i in 0..energies.len() {
        if i > 0 { print!(","); }
        print!("{}", energies[i]);
    }
    println!("],\"current_energy\":{}}}", ce);
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

    for t in 0..total {
        let mode = t % 11;
        let (v, ce) = build(&mut rng, mode);
        // sanity clamp (should always hold anyway)
        let mut ok = v.len() >= 1 && v.len() <= 100_000 && ce >= 0 && ce <= 1_000_000_000;
        for &x in &v {
            if x < 1 || x > 1_000_000_000 { ok = false; }
        }
        if !ok { continue; }
        let (out, out_ce) = generate_test_case(&v, ce);
        print_json(&out, out_ce);
    }
}