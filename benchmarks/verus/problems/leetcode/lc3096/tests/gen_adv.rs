use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<u8>) -> (possible: Vec<i32>)
    requires
        2 <= bits.len() <= 100000,
        forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] == 0u8 || #[trigger] bits[i] == 1u8),
    ensures
        2 <= possible.len() <= 100000,
        possible.len() == bits.len(),
        forall |i: int| 0 <= i < possible.len() ==> (#[trigger] possible[i] == 0i32 || #[trigger] possible[i] == 1i32),
{
    let mut possible: Vec<i32> = Vec::new();
    let n = bits.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            possible.len() == i,
            forall |k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k] == 0u8 || #[trigger] bits[k] == 1u8),
            forall |k: int| 0 <= k < i ==> (#[trigger] possible[k] == 0i32 || #[trigger] possible[k] == 1i32),
        decreases n - i,
    {
        let v: i32 = if bits[i] == 1u8 { 1i32 } else { 0i32 };
        possible.push(v);
        i += 1;
    }
    possible
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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bit(&mut self) -> u8 {
        (self.next_u64() & 1) as u8
    }
}

fn make_bits_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    match mode {
        0 => {
            // all ones
            for i in 0..n { v[i] = 1; }
        }
        1 => {
            // all zeros
            for i in 0..n { v[i] = 0; }
        }
        2 => {
            // alternating 1,0,1,0
            for i in 0..n { v[i] = if i % 2 == 0 { 1 } else { 0 }; }
        }
        3 => {
            // alternating 0,1,0,1
            for i in 0..n { v[i] = if i % 2 == 0 { 0 } else { 1 }; }
        }
        4 => {
            // random uniform
            for i in 0..n { v[i] = rng.gen_bit(); }
        }
        5 => {
            // mostly ones
            for i in 0..n { v[i] = if rng.gen_range(0, 9) == 0 { 0 } else { 1 }; }
        }
        6 => {
            // mostly zeros
            for i in 0..n { v[i] = if rng.gen_range(0, 9) == 0 { 1 } else { 0 }; }
        }
        7 => {
            // ones then zeros
            let mid = n / 2;
            for i in 0..n { v[i] = if i < mid { 1 } else { 0 }; }
        }
        8 => {
            // zeros then ones
            let mid = n / 2;
            for i in 0..n { v[i] = if i < mid { 0 } else { 1 }; }
        }
        9 => {
            // single zero somewhere
            for i in 0..n { v[i] = 1; }
            let p = rng.gen_range(0, n - 1);
            v[p] = 0;
        }
        _ => {
            // single one somewhere
            for i in 0..n { v[i] = 0; }
            let p = rng.gen_range(0, n - 1);
            v[p] = 1;
        }
    }
    v
}

fn print_json(possible: &[i32]) {
    print!("{{\"possible\":[");
    for i in 0..possible.len() {
        if i > 0 { print!(","); }
        print!("{}", possible[i]);
    }
    println!("]}}");
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
        let n = match t % 13 {
            0 => 2,
            1 => 3,
            2 => 4,
            3 => 5,
            4 => 10,
            5 => 50,
            6 => 100,
            7 => 500,
            8 => 1000,
            9 => 5000,
            10 => 10000,
            11 => 50000,
            _ => 100000,
        };
        let bits = make_bits_mode(&mut rng, mode, n);
        let possible = generate_test_case(&bits);
        print_json(&possible);
    }
}