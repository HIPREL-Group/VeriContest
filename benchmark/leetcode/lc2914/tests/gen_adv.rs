use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<u8>) -> (s: Vec<char>)
    requires
        2 <= bits.len() <= 100_000,
        bits.len() % 2 == 0,
        forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0u8 || bits[i] == 1u8,
    ensures
        2 <= s.len() <= 100_000,
        s.len() == bits.len(),
        s.len() % 2 == 0,
        forall |i: int| 0 <= i < s.len() ==> (#[trigger] s[i]) == '0' || s[i] == '1',
{
    let n = bits.len();
    let mut s: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bits.len(),
            0 <= i <= n,
            s.len() == i,
            forall |k: int| 0 <= k < bits.len() ==> (#[trigger] bits[k]) == 0u8 || bits[k] == 1u8,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] s[k]) == '0' || s[k] == '1',
        decreases n - i,
    {
        let c: char = if bits[i] == 0u8 { '0' } else { '1' };
        s.push(c);
        i = i + 1;
    }
    s
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_bit(&mut self) -> u8 {
        (self.next_u64() & 1) as u8
    }
}

fn bits_to_string(bits: &Vec<u8>) -> String {
    let chars = generate_test_case(bits);
    let mut s = String::new();
    for c in chars.iter() {
        s.push(*c);
    }
    s
}

fn print_json(s: &str) {
    println!("{{\"s\":\"{}\"}}", s);
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<u8> {
    // pick even length
    let n: usize = match mode {
        0 => 2,
        1 => 4,
        2 => {
            let k = rng.gen_range_usize(1, 50);
            2 * k
        }
        3 => {
            let k = rng.gen_range_usize(1, 500);
            2 * k
        }
        4 => 100_000,
        5 => 99_998,
        6 => {
            // power of two-ish
            let opts = [2usize, 8, 16, 32, 64, 128, 256, 1024, 4096, 16384];
            opts[t % opts.len()]
        }
        7 => {
            let k = rng.gen_range_usize(1, 5000);
            2 * k
        }
        8 => 6,
        9 => {
            let k = rng.gen_range_usize(1, 50_000);
            2 * k
        }
        _ => {
            let k = rng.gen_range_usize(1, 100);
            2 * k
        }
    };

    let mut bits: Vec<u8> = Vec::with_capacity(n);
    match mode {
        0 | 1 => {
            // fully random small
            for _ in 0..n {
                bits.push(rng.gen_bit());
            }
        }
        2 => {
            // alternating 0101...
            for i in 0..n {
                bits.push((i & 1) as u8);
            }
        }
        3 => {
            // all zeros
            for _ in 0..n {
                bits.push(0);
            }
        }
        4 => {
            // all ones
            for _ in 0..n {
                bits.push(1);
            }
        }
        5 => {
            // paired blocks already: 00110011...
            for i in 0..n {
                bits.push(((i / 2) & 1) as u8);
            }
        }
        6 => {
            // random
            for _ in 0..n {
                bits.push(rng.gen_bit());
            }
        }
        7 => {
            // mostly zeros with a few ones
            for _ in 0..n {
                bits.push(0);
            }
            let flips = rng.gen_range_usize(0, (n / 2).max(1));
            for _ in 0..flips {
                let idx = rng.gen_range_usize(0, n - 1);
                bits[idx] = 1;
            }
        }
        8 => {
            // 010101 small
            for i in 0..n {
                bits.push((i & 1) as u8);
            }
        }
        9 => {
            // half zeros then half ones
            for i in 0..n {
                bits.push(if i < n / 2 { 0 } else { 1 });
            }
        }
        _ => {
            // biased random
            for _ in 0..n {
                let v = rng.next_u64() % 4;
                bits.push(if v == 0 { 1 } else { 0 });
            }
        }
    }
    bits
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
        let bits = gen_mode(&mut rng, mode, t);
        let s = bits_to_string(&bits);
        print_json(&s);
    }
}