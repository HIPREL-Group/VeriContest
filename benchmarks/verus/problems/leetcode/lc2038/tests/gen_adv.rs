use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, bits: &Vec<u8>) -> (result: Vec<char>)
    requires
        1 <= n <= 100_000,
        bits.len() == n,
        forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0u8 || bits[i] == 1u8,
    ensures
        1 <= result.len() <= 100_000,
        result.len() == n,
        forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i]) == 'A' || result[i] == 'B',
{
    let mut v: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == bits.len(),
            v.len() == i,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] v[k]) == 'A' || v[k] == 'B',
        decreases n - i,
    {
        let c: char = if bits[i] == 0u8 { 'A' } else { 'B' };
        v.push(c);
        i = i + 1;
    }
    v
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bool(&mut self, p_num: u32, p_den: u32) -> bool {
        (self.next_u64() as u32 % p_den) < p_num
    }
}

fn vec_to_string(cs: &Vec<char>) -> String {
    let mut s = String::new();
    for &c in cs.iter() {
        s.push(c);
    }
    s
}

fn escape_json_string(s: &str) -> String {
    let mut out = String::new();
    out.push('"');
    for c in s.chars() {
        out.push(c);
    }
    out.push('"');
    out
}

fn print_case(cs: &Vec<char>) {
    let s = vec_to_string(cs);
    println!("{{\"colors\":{}}}", escape_json_string(&s));
}

fn gen_bits_random(rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(if rng.gen_bool(1, 2) { 1u8 } else { 0u8 });
    }
    v
}

fn gen_bits_all_a(n: usize) -> Vec<u8> {
    vec![0u8; n]
}

fn gen_bits_all_b(n: usize) -> Vec<u8> {
    vec![1u8; n]
}

fn gen_bits_alternating(n: usize, start: u8) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    let mut cur = start;
    for _ in 0..n {
        v.push(cur);
        cur = 1 - cur;
    }
    v
}

fn gen_bits_blocks(rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    let mut cur: u8 = if rng.gen_bool(1, 2) { 0 } else { 1 };
    while v.len() < n {
        let block = rng.gen_range(1, 8);
        for _ in 0..block {
            if v.len() >= n { break; }
            v.push(cur);
        }
        cur = 1 - cur;
    }
    v
}

fn gen_bits_biased(rng: &mut Rng, n: usize, p_a_num: u32, p_a_den: u32) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(if rng.gen_bool(p_a_num, p_a_den) { 0u8 } else { 1u8 });
    }
    v
}

fn gen_bits_triples_a(n: usize) -> Vec<u8> {
    // many AAA patterns
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 4 == 3 { 1u8 } else { 0u8 });
    }
    v
}

fn gen_bits_triples_b(n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 4 == 3 { 0u8 } else { 1u8 });
    }
    v
}

fn gen_bits_long_runs(rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    let mut cur: u8 = if rng.gen_bool(1, 2) { 0 } else { 1 };
    while v.len() < n {
        let block = rng.gen_range(20, 200);
        for _ in 0..block {
            if v.len() >= n { break; }
            v.push(cur);
        }
        cur = 1 - cur;
    }
    v
}

fn gen_for_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<u8> {
    match mode {
        0 => gen_bits_random(rng, n),
        1 => gen_bits_all_a(n),
        2 => gen_bits_all_b(n),
        3 => gen_bits_alternating(n, 0),
        4 => gen_bits_alternating(n, 1),
        5 => gen_bits_blocks(rng, n),
        6 => gen_bits_biased(rng, n, 3, 4),
        7 => gen_bits_biased(rng, n, 1, 4),
        8 => gen_bits_triples_a(n),
        9 => gen_bits_triples_b(n),
        _ => gen_bits_long_runs(rng, n),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range(4, 20),
            4 => rng.gen_range(20, 200),
            5 => rng.gen_range(200, 2000),
            _ => {
                if t % 33 == 0 { 100_000 } else { rng.gen_range(2000, 20_000) }
            }
        };
        let bits = gen_for_mode(&mut rng, mode, n);
        let cs = generate_test_case(n, &bits);
        print_case(&cs);
    }
}