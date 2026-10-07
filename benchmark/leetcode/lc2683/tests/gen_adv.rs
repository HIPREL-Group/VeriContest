use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, bits: &Vec<i32>) -> (result: (Vec<i32>, usize))
    requires
        1 <= n <= 100_000,
        bits.len() == n,
        forall |i: int| 0 <= i < bits.len() ==> (bits[i] == 0 || bits[i] == 1),
    ensures
        1 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> (result.0[i] == 0 || result.0[i] == 1),
        result.1 == 0,
{
    let mut derived: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == bits.len(),
            1 <= n <= 100_000,
            derived.len() == i,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] derived[k] == 0 || derived[k] == 1),
            forall |k: int| 0 <= k < bits.len() ==> (bits[k] == 0 || bits[k] == 1),
        decreases n - i,
    {
        derived.push(bits[i]);
        i = i + 1;
    }
    (derived, 0usize)
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn make_bits_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_bit());
    }
    v
}

fn make_bits_all_zero(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(0); }
    v
}

fn make_bits_all_one(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(1); }
    v
}

fn make_bits_alternating(n: usize, start: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur = start;
    for _ in 0..n {
        v.push(cur);
        cur = 1 - cur;
    }
    v
}

fn make_bits_single_one(n: usize, pos: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i == pos { 1 } else { 0 });
    }
    v
}

fn make_bits_valid_xor(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Generate random original, then compute derived which is guaranteed valid
    let mut orig: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n { orig.push(rng.gen_bit()); }
    let mut d: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let nxt = if i == n - 1 { orig[0] } else { orig[i + 1] };
        d.push(orig[i] ^ nxt);
    }
    d
}

fn make_bits_odd_ones(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Force odd number of 1s (invalid)
    let mut v = make_bits_random(rng, n);
    let mut sum = 0i32;
    for &x in &v { sum += x; }
    if sum % 2 == 0 {
        // flip one
        if v[0] == 0 { v[0] = 1; } else { v[0] = 0; }
    }
    v
}

fn make_bits_even_ones(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = make_bits_random(rng, n);
    let mut sum = 0i32;
    for &x in &v { sum += x; }
    if sum % 2 != 0 {
        if v[0] == 0 { v[0] = 1; } else { v[0] = 0; }
    }
    v
}

fn print_json(derived: &[i32], idx: usize) {
    print!("{{\"derived\":[");
    for i in 0..derived.len() {
        if i > 0 { print!(","); }
        print!("{}", derived[i]);
    }
    println!("],\"idx\":{}}}", idx);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(1, 20),
            4 => 100_000,
            5 => rng.gen_range_usize(100, 1000),
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(10_000, 100_000),
            8 => rng.gen_range_usize(2, 50),
            9 => rng.gen_range_usize(500, 5000),
            _ => rng.gen_range_usize(1, 200),
        };

        let bits = match mode {
            0 => make_bits_random(&mut rng, n),
            1 => make_bits_all_zero(n),
            2 => make_bits_all_one(n),
            3 => make_bits_alternating(n, 0),
            4 => make_bits_valid_xor(&mut rng, n),
            5 => make_bits_odd_ones(&mut rng, n),
            6 => make_bits_even_ones(&mut rng, n),
            7 => {
                let pos = rng.gen_range_usize(0, n - 1);
                make_bits_single_one(n, pos)
            }
            8 => make_bits_alternating(n, 1),
            9 => make_bits_valid_xor(&mut rng, n),
            _ => make_bits_random(&mut rng, n),
        };

        let (derived, idx) = generate_test_case(n, &bits);
        print_json(&derived, idx);
    }
}