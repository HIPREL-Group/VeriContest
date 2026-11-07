use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 9999,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 100000,
{
    let n = if values.len() == 0 { 1usize }
            else if values.len() > 9999 { 9999usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 9999,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 100000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        let value = if value < 0 { 0 } else if value > 100000 { 100000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}

pub fn generate_test_case(encoded: Vec<i32>, first: i32) -> (result: (Vec<i32>, i32))
    ensures
        1 <= result.0.len() <= 9999,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 100000,
        0 <= result.1 <= 100000,
{
    let encoded = bounded_values(&encoded);
    let first = if first < 0 { 0 } else if first > 100000 { 100000 } else { first };
    (encoded, first)
}


pub fn generate_candidate(encoded: Vec<i32>, first: i32) -> (result: (Vec<i32>, i32))
    requires
        encoded.len() <= 100000,
        forall |i: int| 0 <= i && i < encoded.len() ==> 0 <= encoded[i] && encoded[i] <= 100000,
        0 <= first && first <= 100000,
    ensures
        result.0.len() == encoded.len(),
        result.0.len() <= 100000,
        forall |i: int| 0 <= i && i < result.0.len() ==> 0 <= result.0[i] && result.0[i] <= 100000,
        0 <= result.1 && result.1 <= 100000,
{
    (encoded, first)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_encoded(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let x = match mode {
            0 => rng.gen_range_i32(0, 100000),
            1 => 0,
            2 => 100000,
            3 => if i % 2 == 0 { 0 } else { 100000 },
            4 => rng.gen_range_i32(0, 10),
            5 => rng.gen_range_i32(99990, 100000),
            6 => (i as i32) % 100001,
            7 => rng.gen_range_i32(0, 1000),
            8 => {
                // powers of 2 below 100000
                let bits = [1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048, 4096, 8192, 16384, 32768, 65536];
                bits[(rng.next_u64() as usize) % bits.len()]
            }
            9 => 65535,
            _ => rng.gen_range_i32(0, 100000),
        };
        v.push(x);
    }
    v
}

fn print_json(encoded: &[i32], first: i32) {
    let (encoded, first) = generate_test_case(encoded.to_vec(), first);
    print!("{{\"encoded\":[");
    for i in 0..encoded.len() {
        if i > 0 { print!(","); }
        print!("{}", encoded[i]);
    }
    println!("],\"first\":{}}}", first);
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
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        // encoded.len() = n - 1, so we pick len in [1, 100000]
        let len = match mode {
            0 => 1 + (t % 10),
            1 => 99999, // arr length 100000 -> encoded length 99999
            2 => 1,
            3 => 2,
            4 => 100,
            5 => 99999,
            6 => 1000,
            7 => 5000,
            8 => 50 + (t % 50),
            _ => rng.gen_range_usize(1, 500),
        };
        let first = match mode {
            1 => 0,
            2 => 100000,
            3 => rng.gen_range_i32(0, 100000),
            5 => 50000,
            _ => rng.gen_range_i32(0, 100000),
        };
        let encoded = build_encoded(&mut rng, len, mode);
        let (enc, f) = generate_candidate(encoded, first);
        print_json(&enc, f);
    }
}
