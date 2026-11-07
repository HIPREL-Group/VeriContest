use vstd::prelude::*;

verus! {

pub fn bounded_values(values: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1,
{
    let n = if values.len() == 0 { 1usize } else if values.len() > 1000 { 1000usize } else { values.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 1000, 0 <= i <= n, result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 0 <= #[trigger] result[j] <= 1,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 0 };
        result.push(if value < 0 { 0 } else if value > 1 { 1 } else { value });
        i += 1;
    }
    result
}

pub fn generate_test_case(bits: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> result[i] == 0 || result[i] == 1,
        result[result.len() as int - 1] == 0,
{
    let mut result = bounded_values(&bits);
    let last = result.len() - 1;
    result.set(last, 0);
    result
}


pub fn generate_candidate(raw: &Vec<i32>) -> (bits: Vec<i32>)
    requires
        1 <= raw.len() <= 1000,
    ensures
        1 <= bits.len() <= 1000,
        forall|i: int| 0 <= i < bits.len() ==> bits[i] == 0 || bits[i] == 1,
{
    let n = raw.len();
    let mut bits: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == raw.len(),
            1 <= n <= 1000,
            bits.len() == i,
            forall|k: int| 0 <= k < bits.len() ==> bits[k] == 0 || bits[k] == 1,
        decreases n - i,
    {
        let v = raw[i];
        if v == 0 {
            bits.push(0);
        } else if v == 1 {
            bits.push(1);
        } else {
            // normalize to 0 or 1
            let b: i32 = if v % 2 == 0 { 0 } else { 1 };
            if b == 0 {
                bits.push(0);
            } else {
                bits.push(1);
            }
        }
        i = i + 1;
    }
    bits
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn build_raw_ending_zero(raw: Vec<i32>) -> Vec<i32> {
    let mut r = raw;
    if r.is_empty() {
        r.push(0);
    } else {
        let last = r.len() - 1;
        r[last] = 0;
    }
    r
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 1000,
        4 => 999,
        5 => rng.gen_range_usize(1, 20),
        6 => rng.gen_range_usize(1, 100),
        7 => rng.gen_range_usize(500, 1000),
        8 => rng.gen_range_usize(1, 1000),
        9 => rng.gen_range_usize(2, 50),
        _ => rng.gen_range_usize(1, 1000),
    };
    let mut raw: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => { raw.push(0); }
        1 => { raw.push(1); raw.push(0); }
        2 => { raw.push(1); raw.push(1); raw.push(0); }
        3 => {
            // all ones except last
            for _ in 0..(n - 1) { raw.push(1); }
            raw.push(0);
        }
        4 => {
            // all zeros
            for _ in 0..n { raw.push(0); }
        }
        5 => {
            // alternating 1,0
            for i in 0..n {
                raw.push(((i % 2) as i32));
            }
            if n > 0 {
                let last = n - 1;
                raw[last] = 0;
            }
        }
        9 => {
            // pattern 1,1,1,1,...,0 (even count of ones before final 0 tests 2-bit)
            for _ in 0..(n - 1) { raw.push(1); }
            raw.push(0);
        }
        _ => {
            for _ in 0..n {
                raw.push(rng.gen_bit());
            }
        }
    }
    build_raw_ending_zero(raw)
}

fn print_json(bits: &[i32]) {
        let bits = generate_test_case(bits.to_vec());
    print!("{{\"bits\":[");
    for i in 0..bits.len() {
        if i > 0 { print!(","); }
        print!("{}", bits[i]);
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
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let raw = gen_mode(&mut rng, mode);
        let bits = generate_candidate(&raw);
        print_json(&bits);
    }
}
