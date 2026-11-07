use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    a_val: i32,
    digits: &Vec<i32>,
) -> (result: (i32, Vec<i32>))
    requires
        1 <= a_val <= i32::MAX,
        1 <= digits.len() <= 2000,
        forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
        digits[0] > 0,
    ensures
        result.0 == a_val,
        1 <= result.0 <= i32::MAX,
        1 <= result.1.len() <= 2000,
        forall|j: int| 0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j] <= 9,
        result.1[0] > 0,
        result.1.len() == digits.len(),
        forall|j: int| 0 <= j < result.1.len() ==> result.1[j] == digits[j],
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < digits.len()
        invariant
            0 <= i <= digits.len(),
            out.len() == i,
            forall|k: int| 0 <= k < i as int ==> out[k] == digits[k],
            forall|j: int| 0 <= j < digits.len() ==> 0 <= #[trigger] digits[j] <= 9,
        decreases digits.len() - i,
    {
        out.push(digits[i]);
        i = i + 1;
    }
    assert(out.len() == digits.len());
    assert(out[0] == digits[0]);
    (a_val, out)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_digits(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    // first digit 1..9
    let first = rng.gen_range_usize(1, 9) as i32;
    v.push(first);
    for _ in 1..len {
        let d = rng.gen_range_usize(0, 9) as i32;
        v.push(d);
    }
    v
}

fn pick_a(rng: &mut Rng, mode: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 2,
        2 => i32::MAX,
        3 => 1336,
        4 => 1337, // 1337 mod 1337 = 0
        5 => 1338,
        6 => 7,
        7 => rng.gen_range_i32(1, 100),
        8 => rng.gen_range_i32(1, i32::MAX),
        9 => 10,
        _ => rng.gen_range_i32(1, 1_000_000),
    }
}

fn pick_len(rng: &mut Rng, mode: usize, t: usize) -> usize {
    match mode {
        0 => 1,
        1 => 1,
        2 => 2000,
        3 => 2000,
        4 => 10,
        5 => 100,
        6 => 500,
        7 => rng.gen_range_usize(1, 2000),
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(1, 200),
        _ => 1 + (t % 1999),
    }
}

fn print_json(a: i32, b: &[i32]) {
    print!("{{\"a\":{},\"b\":[", a);
    for i in 0..b.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", b[i]);
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
        let a = pick_a(&mut rng, mode);
        let len = pick_len(&mut rng, mode, t);
        let digits = make_digits(&mut rng, len);
        let (ra, rd) = generate_test_case(a, &digits);
        print_json(ra, rd.as_slice());
    }
}