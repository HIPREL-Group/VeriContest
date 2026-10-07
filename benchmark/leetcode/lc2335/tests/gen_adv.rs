use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32) -> (result: Vec<i32>)
    requires
        0 <= a <= 100,
        0 <= b <= 100,
        0 <= c <= 100,
    ensures
        result.len() == 3,
        0 <= result[0] <= 100,
        0 <= result[1] <= 100,
        0 <= result[2] <= 100,
{
    let mut v: Vec<i32> = Vec::new();
    v.push(a);
    v.push(b);
    v.push(c);
    v
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn pick_for_mode(rng: &mut Rng, mode: usize) -> (i32, i32, i32) {
    match mode {
        0 => (0, 0, 0),
        1 => (100, 100, 100),
        2 => (rng.gen_range_i32(0, 100), 0, 0),
        3 => (0, rng.gen_range_i32(0, 100), 0),
        4 => (0, 0, rng.gen_range_i32(0, 100)),
        5 => {
            let x = rng.gen_range_i32(0, 100);
            (x, x, x)
        }
        6 => (100, rng.gen_range_i32(0, 100), rng.gen_range_i32(0, 100)),
        7 => (1, 1, 1),
        8 => {
            let a = rng.gen_range_i32(0, 10);
            let b = rng.gen_range_i32(0, 10);
            let c = rng.gen_range_i32(0, 10);
            (a, b, c)
        }
        9 => {
            // one big, two small
            (100, 1, 1)
        }
        _ => (
            rng.gen_range_i32(0, 100),
            rng.gen_range_i32(0, 100),
            rng.gen_range_i32(0, 100),
        ),
    }
}

fn print_json(v: &[i32]) {
    print!("{{\"amount\":[");
    for i in 0..v.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", v[i]);
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
        let (a, b, c) = pick_for_mode(&mut rng, mode);
        let v = generate_test_case(a, b, c);
        print_json(&v);
    }
}