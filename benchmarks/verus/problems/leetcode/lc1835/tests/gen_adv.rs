use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    arr1: Vec<i32>,
    arr2: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= arr1.len() <= 100_000,
        1 <= arr2.len() <= 100_000,
        forall |i: int| 0 <= i < arr1.len() ==> 0 <= #[trigger] arr1[i] <= 1_000_000_000,
        forall |j: int| 0 <= j < arr2.len() ==> 0 <= #[trigger] arr2[j] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall |j: int| 0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j] <= 1_000_000_000,
{
    (arr1, arr2)
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

    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_i32_nonneg(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        let v = (self.next_u64() % span) as i32;
        lo + v
    }
}

fn make_arr(rng: &mut Rng, len: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        let x = match mode {
            0 => rng.gen_i32_nonneg(0, 1_000_000_000),
            1 => 0,
            2 => 1_000_000_000,
            3 => rng.gen_i32_nonneg(0, 1),
            4 => rng.gen_i32_nonneg(0, 10),
            5 => {
                let b = rng.gen_usize(0, 30);
                1i32 << b
            }
            6 => (1i32 << 30) - 1,
            7 => {
                let r = rng.gen_usize(0, 3);
                match r {
                    0 => 0,
                    1 => 1,
                    2 => 1_000_000_000,
                    _ => (1i32 << 30) - 1,
                }
            }
            8 => rng.gen_i32_nonneg(0, 255),
            9 => {
                let a = rng.gen_i32_nonneg(0, 1_000_000_000);
                let b = rng.gen_i32_nonneg(0, 1_000_000_000);
                a & b
            }
            _ => rng.gen_i32_nonneg(0, 1_000_000_000),
        };
        v.push(x);
    }
    v
}

fn print_json(arr1: &[i32], arr2: &[i32]) {
    print!("{{\"arr1\":[");
    for i in 0..arr1.len() {
        if i > 0 { print!(","); }
        print!("{}", arr1[i]);
    }
    print!("],\"arr2\":[");
    for j in 0..arr2.len() {
        if j > 0 { print!(","); }
        print!("{}", arr2[j]);
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

    for t in 0..total {
        let mode1 = t % 10;
        let mode2 = (t / 10) % 10;

        let (n1, n2) = match t % 12 {
            0 => (1, 1),
            1 => (1, 100),
            2 => (100, 1),
            3 => (2, 2),
            4 => (10, 10),
            5 => (100, 100),
            6 => (500, 500),
            7 => (1000, 1000),
            8 => (1, 100_000),
            9 => (100_000, 1),
            10 => (100_000, 100_000),
            _ => {
                let a = rng.gen_usize(1, 200);
                let b = rng.gen_usize(1, 200);
                (a, b)
            }
        };

        let arr1 = make_arr(&mut rng, n1, mode1);
        let arr2 = make_arr(&mut rng, n2, mode2);

        let (a1, a2) = generate_test_case(arr1, arr2);
        print_json(&a1, &a2);
    }
}