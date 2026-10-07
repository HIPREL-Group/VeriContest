use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
    a: i32,
    b: i32,
    c: i32,
) -> (result: (Vec<i32>, i32, i32, i32))
    requires
        3 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1000,
        0 <= a <= 1000,
        0 <= b <= 1000,
        0 <= c <= 1000,
    ensures
        3 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        0 <= result.1 <= 1000,
        0 <= result.2 <= 1000,
        0 <= result.3 <= 1000,
{
    let n = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            arr.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] arr[k] <= 1000,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1000,
        decreases n - i,
    {
        arr.push(values[i]);
        i = i + 1;
    }
    (arr, a, b, c)
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32, i32, i32) {
    let n = match mode {
        0 => 3,
        1 => 100,
        2 => rng.gen_usize(3, 10),
        3 => rng.gen_usize(50, 100),
        4 => rng.gen_usize(3, 100),
        5 => rng.gen_usize(3, 100),
        6 => rng.gen_usize(3, 100),
        7 => 3,
        8 => 100,
        9 => rng.gen_usize(3, 100),
        _ => rng.gen_usize(3, 100),
    };

    let mut values: Vec<i32> = Vec::new();
    match mode {
        0 => {
            for _ in 0..n {
                values.push(rng.gen_i32(0, 1000));
            }
        }
        1 => {
            let v = rng.gen_i32(0, 1000);
            for _ in 0..n {
                values.push(v);
            }
        }
        2 => {
            for i in 0..n {
                values.push(if i % 2 == 0 { 0 } else { 1000 });
            }
        }
        3 => {
            for _ in 0..n {
                values.push(rng.gen_i32(0, 5));
            }
        }
        4 => {
            for i in 0..n {
                values.push((i as i32) % 1001);
            }
        }
        5 => {
            for _ in 0..n {
                values.push(0);
            }
        }
        6 => {
            for _ in 0..n {
                values.push(1000);
            }
        }
        7 => {
            values.push(0);
            values.push(500);
            values.push(1000);
        }
        8 => {
            for i in 0..n {
                values.push(((i * 37) % 1001) as i32);
            }
        }
        9 => {
            for _ in 0..n {
                values.push(rng.gen_i32(0, 10));
            }
        }
        _ => {
            for _ in 0..n {
                values.push(rng.gen_i32(0, 1000));
            }
        }
    }

    let (a, b, c) = match mode {
        0 => (rng.gen_i32(0, 1000), rng.gen_i32(0, 1000), rng.gen_i32(0, 1000)),
        1 => (0, 0, 0),
        2 => (1000, 1000, 1000),
        3 => (rng.gen_i32(0, 10), rng.gen_i32(0, 10), rng.gen_i32(0, 10)),
        4 => (rng.gen_i32(0, 1000), rng.gen_i32(0, 1000), rng.gen_i32(0, 1000)),
        5 => (0, 0, 0),
        6 => (0, 0, 0),
        7 => (1000, 1000, 1000),
        8 => (rng.gen_i32(0, 100), rng.gen_i32(0, 100), rng.gen_i32(0, 100)),
        9 => (rng.gen_i32(0, 5), rng.gen_i32(0, 5), rng.gen_i32(0, 5)),
        _ => (rng.gen_i32(0, 1000), rng.gen_i32(0, 1000), rng.gen_i32(0, 1000)),
    };

    (values, a, b, c)
}

fn print_json(arr: &[i32], a: i32, b: i32, c: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr[i]);
    }
    println!("],\"a\":{},\"b\":{},\"c\":{}}}", a, b, c);
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
        let (values, a, b, c) = build_case(&mut rng, mode);
        let (arr, aa, bb, cc) = generate_test_case(&values, a, b, c);
        print_json(&arr, aa, bb, cc);
    }
}