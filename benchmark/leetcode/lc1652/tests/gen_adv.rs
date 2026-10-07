use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    vals: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100,
        vals.len() == n,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100,
        -(n as int - 1) <= k as int <= n as int - 1,
    ensures
        1 <= result.0@.len() <= 100,
        forall|i: int| 0 <= i < result.0@.len() ==> 1 <= #[trigger] result.0@[i] <= 100,
        -(result.0@.len() as int - 1) <= result.1 as int <= result.0@.len() as int - 1,
{
    let mut code: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            1 <= n <= 100,
            vals.len() == n,
            code.len() == i,
            forall|j: int| 0 <= j < vals.len() ==> 1 <= #[trigger] vals[j] <= 100,
            forall|j: int| 0 <= j < code.len() ==> 1 <= #[trigger] code[j] <= 100,
        decreases n - i,
    {
        code.push(vals[i]);
        i = i + 1;
    }
    (code, k)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, Vec<i32>) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 100,
        3 => rng.gen_range_usize(1, 10),
        4 => rng.gen_range_usize(50, 100),
        5 => rng.gen_range_usize(1, 100),
        6 => rng.gen_range_usize(3, 20),
        7 => rng.gen_range_usize(1, 100),
        8 => rng.gen_range_usize(2, 100),
        9 => rng.gen_range_usize(2, 100),
        _ => rng.gen_range_usize(1, 100),
    };

    let k: i32 = if n == 1 {
        0
    } else {
        match mode {
            0 => 0,
            1 => if rng.next_u64() % 2 == 0 { 1 } else { -1 },
            2 => (n as i32) - 1,
            3 => -((n as i32) - 1),
            4 => 0,
            5 => rng.gen_range_i32(-((n as i32) - 1), (n as i32) - 1),
            6 => {
                let v = rng.gen_range_i32(1, (n as i32) - 1);
                if t % 2 == 0 { v } else { -v }
            }
            7 => rng.gen_range_i32(-((n as i32) - 1), (n as i32) - 1),
            8 => (n as i32) - 1,
            9 => -((n as i32) - 1),
            _ => rng.gen_range_i32(-((n as i32) - 1), (n as i32) - 1),
        }
    };

    let mut vals: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let v: i32 = match mode {
            0 | 1 => rng.gen_range_i32(1, 100),
            2 => 100,
            3 => 1,
            4 => if i % 2 == 0 { 1 } else { 100 },
            5 => rng.gen_range_i32(1, 100),
            6 => if i == 0 { 100 } else { 1 },
            7 => rng.gen_range_i32(1, 10),
            8 => rng.gen_range_i32(90, 100),
            9 => rng.gen_range_i32(1, 5),
            _ => rng.gen_range_i32(1, 100),
        };
        vals.push(v);
    }

    (n, k, vals)
}

fn print_json(code: &[i32], k: i32) {
    print!("{{\"code\":[");
    for i in 0..code.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", code[i]);
    }
    println!("],\"k\":{}}}", k);
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
        let (n, k, vals) = build_case(&mut rng, mode, t);
        let (code, kk) = generate_test_case(n, k, &vals);
        print_json(&code, kk);
    }
}