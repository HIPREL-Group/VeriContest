use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, k: i32, fillers: &Vec<i32>) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 500,
        1 <= k <= 500,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 500,
    ensures
        1 <= result.0.len() <= 500,
        1 <= result.1 <= 500,
        result.0.len() == n,
        result.1 == k,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 500,
{
    let mut a: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            a.len() == idx,
            fillers.len() == n,
            forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 500,
            forall|i: int| 0 <= i < a.len() ==> 0 <= #[trigger] a[i] <= 500,
            forall|i: int| 0 <= i < a.len() ==> a[i] == fillers[i],
        decreases n - idx,
    {
        a.push(fillers[idx]);
        idx = idx + 1;
    }
    (a, k)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let x = match mode {
            0 => rng.gen_range_i32(0, 500),
            1 => 0i32,
            2 => 500i32,
            3 => if i % 2 == 0 { 0 } else { 500 },
            4 => if i % 2 == 0 { 500 } else { 0 },
            5 => rng.gen_range_i32(0, 3),
            6 => rng.gen_range_i32(0, 10),
            7 => {
                if i == 0 || i + 1 == n { 0 } else { rng.gen_range_i32(0, 500) }
            }
            8 => {
                if i == n / 2 { 0 } else { 500 }
            }
            9 => {
                if i == n / 2 { 500 } else { 0 }
            }
            _ => rng.gen_range_i32(0, 500),
        };
        v.push(x);
    }
    v
}

fn print_json(a: &[i32], k: i32) {
    print!("{{\"a\":[");
    for i in 0..a.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", a[i]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            0 => rng.gen_range_usize(1, 500),
            1 => 1,
            2 => 2,
            3 => 500,
            4 => 500,
            5 => rng.gen_range_usize(1, 20),
            6 => rng.gen_range_usize(50, 100),
            7 => rng.gen_range_usize(100, 500),
            8 => rng.gen_range_usize(1, 500),
            9 => rng.gen_range_usize(1, 500),
            _ => rng.gen_range_usize(1, 500),
        };
        let k: i32 = match mode {
            0 => rng.gen_range_i32(1, 500),
            1 => rng.gen_range_i32(1, 500),
            2 => 1,
            3 => 500,
            4 => 500,
            5 => rng.gen_range_i32(1, 5),
            6 => rng.gen_range_i32(1, 500),
            7 => rng.gen_range_i32(1, 500),
            8 => 500,
            9 => rng.gen_range_i32(1, 500),
            _ => rng.gen_range_i32(1, 500),
        };

        let fillers = make_fillers(&mut rng, n, mode);
        let (a, kk) = generate_test_case(n, k, &fillers);
        print_json(&a, kk);
    }
}