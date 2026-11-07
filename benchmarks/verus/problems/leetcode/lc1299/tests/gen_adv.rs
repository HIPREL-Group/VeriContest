use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000,
    ensures
        1 <= arr.len() <= 10_000,
        forall|i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000,
{
    let n = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            arr.len() == i,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] arr[k] <= 100_000,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000,
        decreases n - i,
    {
        arr.push(values[i]);
        i = i + 1;
    }
    arr
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

fn build_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 10_000,
        3 => rng.gen_range_usize(1, 20),
        4 => rng.gen_range_usize(100, 500),
        5 => rng.gen_range_usize(1000, 2000),
        6 => rng.gen_range_usize(1, 100),
        7 => rng.gen_range_usize(1, 100),
        8 => rng.gen_range_usize(1, 50),
        9 => rng.gen_range_usize(1, 50),
        _ => rng.gen_range_usize(1, 1000),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            v.push(rng.gen_range_i32(1, 100_000));
        }
        1 => {
            v.push(rng.gen_range_i32(1, 100_000));
            v.push(rng.gen_range_i32(1, 100_000));
        }
        2 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
        }
        3 => {
            let x = rng.gen_range_i32(1, 100_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        4 => {
            // strictly increasing
            let mut cur: i32 = 1;
            let step = ((100_000 - 1) / (n as i32).max(1)).max(1);
            for _ in 0..n {
                v.push(cur);
                cur = (cur + step).min(100_000);
            }
        }
        5 => {
            // strictly decreasing
            let mut cur: i32 = 100_000;
            let step = ((100_000 - 1) / (n as i32).max(1)).max(1);
            for _ in 0..n {
                v.push(cur);
                cur = (cur - step).max(1);
            }
        }
        6 => {
            // max at the end
            for _ in 0..n - 1 {
                v.push(rng.gen_range_i32(1, 99_999));
            }
            v.push(100_000);
        }
        7 => {
            // max at start
            v.push(100_000);
            for _ in 1..n {
                v.push(rng.gen_range_i32(1, 99_999));
            }
        }
        8 => {
            // all 1
            for _ in 0..n {
                v.push(1);
            }
        }
        9 => {
            // all 100_000
            for _ in 0..n {
                v.push(100_000);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000));
            }
        }
    }
    let _ = t;
    v
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr[i]);
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
        let values = build_values(&mut rng, mode, t);
        let arr = generate_test_case(&values);
        print_json(&arr);
    }
}