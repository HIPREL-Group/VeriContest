use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (stones: Vec<i32>)
    requires
        2 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        2 <= stones.len() <= 1000,
        forall |i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 1000,
{
    let mut stones: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            stones.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] stones[k] <= 1000,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000,
        decreases n - i,
    {
        stones.push(values[i]);
        i = i + 1;
    }
    stones
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
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // random small values
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 10));
            }
        }
        1 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        2 => {
            // all ones
            for _ in 0..n {
                v.push(1);
            }
        }
        3 => {
            // all 1000
            for _ in 0..n {
                v.push(1000);
            }
        }
        4 => {
            // increasing
            for i in 0..n {
                let val = ((i % 1000) as i32) + 1;
                v.push(val);
            }
        }
        5 => {
            // decreasing
            for i in 0..n {
                let val = 1000 - ((i % 1000) as i32);
                v.push(val.max(1));
            }
        }
        6 => {
            // alternating big small
            for i in 0..n {
                v.push(if i % 2 == 0 { 1000 } else { 1 });
            }
        }
        7 => {
            // example 1
            let base = [5, 3, 1, 4, 2];
            for i in 0..n {
                v.push(base[i % 5]);
            }
        }
        8 => {
            // example 2
            let base = [7, 90, 5, 1, 100, 10, 10, 2];
            for i in 0..n {
                v.push(base[i % 8]);
            }
        }
        9 => {
            // palindrome-like
            for i in 0..n {
                let d = if i < n - i - 1 { i } else { n - i - 1 };
                v.push(((d % 1000) as i32) + 1);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
    }
    v
}

fn print_json(stones: &[i32]) {
    print!("{{\"stones\":[");
    for i in 0..stones.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", stones[i]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 2 + (t % 20),
            1 => 2 + rng.gen_range_usize(0, 998),
            2 => 1000,
            3 => 1000,
            4 => 500 + (t % 500),
            5 => 3 + (t % 50),
            6 => 2 + (t % 100),
            7 => 5,
            8 => 8,
            9 => 2 + (t % 200),
            _ => 10,
        };
        let n = if n < 2 { 2 } else if n > 1000 { 1000 } else { n };
        let values = build_values(&mut rng, mode, n);
        let stones = generate_test_case(&values);
        print_json(&stones);
    }
}