use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, usize))
    requires
        2 <= fillers.len() <= 100,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
    ensures
        ({
            let (heights, n) = result;
            &&& 2 <= n <= 100
            &&& heights.len() == n
            &&& (forall|i: int| 0 <= i < heights.len() as int ==> 1 <= #[trigger] heights[i] as int <= 1000)
        }),
{
    let n: usize = fillers.len();
    let mut heights: Vec<i32> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            n == fillers.len(),
            2 <= n <= 100,
            0 <= k <= n,
            heights.len() == k,
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 1000,
            forall|i: int| 0 <= i < heights.len() as int ==> heights[i] == fillers[i],
            forall|i: int| 0 <= i < heights.len() as int ==> 1 <= #[trigger] heights[i] as int <= 1000,
        decreases n - k,
    {
        heights.push(fillers[k]);
        k = k + 1;
    }

    (heights, n)
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
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i32;
        lo + v
    }
}

fn make_fillers_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
        1 => {
            // all equal
            let x = rng.gen_range_i32(1, 1000);
            for _ in 0..n {
                v.push(x);
            }
        }
        2 => {
            // strictly increasing
            let mut start = rng.gen_range_i32(1, 100);
            for _ in 0..n {
                v.push(start);
                if start < 1000 { start += 1; }
            }
        }
        3 => {
            // strictly decreasing
            let mut start = rng.gen_range_i32(100, 1000);
            for _ in 0..n {
                v.push(start);
                if start > 1 { start -= 1; }
            }
        }
        4 => {
            // two close neighbors at wrap around (last and first close)
            for _ in 0..n {
                v.push(rng.gen_range_i32(500, 600));
            }
            // make wrap the minimum
            if n >= 2 {
                v[0] = 500;
                v[n - 1] = 500;
                // make other diffs large
                for i in 1..n-1 {
                    v[i] = if i % 2 == 0 { 1 } else { 1000 };
                }
            }
        }
        5 => {
            // min diff in middle
            for i in 0..n {
                v.push(if i == n/2 || i == n/2 + 1 { 500 } else {
                    if i % 2 == 0 { 1 } else { 1000 }
                });
            }
        }
        6 => {
            // boundary values 1 and 1000
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { 1 } else { 1000 });
            }
        }
        7 => {
            // all min
            for _ in 0..n {
                v.push(1);
            }
        }
        8 => {
            // all max
            for _ in 0..n {
                v.push(1000);
            }
        }
        9 => {
            // alternating
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 1000 });
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
    }
    // ensure bounds
    for i in 0..v.len() {
        if v[i] < 1 { v[i] = 1; }
        if v[i] > 1000 { v[i] = 1000; }
    }
    v
}

fn print_json(heights: &[i32], n: usize) {
    print!("{{\"heights\":[");
    for i in 0..heights.len() {
        if i > 0 { print!(","); }
        print!("{}", heights[i]);
    }
    println!("],\"n\":{}}}", n);
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
            0 => rng.gen_range_usize(2, 100),
            1 => 2 + (t % 99),
            2 => 100,
            3 => 100,
            4 => 2 + (t % 10),
            5 => 5 + (t % 20),
            6 => rng.gen_range_usize(2, 100),
            7 => 2,
            8 => 100,
            9 => 2 + (t % 50),
            _ => rng.gen_range_usize(2, 100),
        };
        let n = if n < 2 { 2 } else if n > 100 { 100 } else { n };
        let fillers = make_fillers_mode(&mut rng, mode, n);
        let (heights, nn) = generate_test_case(&fillers);
        print_json(&heights, nn);
    }
}