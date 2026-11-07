use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (mountain: Vec<i32>)
    requires
        3 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        mountain.len() == values.len(),
        mountain.len() <= 2147483647usize,
        forall |i: int| 0 <= i < mountain.len() ==> 1 <= #[trigger] mountain[i] <= 100,
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n = values.len();
    while i < n
        invariant
            n == values.len(),
            3 <= n <= 100,
            i <= n,
            result.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < result.len() ==> result[k] == values[k],
            forall |k: int| 0 <= k < result.len() ==> 1 <= #[trigger] result[k] <= 100,
        decreases n - i,
    {
        result.push(values[i]);
        i = i + 1;
    }
    result
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

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all same
            let x = rng.gen_range_i32(1, 100);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // strictly increasing
            for i in 0..n { v.push(((i % 100) + 1) as i32); }
        }
        2 => {
            // strictly decreasing
            for i in 0..n { v.push((100 - (i % 100)) as i32); }
        }
        3 => {
            // single peak in middle
            for i in 0..n {
                let mid = n / 2;
                let val = if i <= mid { (i + 1) as i32 } else { (n - i) as i32 };
                let clamped = if val < 1 { 1 } else if val > 100 { 100 } else { val };
                v.push(clamped);
            }
        }
        4 => {
            // plateau peak: e.g., 1,5,5,1
            for i in 0..n {
                if i == 0 || i == n - 1 {
                    v.push(1);
                } else {
                    v.push(5);
                }
            }
        }
        5 => {
            // alternating high-low
            for i in 0..n {
                if i % 2 == 0 { v.push(1); } else { v.push(100); }
            }
        }
        6 => {
            // alternating low-high
            for i in 0..n {
                if i % 2 == 0 { v.push(100); } else { v.push(1); }
            }
        }
        7 => {
            // random with small range
            for _ in 0..n { v.push(rng.gen_range_i32(1, 3)); }
        }
        8 => {
            // random full range
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
        }
        9 => {
            // two peaks
            for i in 0..n {
                let q = n / 4;
                let tq = 3 * n / 4;
                if i == q || i == tq {
                    v.push(100);
                } else {
                    v.push(rng.gen_range_i32(1, 50));
                }
            }
        }
        _ => {
            // boundary-peak-looking (first/last high)
            for i in 0..n {
                if i == 0 || i == n - 1 {
                    v.push(100);
                } else {
                    v.push(rng.gen_range_i32(1, 50));
                }
            }
        }
    }
    // ensure values in [1,100]
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 100 { *x = 100; }
    }
    v
}

fn print_json(mountain: &[i32]) {
    print!("{{\"mountain\":[");
    for i in 0..mountain.len() {
        if i > 0 { print!(","); }
        print!("{}", mountain[i]);
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
        let n = match mode {
            0 => 3 + (t % 5),
            1 => 100,
            2 => 100,
            3 => 3 + (t % 20),
            4 => 4 + (t % 10),
            5 => 3 + (t % 15),
            6 => 3 + (t % 15),
            7 => 3 + (t % 97),
            8 => rng.gen_range_usize(3, 100),
            9 => 10 + (t % 50),
            _ => 3 + (t % 97),
        };
        let n = if n < 3 { 3 } else if n > 100 { 100 } else { n };
        let values = build_values(&mut rng, mode, n);
        let mountain = generate_test_case(&values);
        print_json(&mountain);
    }
}