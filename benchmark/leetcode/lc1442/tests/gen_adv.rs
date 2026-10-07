use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= values.len() <= 300,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000_000,
    ensures
        1 <= arr.len() <= 300,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000_000,
{
    let n: usize = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == values.len(),
            1 <= n <= 300,
            0 <= pos <= n,
            arr.len() == pos,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000_000,
            forall |i: int| 0 <= i < pos as int ==> #[trigger] arr[i] == values[i],
            forall |i: int| 0 <= i < pos as int ==> 1 <= #[trigger] arr[i] <= 100_000_000,
        decreases n - pos,
    {
        arr.push(values[pos]);
        pos = pos + 1;
    }

    arr
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_values(mode: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::new();
    match mode {
        0 => {
            // minimum size
            v.push(1);
        }
        1 => {
            // size 2
            v.push(1);
            v.push(1);
        }
        2 => {
            // all 1s, varying length
            let n = rng.gen_range_usize(1, 300);
            for _ in 0..n { v.push(1); }
        }
        3 => {
            // small values from {1,2,3}
            let n = rng.gen_range_usize(2, 300);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 3));
            }
        }
        4 => {
            // example 1
            v.push(2); v.push(3); v.push(1); v.push(6); v.push(7);
        }
        5 => {
            // powers of 2
            let n = rng.gen_range_usize(2, 50);
            for _ in 0..n {
                let e = rng.gen_range_usize(0, 26);
                v.push(1i32 << e);
            }
        }
        6 => {
            // xor to zero patterns: pairs
            let n = rng.gen_range_usize(1, 150);
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 1000);
                v.push(x); v.push(x);
            }
            if v.len() > 300 { v.truncate(300); }
            if v.is_empty() { v.push(1); }
        }
        7 => {
            // max size, random
            for _ in 0..300 {
                v.push(rng.gen_range_i32(1, 100_000_000));
            }
        }
        8 => {
            // max values
            let n = rng.gen_range_usize(1, 300);
            for _ in 0..n { v.push(100_000_000); }
        }
        9 => {
            // random mid-sized
            let n = rng.gen_range_usize(3, 100);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 1_000_000));
            }
        }
        _ => {
            let n = rng.gen_range_usize(1, 300);
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100_000_000));
            }
        }
    }
    if v.is_empty() { v.push(1); }
    if v.len() > 300 { v.truncate(300); }
    v
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
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
        let values = build_values(mode, &mut rng);
        let arr = generate_test_case(&values);
        print_json(&arr);
    }
}