use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= arr.len() <= 100_000,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
{
    let n = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            arr.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] arr[k] <= 100,
        decreases n - i,
    {
        let v = values[i];
        assert(1 <= v <= 100);
        arr.push(v);
        i = i + 1;
    }
    arr
}

}

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => { // all 1s
            for _ in 0..n { v.push(1); }
        }
        1 => { // all 2s (even)
            for _ in 0..n { v.push(2); }
        }
        2 => { // all 100s
            for _ in 0..n { v.push(100); }
        }
        3 => { // all 99s (odd)
            for _ in 0..n { v.push(99); }
        }
        4 => { // alternating odd/even
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 2 });
            }
        }
        5 => { // alternating even/odd
            for i in 0..n {
                v.push(if i % 2 == 0 { 2 } else { 1 });
            }
        }
        6 => { // random odd values
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 50);
                v.push(2 * x - 1);
            }
        }
        7 => { // random even values
            for _ in 0..n {
                let x = rng.gen_range_i32(1, 50);
                v.push(2 * x);
            }
        }
        8 => { // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        9 => { // one odd, rest even
            for i in 0..n {
                v.push(if i == n/2 { 1 } else { 2 });
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
    }
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
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 100_000,
            4 => 99_999,
            _ => {
                let r = rng.gen_range_usize(1, 1000);
                if t % 17 == 0 { rng.gen_range_usize(1, 100_000) } else { r }
            }
        };
        let values = make_values(&mut rng, mode, n);
        let arr = generate_test_case(&values);
        print_json(&arr);
    }
}