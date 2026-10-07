use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= values.len() <= 40_000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= arr.len() <= 40_000,
        forall |i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            arr.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] arr[k] == values[k],
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1_000_000_000,
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
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // single element
            vec![rng.gen_i32(0, 1_000_000_000)]
        }
        1 => {
            // all equal
            let n = rng.gen_usize(1, 100);
            let v = rng.gen_i32(0, 1_000_000_000);
            vec![v; n]
        }
        2 => {
            // strictly increasing
            let n = rng.gen_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            let mut cur: i32 = rng.gen_i32(0, 1000);
            for _ in 0..n {
                v.push(cur);
                cur = cur.saturating_add(rng.gen_i32(1, 10));
            }
            v
        }
        3 => {
            // strictly decreasing
            let n = rng.gen_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            let mut cur: i32 = rng.gen_i32(10_000, 100_000);
            for _ in 0..n {
                v.push(cur);
                cur = (cur - rng.gen_i32(1, 10)).max(0);
            }
            v
        }
        4 => {
            // perfectly turbulent alternating
            let n = rng.gen_usize(2, 200);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_i32(0, 100));
                } else {
                    v.push(rng.gen_i32(500, 1000));
                }
            }
            v
        }
        5 => {
            // small values 0/1 only
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32(0, 1));
            }
            v
        }
        6 => {
            // random small
            let n = rng.gen_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32(0, 10));
            }
            v
        }
        7 => {
            // large n
            let n = if t % 2 == 0 { 40_000 } else { 39_999 };
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_i32(0, 1_000_000_000));
                } else {
                    v.push(rng.gen_i32(0, 1_000_000_000));
                }
            }
            v
        }
        8 => {
            // plateau with turbulence mixed
            let n = rng.gen_usize(5, 80);
            let mut v = Vec::with_capacity(n);
            let mut alt = true;
            for i in 0..n {
                if i > 0 && i % 5 == 0 {
                    v.push(v[i-1]); // equal
                } else if alt {
                    v.push(100);
                    alt = false;
                } else {
                    v.push(200);
                    alt = true;
                }
            }
            v
        }
        9 => {
            // extreme values
            let n = rng.gen_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(1_000_000_000);
                }
            }
            v
        }
        _ => {
            let n = rng.gen_usize(1, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_i32(0, 1_000_000_000));
            }
            v
        }
    }
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
        let values = gen_mode(&mut rng, mode, t);
        // safety clamp
        let mut clean: Vec<i32> = Vec::with_capacity(values.len().min(40_000).max(1));
        for i in 0..values.len() {
            if clean.len() >= 40_000 { break; }
            let mut v = values[i];
            if v < 0 { v = 0; }
            if v > 1_000_000_000 { v = 1_000_000_000; }
            clean.push(v);
        }
        if clean.is_empty() {
            clean.push(0);
        }
        let arr = generate_test_case(&clean);
        print_json(&arr);
    }
}