use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k_val: i32,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        n % 2 == 0,
        2 <= n <= 100000,
        1 <= k_val <= 100000,
        fillers.len() == n,
        forall|i: int| 0 <= i < fillers.len() ==> -1000000000 <= #[trigger] fillers[i] <= 1000000000,
    ensures
        result.0@.len() % 2 == 0,
        2 <= result.0@.len() <= 100000,
        1 <= result.1 <= 100000,
        forall|i: int| 0 <= i < result.0@.len() ==> -1000000000 <= #[trigger] result.0@[i] <= 1000000000,
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            arr.len() == i,
            fillers.len() == n,
            forall|j: int| 0 <= j < i as int ==> -1000000000 <= #[trigger] arr[j] <= 1000000000,
            forall|j: int| 0 <= j < fillers.len() ==> -1000000000 <= #[trigger] fillers[j] <= 1000000000,
        decreases n - i,
    {
        arr.push(fillers[i]);
        i = i + 1;
    }
    (arr, k_val)
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn make_fillers(rng: &mut Rng, n: usize, mode: usize, k: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32);
            }
        }
        1 => {
            for _ in 0..n {
                let r = rng.gen_range_i64(0, k as i64 - 1);
                v.push(r as i32);
            }
        }
        2 => {
            for i in 0..n {
                let r = (i as i64) % (k as i64);
                v.push(r as i32);
            }
        }
        3 => {
            for _ in 0..n {
                v.push(0i32);
            }
        }
        4 => {
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i64(-1_000_000_000, -1) as i32);
                } else {
                    v.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
                }
            }
        }
        5 => {
            for _ in 0..n {
                v.push(1_000_000_000i32);
            }
        }
        6 => {
            for _ in 0..n {
                v.push(-1_000_000_000i32);
            }
        }
        7 => {
            // pairs that each sum to multiples of k
            let mut i = 0;
            while i < n {
                let a = rng.gen_range_i64(-1_000_000_000, 1_000_000_000);
                let ar = ((a % k as i64) + k as i64) % k as i64;
                let need = if ar == 0 { 0 } else { k as i64 - ar };
                let mut b = need;
                // adjust b into range
                while b > 1_000_000_000 {
                    b -= k as i64;
                }
                while b < -1_000_000_000 {
                    b += k as i64;
                }
                v.push(a as i32);
                v.push(b as i32);
                i += 2;
            }
            v.truncate(n);
        }
        8 => {
            // small k, all same value
            let x = rng.gen_range_i64(-1000, 1000);
            for _ in 0..n {
                v.push(x as i32);
            }
        }
        9 => {
            // multiples of k
            for _ in 0..n {
                let m = rng.gen_range_i64(-1000, 1000);
                let val = m * (k as i64);
                let clamped = if val > 1_000_000_000 { 1_000_000_000 }
                              else if val < -1_000_000_000 { -1_000_000_000 }
                              else { val };
                v.push(clamped as i32);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i64(-100, 100) as i32);
            }
        }
    }
    while v.len() < n {
        v.push(0);
    }
    v.truncate(n);
    v
}

fn print_json(arr: &[i32], k: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
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
        let n_raw = match mode {
            0 => 2 + (t % 10) * 2,
            1 => 4 + (t % 20) * 2,
            2 => 100,
            3 => 2,
            4 => 50,
            5 => 1000,
            6 => 2,
            7 => 20 + (t % 30) * 2,
            8 => 10,
            9 => 100,
            _ => 500,
        };
        let n = if n_raw % 2 == 0 { n_raw } else { n_raw + 1 };
        let n = if n < 2 { 2 } else if n > 100000 { 100000 } else { n };

        let k = match mode {
            0 => rng.gen_range_i64(1, 100000) as i32,
            1 => rng.gen_range_i64(1, 100) as i32,
            2 => 1i32,
            3 => 100000i32,
            4 => rng.gen_range_i64(1, 1000) as i32,
            5 => 7i32,
            6 => 2i32,
            7 => rng.gen_range_i64(2, 50) as i32,
            8 => 3i32,
            9 => rng.gen_range_i64(1, 100) as i32,
            _ => rng.gen_range_i64(1, 100000) as i32,
        };
        let k = if k < 1 { 1 } else if k > 100000 { 100000 } else { k };

        let fillers = make_fillers(&mut rng, n, mode, k);
        let (arr, kk) = generate_test_case(n, k, &fillers);
        print_json(&arr, kk);
    }
}