use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals: &Vec<i32>,
    d_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= vals.len() <= 1000,
        1 <= d_val,
        d_val as int <= vals.len() as int,
        forall|i: int| 0 <= i < vals.len() ==> 1 <= (#[trigger] vals[i]) <= 100_000,
    ensures
        1 <= result.0.len() <= 1000,
        1 <= result.1,
        result.1 as int <= result.0.len() as int,
        forall|i: int| 0 <= i < result.0.len() ==> 1 <= (#[trigger] result.0[i]) <= 100_000,
{
    let mut arr: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            arr.len() == i,
            forall|k: int| 0 <= k < i as int ==> 1 <= (#[trigger] arr[k]) <= 100_000,
            forall|k: int| 0 <= k < vals.len() ==> 1 <= (#[trigger] vals[k]) <= 100_000,
        decreases n - i,
    {
        arr.push(vals[i]);
        i = i + 1;
    }
    (arr, d_val)
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

fn build(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => rng.gen_range_usize(1, 10),
        3 => rng.gen_range_usize(50, 200),
        4 => 1000,
        5 => rng.gen_range_usize(1, 1000),
        6 => rng.gen_range_usize(1, 1000),
        7 => rng.gen_range_usize(1, 1000),
        8 => rng.gen_range_usize(2, 100),
        9 => rng.gen_range_usize(1, 500),
        _ => rng.gen_range_usize(1, 1000),
    };

    let mut vals: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 | 1 => {
            for _ in 0..n {
                vals.push(rng.gen_range_i32(1, 100_000));
            }
        }
        2 => {
            let v = rng.gen_range_i32(1, 100_000);
            for _ in 0..n {
                vals.push(v);
            }
        }
        3 => {
            for i in 0..n {
                vals.push(((n - i) as i32).max(1));
            }
        }
        4 => {
            for i in 0..n {
                vals.push(((i + 1) as i32).min(100_000));
            }
        }
        5 => {
            for i in 0..n {
                if i % 2 == 0 {
                    vals.push(1);
                } else {
                    vals.push(100_000);
                }
            }
        }
        6 => {
            for _ in 0..n {
                vals.push(rng.gen_range_i32(1, 3));
            }
        }
        7 => {
            for _ in 0..n {
                vals.push(rng.gen_range_i32(1, 100_000));
            }
        }
        8 => {
            // Mountain
            let mid = n / 2;
            for i in 0..n {
                let v = if i <= mid { (i + 1) as i32 } else { (n - i) as i32 };
                vals.push(v.max(1).min(100_000));
            }
        }
        9 => {
            // Valley
            let mid = n / 2;
            for i in 0..n {
                let v = if i <= mid { (mid - i + 1) as i32 } else { (i - mid + 1) as i32 };
                vals.push(v.max(1).min(100_000));
            }
        }
        _ => {
            let _ = t;
            for _ in 0..n {
                vals.push(rng.gen_range_i32(1, 100));
            }
        }
    }

    let n_actual = vals.len();
    let d = match mode {
        0 => 1,
        1 => rng.gen_range_usize(1, n_actual),
        4 => n_actual,
        _ => rng.gen_range_usize(1, n_actual),
    };
    let d_i32 = d as i32;

    generate_test_case(&vals, d_i32)
}

fn print_json(arr: &[i32], d: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"d\":{}}}", d);
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
        let (arr, d) = build(&mut rng, mode, t);
        print_json(&arr, d);
    }
}