use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= vals.len() <= 10_000,
        forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000,
    ensures
        1 <= arr.len() <= 10_000,
        forall |k: int| 0 <= k < arr.len() ==> 0 <= #[trigger] arr[k] <= 10_000,
{
    let n = vals.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            0 <= i <= n,
            arr.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] arr[k] == vals[k],
            forall |k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10_000,
        decreases n - i,
    {
        arr.push(vals[i]);
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
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn clamp_vec(v: Vec<i32>) -> Vec<i32> {
    v.into_iter().map(|x| if x < 0 { 0 } else if x > 10_000 { 10_000 } else { x }).collect()
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Random small
            let n = rng.gen_range_usize(1, 20);
            (0..n).map(|_| rng.gen_range_i32(0, 10)).collect()
        }
        1 => {
            // Strictly increasing
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|i| (i as i32).min(10_000)).collect()
        }
        2 => {
            // Strictly decreasing
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|i| (n as i32 - 1 - i as i32).max(0)).collect()
        }
        3 => {
            // All equal
            let n = rng.gen_range_usize(1, 100);
            let v = rng.gen_range_i32(0, 10_000);
            vec![v; n]
        }
        4 => {
            // Single mountain
            let n = rng.gen_range_usize(3, 50);
            let peak = rng.gen_range_usize(1, n - 2);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i <= peak {
                    v.push(i as i32);
                } else {
                    v.push((peak as i32) - (i as i32 - peak as i32));
                }
            }
            clamp_vec(v)
        }
        5 => {
            // Plateau peak (not a valid mountain)
            let n = rng.gen_range_usize(5, 30);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i < n/3 {
                    v.push(i as i32);
                } else if i < 2*n/3 {
                    v.push((n/3) as i32);
                } else {
                    v.push(((n as i32) - (i as i32)).max(0));
                }
            }
            clamp_vec(v)
        }
        6 => {
            // Multiple mountains
            let n = rng.gen_range_usize(5, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let m = i % 6;
                let val = if m <= 3 { m as i32 } else { (6 - m) as i32 };
                v.push(val);
            }
            v
        }
        7 => {
            // Large n
            let n = 10_000;
            (0..n).map(|i| ((i * 7919) % 10_001) as i32).collect()
        }
        8 => {
            // Size 1 or 2
            let n = rng.gen_range_usize(1, 2);
            (0..n).map(|_| rng.gen_range_i32(0, 10_000)).collect()
        }
        9 => {
            // Values only 0/1
            let n = rng.gen_range_usize(1, 50);
            (0..n).map(|_| rng.gen_range_i32(0, 1)).collect()
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            (0..n).map(|_| rng.gen_range_i32(0, 10_000)).collect()
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
    let modes = 10usize;
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let vals = gen_mode(&mut rng, mode);
        if vals.is_empty() || vals.len() > 10_000 {
            continue;
        }
        let mut ok = true;
        for &v in &vals {
            if v < 0 || v > 10_000 { ok = false; break; }
        }
        if !ok { continue; }
        let arr = generate_test_case(&vals);
        print_json(&arr);
    }
}