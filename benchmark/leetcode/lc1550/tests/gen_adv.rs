use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= vals.len() <= 1000,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 1000,
    ensures
        1 <= arr.len() <= 1000,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
{
    let n = vals.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            arr.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> 1 <= #[trigger] vals[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] arr[k] <= 1000,
        decreases n - i,
    {
        arr.push(vals[i]);
        i = i + 1;
    }
    arr
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_vec(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // All evens
            for _ in 0..n { v.push(rng.gen_range(1, 500) * 2); if *v.last().unwrap() > 1000 { *v.last_mut().unwrap() = 1000; } }
        }
        1 => {
            // All odds
            for _ in 0..n { let x = rng.gen_range(1, 499) * 2 + 1; v.push(if x > 999 { 999 } else { x }); }
        }
        2 => {
            // Exactly 3 consecutive odds at start
            if n >= 3 {
                v.push(1); v.push(3); v.push(5);
                for _ in 3..n { v.push(rng.gen_range(1, 500) * 2); }
            } else {
                for _ in 0..n { v.push(rng.gen_range(1, 1000)); }
            }
        }
        3 => {
            // Exactly 3 consecutive odds at end
            for _ in 0..n.saturating_sub(3) { v.push(rng.gen_range(1, 500) * 2); }
            while v.len() < n { v.push(rng.gen_range(0, 499) * 2 + 1); }
        }
        4 => {
            // 2 consecutive odds scattered (no 3 in a row)
            for i in 0..n {
                if i % 3 == 2 { v.push(2); } else { v.push(rng.gen_range(0, 499) * 2 + 1); }
            }
        }
        5 => {
            // Alternating odd/even
            for i in 0..n { if i % 2 == 0 { v.push(1); } else { v.push(2); } }
        }
        6 => {
            // All 1s
            for _ in 0..n { v.push(1); }
        }
        7 => {
            // All 1000s (even)
            for _ in 0..n { v.push(1000); }
        }
        8 => {
            // Random
            for _ in 0..n { v.push(rng.gen_range(1, 1000)); }
        }
        9 => {
            // Triple odds in middle
            let mid = n / 2;
            for i in 0..n {
                if i == mid || i == mid + 1 || i == mid + 2 {
                    v.push(rng.gen_range(0, 499) * 2 + 1);
                } else {
                    v.push(rng.gen_range(1, 500) * 2);
                }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range(1, 1000)); }
        }
    }
    // Ensure length and bounds
    v.truncate(n);
    while v.len() < n { v.push(1); }
    for x in v.iter_mut() {
        if *x < 1 { *x = 1; }
        if *x > 1000 { *x = 1000; }
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_usize(1, 20),
            1 => rng.gen_usize(1, 20),
            2 => rng.gen_usize(3, 50),
            3 => rng.gen_usize(3, 50),
            4 => rng.gen_usize(5, 100),
            5 => rng.gen_usize(1, 100),
            6 => rng.gen_usize(1, 1000),
            7 => rng.gen_usize(1, 1000),
            8 => rng.gen_usize(1, 1000),
            9 => rng.gen_usize(3, 100),
            _ => rng.gen_usize(1, 1000),
        };
        let vals = build_vec(&mut rng, n, mode);
        let arr = generate_test_case(&vals);
        print_json(&arr);
    }
}