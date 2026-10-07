use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= values.len() <= 2_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100_000_000,
    ensures
        1 <= arr.len() <= 2_000,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 100_000_000,
{
    let mut arr: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            arr.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] arr[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100_000_000,
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
        Self { state: seed.wrapping_add(1) }
    }
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

fn build_values(mode: usize, n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // random small range
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
        }
        1 => {
            // sorted ascending
            let mut cur = 0i32;
            for _ in 0..n {
                cur = cur.saturating_add(rng.gen_range_i32(0, 3));
                if cur > 100_000_000 { cur = 100_000_000; }
                v.push(cur);
            }
        }
        2 => {
            // sorted descending
            for i in 0..n {
                v.push((n - 1 - i) as i32);
            }
        }
        3 => {
            // all equal
            let x = rng.gen_range_i32(0, 100_000_000);
            for _ in 0..n {
                v.push(x);
            }
        }
        4 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        5 => {
            // maxed values
            for _ in 0..n {
                v.push(100_000_000);
            }
        }
        6 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100_000_000));
            }
        }
        7 => {
            // almost sorted - one swap
            for i in 0..n {
                v.push(i as i32);
            }
            if n >= 2 {
                let i = rng.gen_range_usize(0, n - 1);
                let mut j = rng.gen_range_usize(0, n - 1);
                if j == i { j = (j + 1) % n; }
                v.swap(i, j);
            }
        }
        8 => {
            // duplicated pattern
            for i in 0..n {
                v.push(((i / 2) as i32) % 10);
            }
        }
        9 => {
            // two-valued
            let a = rng.gen_range_i32(0, 100);
            let b = rng.gen_range_i32(0, 100);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(a); } else { v.push(b); }
            }
        }
        _ => {
            // zigzag
            for i in 0..n {
                v.push(if i % 2 == 0 { 0 } else { 100_000_000 });
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 20),
            1 => 2000,
            2 => 50,
            3 => 2000,
            4 => 1,
            5 => 100,
            6 => rng.gen_range_usize(1, 2000),
            7 => rng.gen_range_usize(2, 500),
            8 => 200,
            9 => rng.gen_range_usize(1, 300),
            _ => rng.gen_range_usize(1, 1000),
        };
        let n = if n == 0 { 1 } else if n > 2000 { 2000 } else { n };
        let values = build_values(mode, n, &mut rng);
        // safety clamp
        let mut clamped: Vec<i32> = Vec::with_capacity(values.len());
        for x in &values {
            let mut y = *x;
            if y < 0 { y = 0; }
            if y > 100_000_000 { y = 100_000_000; }
            clamped.push(y);
        }
        let arr = generate_test_case(&clamped);
        print_json(&arr);
    }
}