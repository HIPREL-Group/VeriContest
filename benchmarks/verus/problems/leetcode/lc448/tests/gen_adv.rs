use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= n <= 100_000,
        values.len() == n,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= n,
    ensures
        nums.len() == n,
        nums.len() >= 1,
        nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= nums.len(),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            nums.len() == i,
            values.len() == n,
            1 <= n <= 100_000,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= n,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= n,
        decreases n - i,
    {
        nums.push(values[i]);
        i = i + 1;
    }
    nums
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
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all 1s
            for _ in 0..n { v.push(1); }
        }
        1 => {
            // all n
            for _ in 0..n { v.push(n as i32); }
        }
        2 => {
            // identity: 1..n (no missing)
            for i in 0..n { v.push((i + 1) as i32); }
        }
        3 => {
            // reverse: n..1
            for i in 0..n { v.push((n - i) as i32); }
        }
        4 => {
            // all same random value
            let x = rng.gen_range_usize(1, n) as i32;
            for _ in 0..n { v.push(x); }
        }
        5 => {
            // half identity, half duplicates of 1
            for i in 0..n {
                if i < n / 2 { v.push((i + 1) as i32); } else { v.push(1); }
            }
        }
        6 => {
            // first half duplicated
            for i in 0..n {
                let idx = if i < n / 2 { i } else { i - n / 2 };
                v.push(((idx % n) + 1) as i32);
            }
        }
        7 => {
            // random values
            for _ in 0..n {
                v.push(rng.gen_range_usize(1, n) as i32);
            }
        }
        8 => {
            // missing only the last: 1..n-1, then 1
            for i in 0..n {
                if i < n - 1 { v.push((i + 1) as i32); } else { v.push(1); }
            }
        }
        9 => {
            // missing only the first: 2..n, then n
            for i in 0..n {
                if i < n - 1 { v.push((i + 2) as i32); } else { v.push(n as i32); }
            }
        }
        _ => {
            // shuffled-ish: values = (i*7 + 3) mod n + 1
            for i in 0..n {
                let x = ((i.wrapping_mul(7)).wrapping_add(3)) % n + 1;
                v.push(x as i32);
            }
        }
    }
    // ensure length exactly n
    while v.len() < n { v.push(1); }
    while v.len() > n { v.pop(); }
    // clamp to [1, n]
    for i in 0..v.len() {
        if v[i] < 1 { v[i] = 1; }
        if v[i] > n as i32 { v[i] = n as i32; }
    }
    v
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
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
            0 => 1,
            1 => 2,
            2 => 100_000,
            3 => 100,
            4 => 1 + (t % 50),
            5 => 50,
            6 => 500,
            7 => 1000 + (t % 100),
            8 => 10_000,
            9 => 8,
            _ => 1 + rng.gen_range_usize(1, 2000),
        };
        let n = if n < 1 { 1 } else if n > 100_000 { 100_000 } else { n };
        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(n, &values);
        print_json(&nums);
    }
}