use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 3,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 3,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 100,
            i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 3,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 3,
        decreases n - i,
    {
        let v = values[i];
        assert(1 <= v <= 3);
        nums.push(v);
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
    fn gen_val(&mut self) -> i32 {
        (self.gen_range_usize(1, 3)) as i32
    }
}

fn make_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n { v.push(rng.gen_val()); }
        }
        1 => {
            for _ in 0..n { v.push(1); }
        }
        2 => {
            for _ in 0..n { v.push(2); }
        }
        3 => {
            for _ in 0..n { v.push(3); }
        }
        4 => {
            // already sorted
            let a = rng.gen_range_usize(0, n);
            let b = rng.gen_range_usize(0, n - a.min(n));
            let c = n - a - b.min(n - a);
            let bb = if a + b > n { n - a } else { b };
            let cc = n - a - bb;
            for _ in 0..a { v.push(1); }
            for _ in 0..bb { v.push(2); }
            for _ in 0..cc { v.push(3); }
        }
        5 => {
            // reverse sorted
            for _ in 0..n { v.push(3); }
            // then change some to 2s and 1s at start
            for i in 0..n/3 { v[i] = 1; }
            for i in n/3..2*n/3 { v[i] = 2; }
            v.reverse();
        }
        6 => {
            // alternating
            for i in 0..n {
                v.push(((i % 3) + 1) as i32);
            }
        }
        7 => {
            // two values only
            let a = (rng.gen_range_usize(1, 3)) as i32;
            let mut b = (rng.gen_range_usize(1, 3)) as i32;
            if b == a { b = if a == 3 { 1 } else { a + 1 }; }
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(a); } else { v.push(b); }
            }
        }
        8 => {
            // mostly sorted with few swaps
            let third = n / 3;
            for i in 0..n {
                if i < third { v.push(1); }
                else if i < 2*third { v.push(2); }
                else { v.push(3); }
            }
            // swap a few
            let swaps = rng.gen_range_usize(0, 3);
            for _ in 0..swaps {
                if n >= 2 {
                    let i = rng.gen_range_usize(0, n - 1);
                    let j = rng.gen_range_usize(0, n - 1);
                    v.swap(i, j);
                }
            }
        }
        9 => {
            // single element duplicates with one outlier
            for _ in 0..n { v.push(2); }
            if n > 0 {
                v[0] = 3;
                if n > 1 { v[n - 1] = 1; }
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_val()); }
        }
    }
    while v.len() < n { v.push(1); }
    while v.len() > n { v.pop(); }
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
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => rng.gen_range_usize(1, 100),
            1 => 1,
            2 => 100,
            3 => rng.gen_range_usize(1, 10),
            4 => rng.gen_range_usize(1, 100),
            5 => rng.gen_range_usize(3, 50),
            6 => rng.gen_range_usize(1, 100),
            7 => rng.gen_range_usize(2, 100),
            8 => rng.gen_range_usize(3, 100),
            9 => rng.gen_range_usize(1, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let n = if n < 1 { 1 } else if n > 100 { 100 } else { n };
        let values = make_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}