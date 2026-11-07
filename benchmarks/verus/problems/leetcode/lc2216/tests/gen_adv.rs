use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= nums.len() <= 100000,
        nums.len() == values.len(),
        forall|i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == values[i],
{
    let mut nums: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] nums[k] == values[k],
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_values(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all same
            let x = rng.gen_range_i32(0, 100000);
            for _ in 0..n { v.push(x); }
        }
        1 => {
            // strictly alternating (already beautiful ideally)
            for i in 0..n {
                v.push(((i % 2) as i32));
            }
        }
        2 => {
            // pairs of duplicates: a,a,b,b,...
            let mut i = 0;
            while i < n {
                let x = rng.gen_range_i32(0, 100000);
                v.push(x);
                if i + 1 < n { v.push(x); }
                i += 2;
            }
        }
        3 => {
            // random small range
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 3));
            }
        }
        4 => {
            // random full range
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100000));
            }
        }
        5 => {
            // ascending sequence
            for i in 0..n {
                v.push((i as i32) % 100001);
            }
        }
        6 => {
            // descending
            for i in 0..n {
                v.push((100000 - (i as i32 % 100001)).max(0));
            }
        }
        7 => {
            // one duplicate pair at start
            for i in 0..n {
                if i == 0 || i == 1 {
                    v.push(5);
                } else {
                    v.push(i as i32);
                }
            }
        }
        8 => {
            // length 1 edge (always padded to 1)
            v.push(rng.gen_range_i32(0, 100000));
        }
        9 => {
            // two elements equal vs not
            v.push(7);
            if n >= 2 { v.push(if rng.next_u64() % 2 == 0 { 7 } else { 8 }); }
            for _ in 2..n {
                v.push(rng.gen_range_i32(0, 100000));
            }
        }
        _ => {
            // triplets x,x,x pattern
            for i in 0..n {
                v.push(((i / 3) as i32) % 100001);
            }
        }
    }
    // Trim/ensure length exactly n
    while v.len() > n { v.pop(); }
    while v.len() < n { v.push(0); }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 50),
            1 => 2 + (t % 100),
            2 => 4 + (t % 200),
            3 => 10 + (t % 500),
            4 => 100 + (t % 900),
            5 => 1000,
            6 => if t % 3 == 0 { 100000 } else { 5000 },
            7 => 2 + (t % 20),
            8 => 1,
            9 => 2 + (t % 10),
            _ => 50 + (t % 300),
        };
        let n = if n == 0 { 1 } else if n > 100000 { 100000 } else { n };

        let values = build_values(&mut rng, mode, n);
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}