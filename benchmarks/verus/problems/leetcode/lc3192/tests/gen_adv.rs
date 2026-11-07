use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    bits: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len <= 100000,
        bits.len() == len,
        forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] == 0 || bits[i] == 1),
    ensures
        1 <= nums.len() <= 100000,
        forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            0 <= k <= len,
            1 <= len <= 100000,
            bits.len() == len,
            nums.len() == k,
            forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i] == 0 || bits[i] == 1),
            forall |i: int| 0 <= i < nums.len() ==> (#[trigger] nums[i] == 0 || nums[i] == 1),
        decreases len - k,
    {
        let v = bits[k];
        if v == 0 {
            nums.push(0);
        } else {
            nums.push(1);
        }
        k = k + 1;
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
}

fn make_bits(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => { for _ in 0..n { v.push(1); } }
        1 => { for _ in 0..n { v.push(0); } }
        2 => { for i in 0..n { v.push(((i % 2) as i32)); } }
        3 => { for i in 0..n { v.push((((i+1) % 2) as i32)); } }
        4 => {
            for i in 0..n { if i < n/2 { v.push(0); } else { v.push(1); } }
        }
        5 => {
            for i in 0..n { if i < n/2 { v.push(1); } else { v.push(0); } }
        }
        6 => {
            for i in 0..n {
                if i == 0 || i == n-1 { v.push(0); } else { v.push(1); }
            }
        }
        7 => {
            for i in 0..n {
                if i == 0 || i == n-1 { v.push(1); } else { v.push(0); }
            }
        }
        8 => {
            for _ in 0..n {
                v.push((rng.next_u64() & 1) as i32);
            }
        }
        9 => {
            let mut cur: i32 = (rng.next_u64() & 1) as i32;
            for _ in 0..n {
                v.push(cur);
                if rng.next_u64() % 3 == 0 {
                    cur = 1 - cur;
                }
            }
        }
        _ => {
            for _ in 0..n { v.push((rng.next_u64() & 1) as i32); }
        }
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
    } else { 1 };
    let mut rng = Rng::new(seed);

    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 13 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 100000,
            4 => 99999,
            5 => 10,
            6 => 100,
            7 => 1000,
            8 => 10000,
            9 => 50000,
            10 => rng.gen_range_usize(1, 100),
            11 => rng.gen_range_usize(1, 5000),
            _ => rng.gen_range_usize(1, 100000),
        };
        let bits = make_bits(&mut rng, mode, n);
        let nums = generate_test_case(n, &bits);
        print_json(&nums);
    }
}