use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
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
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn clamp_vec(v: Vec<i32>) -> Vec<i32> {
    let mut out = Vec::with_capacity(v.len());
    for &x in &v {
        let y = if x < 1 { 1 } else if x > 100 { 100 } else { x };
        out.push(y);
    }
    out
}

fn make_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => vec![4, 1, 2, 3],
        1 => vec![2, 1],
        2 => vec![rng.gen_range_i32(1, 100)],
        3 => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            v
        }
        4 => {
            let n = 100;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            v
        }
        5 => {
            let n = rng.gen_range_usize(1, 100);
            let x = rng.gen_range_i32(1, 100);
            vec![x; n]
        }
        6 => {
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push(((i % 100) + 1) as i32); }
            v
        }
        7 => {
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n { v.push((100 - (i % 100)) as i32); }
            v
        }
        8 => {
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 100 });
            }
            v
        }
        9 => {
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 100 } else { 1 });
            }
            v
        }
        10 => {
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 5)); }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n { v.push(rng.gen_range_i32(1, 100)); }
            v
        }
    }
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
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let raw = make_case(&mut rng, mode);
        let values = clamp_vec(raw);
        let values = if values.is_empty() { vec![1i32] } else { values };
        let values = if values.len() > 100 { values[..100].to_vec() } else { values };
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}