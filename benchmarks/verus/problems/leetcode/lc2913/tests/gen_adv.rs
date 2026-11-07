use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    filler: &Vec<i32>,
    start: usize,
    end: usize,
    value: i32,
) -> (result: (Vec<i32>, usize, usize, i32))
    requires
        1 <= filler.len() <= 100,
        forall |i: int| 0 <= i < filler.len() ==> 1 <= #[trigger] filler[i] <= 100,
        start <= filler.len(),
        end <= filler.len(),
        1 <= value <= 100,
    ensures
        1 <= result.0.len() <= 100,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        result.0@ == filler@,
        result.1 == start,
        result.2 == end,
        result.3 == value,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < filler.len()
        invariant
            0 <= i <= filler.len(),
            nums.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums[k] == filler[k],
        decreases filler.len() - i,
    {
        nums.push(filler[i]);
        i += 1;
    }
    assert(nums@ =~= filler@);
    (nums, start, end, value)
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_filler(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => { for _ in 0..n { v.push(1); } }
        1 => { for i in 0..n { v.push(((i % 100) + 1) as i32); } }
        2 => { for _ in 0..n { v.push(rng.gen_i32(1, 2)); } }
        3 => { for _ in 0..n { v.push(rng.gen_i32(1, 3)); } }
        4 => { for _ in 0..n { v.push(rng.gen_i32(1, 100)); } }
        5 => { for i in 0..n { v.push((((i / 2) % 100) + 1) as i32); } }
        6 => { for i in 0..n { v.push(if i % 2 == 0 { 1 } else { 2 }); } }
        7 => {
            for i in 0..n {
                if i < n / 2 { v.push(1); } else { v.push(2); }
            }
        }
        8 => { for i in 0..n { v.push((((n - i) % 100) + 1) as i32); } }
        9 => {
            for i in 0..n {
                let k = if i < 50 { i + 1 } else { (i % 50) + 1 };
                v.push(k as i32);
            }
        }
        _ => { for _ in 0..n { v.push(rng.gen_i32(1, 10)); } }
    }
    v
}

fn print_json(nums: &[i32], start: usize, end: usize, value: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"start\":{},\"end\":{},\"value\":{}}}", start, end, value);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1,
            1 => 100,
            2 => 2,
            3 => 3,
            4 => rng.gen_range(1, 100),
            5 => rng.gen_range(1, 20),
            6 => 50,
            7 => rng.gen_range(1, 100),
            8 => 10,
            9 => 100,
            _ => rng.gen_range(1, 100),
        };
        let filler = build_filler(&mut rng, n, mode);
        let start = rng.gen_range(0, n);
        let end = rng.gen_range(0, n);
        let value = rng.gen_i32(1, 100);
        let (nums, s, e, v) = generate_test_case(&filler, start, end, value);
        print_json(&nums, s, e, v);
    }
}