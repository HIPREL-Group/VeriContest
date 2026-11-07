use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    elements: &Vec<i32>,
    val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        0 <= elements.len() <= 100,
        forall|i: int| 0 <= i < elements.len() ==> 0 <= #[trigger] elements[i] <= 50,
        0 <= val <= 100,
    ensures
        0 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 50,
        0 <= result.1 <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = elements.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == elements.len(),
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] nums[k] <= 50,
            forall|k: int| 0 <= k < elements.len() ==> 0 <= #[trigger] elements[k] <= 50,
            forall|k: int| 0 <= k < i as int ==> nums[k] == elements[k],
        decreases n - i,
    {
        nums.push(elements[i]);
        i = i + 1;
    }
    (nums, val)
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
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // empty
            (Vec::new(), rng.gen_range_i32(0, 100))
        }
        1 => {
            // all equal to val
            let n = rng.gen_range_usize(1, 100);
            let val = rng.gen_range_i32(0, 50);
            let mut v = Vec::new();
            for _ in 0..n { v.push(val); }
            (v, val)
        }
        2 => {
            // none equal to val (val > 50)
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            (v, rng.gen_range_i32(51, 100))
        }
        3 => {
            // single element equal to val
            let val = rng.gen_range_i32(0, 50);
            (vec![val], val)
        }
        4 => {
            // single element not equal
            let val = rng.gen_range_i32(0, 50);
            let e = if val == 0 { 1 } else { 0 };
            (vec![e], val)
        }
        5 => {
            // max length, mixed
            let val = rng.gen_range_i32(0, 50);
            let mut v = Vec::new();
            for _ in 0..100 { v.push(rng.gen_range_i32(0, 50)); }
            (v, val)
        }
        6 => {
            // val at the end only
            let n = rng.gen_range_usize(2, 100);
            let val = rng.gen_range_i32(0, 50);
            let other = if val == 0 { 1 } else { 0 };
            let mut v = Vec::new();
            for _ in 0..(n-1) { v.push(other); }
            v.push(val);
            (v, val)
        }
        7 => {
            // val at the start only
            let n = rng.gen_range_usize(2, 100);
            let val = rng.gen_range_i32(0, 50);
            let other = if val == 0 { 1 } else { 0 };
            let mut v = Vec::new();
            v.push(val);
            for _ in 1..n { v.push(other); }
            (v, val)
        }
        8 => {
            // alternating val/not-val
            let n = rng.gen_range_usize(2, 100);
            let val = rng.gen_range_i32(0, 50);
            let other = if val == 0 { 1 } else { 0 };
            let mut v = Vec::new();
            for i in 0..n {
                if i % 2 == 0 { v.push(val); } else { v.push(other); }
            }
            (v, val)
        }
        9 => {
            // val = 100 (cannot appear in nums since nums[i] <= 50)
            let n = rng.gen_range_usize(0, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            (v, 100)
        }
        _ => {
            // random
            let n = rng.gen_range_usize(0, 100);
            let val = rng.gen_range_i32(0, 100);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.gen_range_i32(0, 50)); }
            (v, val)
        }
    }
}

fn print_json(nums: &[i32], val: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"val\":{}}}", val);
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
        let (elements, val) = gen_mode(&mut rng, mode);
        let (nums, v) = generate_test_case(&elements, val);
        print_json(&nums, v);
    }
}