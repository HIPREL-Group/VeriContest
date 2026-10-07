use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 99,
    ensures
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 99,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] nums[k] <= 99,
            forall|k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 99,
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
        Self { state: seed.wrapping_add(0xdeadbeef) }
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

fn build_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // all single digit
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 9));
            }
            v
        }
        1 => {
            // all double digit
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(10, 99));
            }
            v
        }
        2 => {
            // single-digit sum equals double-digit sum (tie => false)
            // e.g. [5,5,10]: singles=10, doubles=10 -> diff 0
            vec![5, 5, 10]
        }
        3 => {
            // exact tie larger
            vec![1, 2, 3, 4, 10]
        }
        4 => {
            // singles win
            vec![1, 2, 3, 4, 5, 14]
        }
        5 => {
            // doubles win
            vec![5, 5, 5, 25]
        }
        6 => {
            // length 1 single digit
            let x = rng.gen_range_i32(1, 9);
            vec![x]
        }
        7 => {
            // length 1 double digit
            let x = rng.gen_range_i32(10, 99);
            vec![x]
        }
        8 => {
            // all 9s and 99s (boundary)
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(9); } else { v.push(99); }
            }
            v
        }
        9 => {
            // boundary values 1, 10
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 { v.push(1); } else { v.push(10); }
            }
            v
        }
        10 => {
            // max length 100 mixed
            let mut v = Vec::new();
            for _ in 0..100 {
                v.push(rng.gen_range_i32(1, 99));
            }
            v
        }
        11 => {
            // crafted tie scenarios
            // singles: many 1s, doubles: one value equal to sum
            let k = rng.gen_range_usize(10, 50);
            let mut v = Vec::new();
            for _ in 0..k { v.push(1); }
            v.push(k as i32); // double digit if k>=10
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 99));
            }
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
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 12usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let values = build_mode(&mut rng, mode);
        // safety: ensure 1<=len<=100 and 1<=vals<=99
        if values.is_empty() || values.len() > 100 { continue; }
        let mut ok = true;
        for &x in &values {
            if x < 1 || x > 99 { ok = false; break; }
        }
        if !ok { continue; }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}