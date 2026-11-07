use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        3 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> -100 <= #[trigger] result[i] <= 100,
{
    let n = if values.len() < 3 { 3usize }
            else if values.len() > 100 { 100usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            3 <= n <= 100,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> -100 <= #[trigger] result[j] <= 100,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { -100 };
        let value = if value < -100 { -100 } else if value > 100 { 100 } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        3 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> -100 <= #[trigger] values[i] <= 100,
    ensures
        3 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> -100 <= #[trigger] nums[i] <= 100,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            3 <= n <= 100,
            0 <= i <= n,
            nums.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -100 <= #[trigger] values[k] <= 100,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> -100 <= #[trigger] nums[k] <= 100,
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp(v: i32) -> i32 {
    if v < -100 { -100 } else if v > 100 { 100 } else { v }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = rng.gen_range_usize(3, 100);
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // fully random
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
        1 => {
            // all zeros
            for _ in 0..n {
                v.push(0);
            }
        }
        2 => {
            // triples satisfying condition: a, 2*(a+c), c
            let mut i = 0;
            while i < n {
                if i + 2 < n {
                    let a = rng.gen_range_i32(-25, 25);
                    let c = rng.gen_range_i32(-25, 25);
                    let b = clamp(2 * (a + c));
                    v.push(a);
                    v.push(b);
                    v.push(c);
                    i += 3;
                } else {
                    v.push(rng.gen_range_i32(-100, 100));
                    i += 1;
                }
            }
        }
        3 => {
            // all same small value
            let x = rng.gen_range_i32(-5, 5);
            for _ in 0..n {
                v.push(x);
            }
        }
        4 => {
            // extreme values
            for _ in 0..n {
                let r = rng.next_u64() % 4;
                v.push(match r { 0 => -100, 1 => 100, 2 => 0, _ => rng.gen_range_i32(-100, 100) });
            }
        }
        5 => {
            // length exactly 3
            let v2: Vec<i32> = vec![rng.gen_range_i32(-100,100), rng.gen_range_i32(-100,100), rng.gen_range_i32(-100,100)];
            return v2;
        }
        6 => {
            // length exactly 3 satisfying
            let a = rng.gen_range_i32(-25, 25);
            let c = rng.gen_range_i32(-25, 25);
            let b = clamp(2 * (a + c));
            return vec![a, b, c];
        }
        7 => {
            // max length
            for _ in 0..100 {
                v.push(rng.gen_range_i32(-100, 100));
            }
            return v;
        }
        8 => {
            // odd middles (2*(a+c) must be even, so no triple works for odd b)
            for _ in 0..n {
                let r = rng.next_u64() % 2;
                v.push(if r == 0 { rng.gen_range_i32(-50, 50) * 2 + 1 } else { rng.gen_range_i32(-50, 50) });
            }
        }
        9 => {
            // alternating pattern
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 4 });
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(-100, 100));
            }
        }
    }
    v
}

fn print_json(nums: &[i32]) {
    let nums = generate_test_case(nums.to_vec());
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
    let total = 220usize;
    let modes = 10usize;
    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode);
        // ensure validity
        if values.len() < 3 || values.len() > 100 {
            continue;
        }
        let mut ok = true;
        for &x in &values {
            if x < -100 || x > 100 { ok = false; break; }
        }
        if !ok { continue; }
        let nums = generate_candidate(&values);
        print_json(&nums);
    }
}
