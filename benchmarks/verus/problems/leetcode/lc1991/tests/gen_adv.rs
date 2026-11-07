use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= vals.len() <= 100,
        forall |i: int| 0 <= i < vals.len() ==> -1000 <= #[trigger] vals[i] <= 1000,
    ensures
        1 <= nums.len() <= 100,
        nums.len() == vals.len(),
        forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == vals.len(),
            1 <= n <= 100,
            nums.len() == i,
            forall |k: int| 0 <= k < vals.len() ==> -1000 <= #[trigger] vals[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> -1000 <= #[trigger] nums[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == vals[k],
        decreases n - i,
    {
        nums.push(vals[i]);
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_random(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 100);
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(-1000, 1000));
    }
    v
}

fn build_all_zero(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 100);
    vec![0i32; n]
}

fn build_single(rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_range_i32(-1000, 1000)]
}

fn build_two(rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_range_i32(-1000, 1000), rng.gen_range_i32(-1000, 1000)]
}

fn build_middle_at_zero(rng: &mut Rng) -> Vec<i32> {
    // left sum = 0, right sum = 0 -> rest sums to 0
    let n = rng.gen_range_usize(2, 100);
    let mut v: Vec<i32> = Vec::with_capacity(n);
    v.push(rng.gen_range_i32(-1000, 1000));
    let mut s: i64 = 0;
    for _ in 1..n-1 {
        let x = rng.gen_range_i32(-500, 500);
        v.push(x);
        s += x as i64;
    }
    // last element cancels s
    let last = (-s).max(-1000).min(1000) as i32;
    v.push(last);
    v
}

fn build_middle_at_last(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(2, 100);
    let mut v: Vec<i32> = Vec::with_capacity(n);
    let mut s: i64 = 0;
    for _ in 0..n-1 {
        let x = rng.gen_range_i32(-500, 500);
        v.push(x);
        s += x as i64;
    }
    // want left sum (excluding last, so all before last) == 0? No: middleIndex == n-1 means sum before n-1 == 0.
    // So we need sum of v[0..n-1] == 0. Adjust last pushed.
    // Simpler: regenerate with constraint
    let _ = s;
    // rebuild
    let mut v2: Vec<i32> = Vec::with_capacity(n);
    let mut ss: i64 = 0;
    for _ in 0..n-2 {
        let x = rng.gen_range_i32(-400, 400);
        v2.push(x);
        ss += x as i64;
    }
    let adj = (-ss).max(-1000).min(1000) as i32;
    v2.push(adj);
    v2.push(rng.gen_range_i32(-1000, 1000));
    v2
}

fn build_no_middle(rng: &mut Rng) -> Vec<i32> {
    // all ones, length >= 2
    let n = rng.gen_range_usize(2, 100);
    vec![1i32; n]
}

fn build_example1() -> Vec<i32> {
    vec![2, 3, -1, 8, 4]
}

fn build_example2() -> Vec<i32> {
    vec![1, -1, 4]
}

fn build_example3() -> Vec<i32> {
    vec![2, 5]
}

fn build_extremes(rng: &mut Rng) -> Vec<i32> {
    let n = rng.gen_range_usize(1, 100);
    let mut v: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let r = rng.gen_range_usize(0, 2);
        let x = match r { 0 => -1000, 1 => 1000, _ => 0 };
        v.push(x);
    }
    v
}

fn build_max_len(rng: &mut Rng) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(100);
    for _ in 0..100 {
        v.push(rng.gen_range_i32(-1000, 1000));
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
    let total = 200usize;

    for t in 0..total {
        let mode = t % 11;
        let vals = match mode {
            0 => build_random(&mut rng),
            1 => build_all_zero(&mut rng),
            2 => build_single(&mut rng),
            3 => build_two(&mut rng),
            4 => build_middle_at_zero(&mut rng),
            5 => build_middle_at_last(&mut rng),
            6 => build_no_middle(&mut rng),
            7 => build_extremes(&mut rng),
            8 => build_max_len(&mut rng),
            9 => {
                if t == 9 { build_example1() }
                else if t == 20 { build_example2() }
                else { build_example3() }
            }
            _ => build_random(&mut rng),
        };
        let nums = generate_test_case(&vals);
        print_json(&nums);
    }
}