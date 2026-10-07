use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 10_000,
        forall |i: int| 0 <= i < values.len() ==> -1000 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= nums.len() <= 10_000,
        forall |i: int| 0 <= i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000,
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            nums.len() == i,
            1 <= n <= 10_000,
            forall |k: int| 0 <= k < values.len() ==> -1000 <= #[trigger] values[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> nums[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> -1000 <= #[trigger] nums[k] <= 1000,
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(-1000, 1000));
    }
    v
}

fn build_all_same(n: usize, val: i32) -> Vec<i32> {
    let clamped = if val > 1000 { 1000 } else if val < -1000 { -1000 } else { val };
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(clamped); }
    v
}

fn build_all_zero(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n { v.push(0); }
    v
}

fn build_pivot_at(rng: &mut Rng, n: usize, pivot: usize) -> Vec<i32> {
    // Build sums that are equal on both sides. Fill fillers randomly in [-100,100].
    let mut left: Vec<i32> = Vec::new();
    let mut right: Vec<i32> = Vec::new();
    let mut lsum: i64 = 0;
    let mut rsum: i64 = 0;
    for _ in 0..pivot {
        let x = rng.gen_range_i32(-100, 100);
        left.push(x);
        lsum += x as i64;
    }
    for _ in (pivot + 1)..n {
        let x = rng.gen_range_i32(-100, 100);
        right.push(x);
        rsum += x as i64;
    }
    // Need to adjust: we want lsum == rsum. Adjust one element if possible.
    let diff = lsum - rsum; // want to reduce left by diff or increase right by diff
    // Try to put adjustment in right side by modifying one element; if that exceeds bounds, skip
    let mut adjusted = false;
    if !right.is_empty() {
        let old = right[0] as i64;
        let newv = old + diff;
        if newv >= -1000 && newv <= 1000 {
            right[0] = newv as i32;
            adjusted = true;
        }
    }
    if !adjusted && !left.is_empty() {
        let old = left[0] as i64;
        let newv = old - diff;
        if newv >= -1000 && newv <= 1000 {
            left[0] = newv as i32;
            adjusted = true;
        }
    }
    // Pivot value itself
    let pv = rng.gen_range_i32(-1000, 1000);
    let mut v = Vec::with_capacity(n);
    for x in left { v.push(x); }
    v.push(pv);
    for x in right { v.push(x); }
    // Clamp any out of range just in case
    for i in 0..v.len() {
        if v[i] > 1000 { v[i] = 1000; }
        if v[i] < -1000 { v[i] = -1000; }
    }
    v
}

fn build_adversarial(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    match mode {
        0 => build_random(rng, n),
        1 => build_all_zero(n),
        2 => build_all_same(n, 1000),
        3 => build_all_same(n, -1000),
        4 => {
            // single element
            vec![rng.gen_range_i32(-1000, 1000)]
        }
        5 => {
            // pivot at index 0
            build_pivot_at(rng, n, 0)
        }
        6 => {
            // pivot at last index
            build_pivot_at(rng, n, if n > 0 { n - 1 } else { 0 })
        }
        7 => {
            // pivot in middle
            build_pivot_at(rng, n, n / 2)
        }
        8 => {
            // alternating +1 / -1
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { -1 });
            }
            v
        }
        9 => {
            // ascending
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let x = (i as i32) % 2001 - 1000;
                v.push(x);
            }
            v
        }
        _ => {
            // small range random
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-5, 5));
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = if mode == 4 {
            1
        } else {
            match t % 7 {
                0 => 2,
                1 => 3,
                2 => 10,
                3 => 100,
                4 => 1000,
                5 => 10_000,
                _ => rng.gen_range_usize(1, 500),
            }
        };
        let values = build_adversarial(&mut rng, mode, n);
        // ensure values are within bounds and length within range
        let mut v = values;
        if v.len() == 0 { v.push(0); }
        if v.len() > 10_000 { v.truncate(10_000); }
        for i in 0..v.len() {
            if v[i] > 1000 { v[i] = 1000; }
            if v[i] < -1000 { v[i] = -1000; }
        }
        let nums = generate_test_case(&v);
        print_json(&nums);
    }
}