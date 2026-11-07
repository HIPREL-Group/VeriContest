use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() - 1 ==> #[trigger] values[i] != values[i + 1],
    ensures
        1 <= nums.len() <= 1000,
        nums.len() == values.len(),
        forall |i: int| 0 <= i < nums.len() - 1 ==> #[trigger] nums[i] != nums[i + 1],
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            n == values.len(),
            0 <= k <= n,
            nums.len() == k,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums[i] == values[i],
        decreases n - k,
    {
        nums.push(values[k]);
        k = k + 1;
    }

    assert forall |i: int| 0 <= i < nums.len() - 1 implies #[trigger] nums[i] != nums[i + 1] by {
        assert(nums[i] == values[i]);
        assert(nums[i + 1] == values[i + 1]);
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn ensure_distinct_adjacent(v: &mut Vec<i32>, rng: &mut Rng) {
    let n = v.len();
    for i in 1..n {
        if v[i] == v[i - 1] {
            // perturb
            let prev = v[i - 1];
            let mut new_val = if prev < i32::MAX { prev + 1 } else { prev - 1 };
            if i + 1 < n && new_val == v[i + 1] {
                // pick another
                new_val = if prev > i32::MIN + 1 { prev - 1 } else { prev + 2 };
                if i + 1 < n && new_val == v[i + 1] {
                    new_val = rng.gen_range_i32(-1000, 1000);
                    while new_val == prev || (i + 1 < n && new_val == v[i + 1]) {
                        new_val = new_val.wrapping_add(1);
                    }
                }
            }
            v[i] = new_val;
        }
    }
    // final pass
    for i in 1..n {
        if v[i] == v[i - 1] {
            // fix by increment/decrement using wraparound-safe logic
            let prev = v[i - 1];
            let mut candidate = prev.wrapping_add(1);
            if i + 1 < n && candidate == v[i + 1] {
                candidate = prev.wrapping_sub(1);
            }
            if candidate == prev {
                candidate = prev.wrapping_add(2);
            }
            v[i] = candidate;
        }
    }
}

fn make_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    ensure_distinct_adjacent(&mut v, rng);
    v
}

fn make_increasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(i as i32 - (n as i32 / 2));
    }
    v
}

fn make_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push((n as i32 / 2) - i as i32);
    }
    v
}

fn make_zigzag(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 {
            v.push(0);
        } else {
            v.push(1);
        }
    }
    v
}

fn make_peak_middle(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..n {
        if i <= mid {
            v.push(i as i32);
        } else {
            v.push((2 * mid) as i32 - i as i32);
        }
    }
    // ensure adjacency
    v
}

fn make_peak_left(n: usize) -> Vec<i32> {
    // strictly decreasing - peak at 0
    make_decreasing(n)
}

fn make_peak_right(n: usize) -> Vec<i32> {
    // strictly increasing - peak at n-1
    make_increasing(n)
}

fn make_extreme(n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 {
            v.push(i32::MAX);
        } else {
            v.push(i32::MIN);
        }
        let _ = rng.next_u64();
    }
    v
}

fn make_two_peaks(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let q1 = n / 4;
    let q3 = 3 * n / 4;
    for i in 0..n {
        let d1 = if i <= q1 { i as i32 } else { 2 * q1 as i32 - i as i32 };
        let d2 = if i <= q3 { i as i32 - q1 as i32 * 2 } else { 2 * q3 as i32 - 2 * q1 as i32 - i as i32 };
        v.push(d1.max(d2).max(-1000));
    }
    v
}

fn make_single(_n: usize, rng: &mut Rng) -> Vec<i32> {
    vec![rng.gen_range_i32(-1000, 1000)]
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn validate_and_fix(v: &mut Vec<i32>, rng: &mut Rng) {
    if v.is_empty() {
        v.push(0);
    }
    if v.len() > 1000 {
        v.truncate(1000);
    }
    ensure_distinct_adjacent(v, rng);
    // Final fallback: if still bad, replace with alternating
    let mut bad = false;
    for i in 1..v.len() {
        if v[i] == v[i - 1] { bad = true; break; }
    }
    if bad {
        for i in 0..v.len() {
            v[i] = if i % 2 == 0 { 0 } else { 1 };
        }
    }
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
        let mode = t % 10;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 1000,
            3 => 3 + (t % 20),
            4 => 500,
            5 => 1000,
            6 => 100 + (t % 50),
            7 => 1000,
            8 => 50,
            _ => 10 + (t % 40),
        };

        let mut v = match mode {
            0 => make_single(n, &mut rng),
            1 => make_random(&mut rng, n, -1000, 1000),
            2 => make_increasing(n),
            3 => make_decreasing(n),
            4 => make_zigzag(n),
            5 => make_peak_middle(n),
            6 => make_two_peaks(n),
            7 => make_extreme(n, &mut rng),
            8 => make_peak_left(n),
            _ => make_random(&mut rng, n, i32::MIN, i32::MAX),
        };

        validate_and_fix(&mut v, &mut rng);

        // Only pass if valid
        if v.len() >= 1 && v.len() <= 1000 {
            let mut ok = true;
            for i in 1..v.len() {
                if v[i] == v[i - 1] { ok = false; break; }
            }
            if ok {
                let nums = generate_test_case(&v);
                print_json(&nums);
            }
        }
    }
}