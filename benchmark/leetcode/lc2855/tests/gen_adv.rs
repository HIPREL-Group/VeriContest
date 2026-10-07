use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (nums: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
        forall |i: int, j: int| 0 <= i < j < values.len() ==> values[i] != values[j],
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
{
    let n = values.len();
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            n == values.len(),
            nums.len() == idx,
            1 <= n <= 100,
            forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
            forall |i: int, j: int| 0 <= i < j < values.len() ==> values[i] != values[j],
            forall |k: int| 0 <= k < idx as int ==> #[trigger] nums[k] == values[k],
        decreases n - idx,
    {
        nums.push(values[idx]);
        idx = idx + 1;
    }

    proof {
        assert forall |i: int, j: int| 0 <= i < j < nums.len() implies nums[i] != nums[j] by {
            assert(nums[i] == values[i]);
            assert(nums[j] == values[j]);
        }
        assert forall |i: int| 0 <= i < nums.len() implies 1 <= #[trigger] nums[i] <= 100 by {
            assert(nums[i] == values[i]);
        }
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
}

// Build distinct values in [1,100]
fn distinct_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    // create a shuffled range [1..=100] and take first n
    let mut pool: Vec<i32> = (1..=100).collect();
    // Fisher-Yates shuffle
    for i in (1..pool.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        pool.swap(i, j);
    }
    pool.truncate(n);
    pool
}

fn sorted_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = distinct_values(rng, n);
    v.sort();
    v
}

fn right_shift(v: &[i32], k: usize) -> Vec<i32> {
    let n = v.len();
    if n == 0 { return Vec::new(); }
    let k = k % n;
    let mut out = vec![0i32; n];
    for i in 0..n {
        out[(i + k) % n] = v[i];
    }
    out
}

fn adversarial(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // already sorted, small
            let n = rng.gen_range_usize(1, 10);
            sorted_values(rng, n)
        }
        1 => {
            // already sorted, max size
            sorted_values(rng, 100)
        }
        2 => {
            // single element
            let x = rng.gen_range_usize(1, 100) as i32;
            vec![x]
        }
        3 => {
            // sorted then right-shifted by random k
            let n = rng.gen_range_usize(2, 20);
            let s = sorted_values(rng, n);
            let k = rng.gen_range_usize(0, n - 1);
            right_shift(&s, k)
        }
        4 => {
            // shift by 1
            let n = rng.gen_range_usize(2, 100);
            let s = sorted_values(rng, n);
            right_shift(&s, 1)
        }
        5 => {
            // shift by n-1
            let n = rng.gen_range_usize(2, 100);
            let s = sorted_values(rng, n);
            right_shift(&s, n - 1)
        }
        6 => {
            // completely random, likely unsortable
            let n = rng.gen_range_usize(3, 100);
            distinct_values(rng, n)
        }
        7 => {
            // reverse sorted (unsortable for n>=2)
            let n = rng.gen_range_usize(2, 50);
            let mut s = sorted_values(rng, n);
            s.reverse();
            s
        }
        8 => {
            // size 2 cases
            let a = rng.gen_range_usize(1, 100) as i32;
            let mut b = rng.gen_range_usize(1, 100) as i32;
            while b == a { b = rng.gen_range_usize(1, 100) as i32; }
            vec![a, b]
        }
        9 => {
            // Full size shifted
            let s = sorted_values(rng, 100);
            let k = rng.gen_range_usize(0, 99);
            right_shift(&s, k)
        }
        _ => {
            // swap two elements in sorted
            let n = rng.gen_range_usize(3, 30);
            let mut s = sorted_values(rng, n);
            let i = rng.gen_range_usize(0, n - 1);
            let j = rng.gen_range_usize(0, n - 1);
            s.swap(i, j);
            let _ = t;
            s
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

fn validate(v: &[i32]) -> bool {
    if v.is_empty() || v.len() > 100 { return false; }
    for &x in v { if x < 1 || x > 100 { return false; } }
    for i in 0..v.len() {
        for j in (i+1)..v.len() {
            if v[i] == v[j] { return false; }
        }
    }
    true
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
        let values = adversarial(&mut rng, mode, t);
        if !validate(&values) { continue; }
        let nums = generate_test_case(&values);
        print_json(&nums);
    }
}