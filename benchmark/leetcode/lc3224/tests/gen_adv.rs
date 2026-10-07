use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n_half: usize,
    k: i32,
    vals: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n_half <= 50000,
        0 <= k <= 100000,
        vals.len() == 2 * n_half,
        forall |i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= k,
    ensures
        2 <= result.0.len() <= 100000,
        result.0.len() % 2 == 0,
        0 <= result.1 <= 100000,
        result.1 == k,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= result.1,
{
    let n: usize = 2 * n_half;
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            n == 2 * n_half,
            1 <= n_half <= 50000,
            0 <= k <= 100000,
            vals.len() == n,
            idx <= n,
            nums.len() == idx,
            forall |i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= k,
            forall |i: int| 0 <= i < nums.len() ==> nums[i] == vals[i],
        decreases n - idx,
    {
        nums.push(vals[idx]);
        idx = idx + 1;
    }
    assert(nums.len() == n);
    assert(n % 2 == 0) by {
        assert(n == 2 * n_half);
    }
    (nums, k)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vals(rng: &mut Rng, n: usize, k: i32, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => { // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => { // all k
            for _ in 0..n { v.push(k); }
        }
        2 => { // all same random
            let x = rng.gen_range_i32(0, k);
            for _ in 0..n { v.push(x); }
        }
        3 => { // alternating 0 and k
            for i in 0..n { v.push(if i % 2 == 0 { 0 } else { k }); }
        }
        4 => { // pairs with constant difference
            let x = rng.gen_range_i32(0, k);
            for i in 0..n/2 {
                let a = rng.gen_range_i32(0, k - x.min(k));
                v.push(a);
            }
            // we'll fix symmetry after
            for i in 0..n/2 { v.push(0); }
            // rebuild properly
            v.clear();
            let diff = rng.gen_range_i32(0, k);
            for _ in 0..n/2 {
                let a = rng.gen_range_i32(0, k);
                let b = if a + diff <= k { a + diff } else if a - diff >= 0 { a - diff } else { a };
                v.push(a);
                v.push(b);
            }
            // arrange as symmetric pairs: we want nums[i] and nums[n-1-i] to have same diff
            // current layout places pairs adjacent; reshape into symmetric layout
            let mut v2 = vec![0i32; n];
            for i in 0..n/2 {
                v2[i] = v[2*i];
                v2[n-1-i] = v[2*i+1];
            }
            v = v2;
        }
        5 => { // sequential
            for i in 0..n {
                v.push((i as i32) % (k + 1));
            }
        }
        6 => { // max diff pairs
            for i in 0..n/2 { v.push(0); }
            for i in 0..n/2 { v.push(k); }
            // make symmetric
            let mut v2 = vec![0i32; n];
            for i in 0..n/2 {
                v2[i] = 0;
                v2[n-1-i] = k;
            }
            v = v2;
        }
        7 => { // random
            for _ in 0..n { v.push(rng.gen_range_i32(0, k)); }
        }
        8 => { // mostly zeros one spike
            for _ in 0..n { v.push(0); }
            if n > 0 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = k;
            }
        }
        9 => { // two different diffs
            let mut v2 = vec![0i32; n];
            for i in 0..n/2 {
                if i % 2 == 0 {
                    v2[i] = 0;
                    v2[n-1-i] = k;
                } else {
                    v2[i] = 0;
                    v2[n-1-i] = 0;
                }
            }
            v = v2;
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(0, k)); }
        }
    }
    // safety: clamp
    for i in 0..v.len() {
        if v[i] < 0 { v[i] = 0; }
        if v[i] > k { v[i] = k; }
    }
    v
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n_half = match t % 7 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(1, 10),
            3 => rng.gen_range_usize(50, 500),
            4 => rng.gen_range_usize(500, 5000),
            5 => 50000,
            _ => rng.gen_range_usize(1, 1000),
        };
        let n = 2 * n_half;
        let k = match t % 5 {
            0 => 0,
            1 => 1,
            2 => 100000,
            3 => rng.gen_range_i32(1, 100),
            _ => rng.gen_range_i32(0, 100000),
        };

        let vals = build_vals(&mut rng, n, k, mode);
        // ensure length is exactly n and values in [0,k]
        let mut vals = vals;
        if vals.len() != n {
            vals.resize(n, 0);
        }
        for i in 0..vals.len() {
            if vals[i] < 0 { vals[i] = 0; }
            if vals[i] > k { vals[i] = k; }
        }

        let (nums, kk) = generate_test_case(n_half, k, &vals);
        print_json(&nums, kk);
    }
}