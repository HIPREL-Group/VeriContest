use vstd::prelude::*;

verus! {

pub open spec fn mask_for(mb: i32) -> i32 {
    !(!0i32 << (mb as u32))
}

pub fn generate_test_case(
    n: usize,
    maximum_bit: i32,
    vals: &Vec<i32>,
    mask_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= n <= 100_000,
        1 <= maximum_bit <= 20,
        vals.len() == n,
        mask_val == mask_for(maximum_bit),
        0 <= mask_val,
        forall |i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= mask_val,
        forall |i: int, j: int| 0 <= i < j < vals.len() ==> vals[i] <= vals[j],
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1 <= 20,
        result.1 == maximum_bit,
        result.0.len() == n,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= mask_for(result.1),
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] <= result.0[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx <= n,
            nums.len() == idx,
            vals.len() == n,
            mask_val == mask_for(maximum_bit),
            0 <= mask_val,
            forall |i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= mask_val,
            forall |i: int, j: int| 0 <= i < j < vals.len() ==> vals[i] <= vals[j],
            forall |i: int| 0 <= i < nums.len() ==> #[trigger] nums[i] == vals[i],
        decreases n - idx,
    {
        nums.push(vals[idx]);
        idx = idx + 1;
    }

    assert(forall |i: int| 0 <= i < nums.len() ==> nums[i] == vals[i]);
    assert(forall |i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= mask_for(maximum_bit));
    assert(forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] <= nums[j]);

    (nums, maximum_bit)
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

fn compute_mask(mb: i32) -> i32 {
    // !(!0i32 << mb)
    let shifted = (!0i32).wrapping_shl(mb as u32);
    !shifted
}

fn make_sorted_vals(rng: &mut Rng, n: usize, mask: i32, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // all mask (max value)
            for _ in 0..n { v.push(mask); }
        }
        2 => {
            // random sorted
            let mut tmp: Vec<i32> = Vec::with_capacity(n);
            for _ in 0..n {
                tmp.push(rng.gen_range_i32(0, mask));
            }
            tmp.sort();
            v = tmp;
        }
        3 => {
            // strictly increasing starting at 0 (if room)
            let start = 0i32;
            let step = if n > 0 { std::cmp::max(1i32, mask / (n as i32).max(1)) } else { 1 };
            let mut cur = start;
            for _ in 0..n {
                v.push(cur);
                let next = cur as i64 + step as i64;
                cur = if next > mask as i64 { mask } else { next as i32 };
            }
        }
        4 => {
            // all same random
            let x = rng.gen_range_i32(0, mask);
            for _ in 0..n { v.push(x); }
        }
        5 => {
            // half zeros half mask
            let half = n / 2;
            for _ in 0..half { v.push(0); }
            for _ in half..n { v.push(mask); }
        }
        6 => {
            // sequential 0,1,2,... clamped to mask
            for i in 0..n {
                let vv = if (i as i64) > mask as i64 { mask } else { i as i32 };
                v.push(vv);
            }
        }
        7 => {
            // random small values sorted
            let mut tmp: Vec<i32> = Vec::with_capacity(n);
            let cap = std::cmp::min(mask, 3);
            for _ in 0..n {
                tmp.push(rng.gen_range_i32(0, cap));
            }
            tmp.sort();
            v = tmp;
        }
        8 => {
            // powers of 2 pattern (sorted)
            let mut tmp: Vec<i32> = Vec::with_capacity(n);
            let mut p: i32 = 1;
            for _ in 0..n {
                let vv = if p > mask || p < 0 { mask } else { p };
                tmp.push(vv);
                let np = p.wrapping_mul(2);
                if np > mask || np <= 0 { p = mask; } else { p = np; }
            }
            tmp.sort();
            v = tmp;
        }
        9 => {
            // only 0 and mask alternating then sorted
            let mut tmp: Vec<i32> = Vec::with_capacity(n);
            for i in 0..n {
                tmp.push(if i % 2 == 0 { 0 } else { mask });
            }
            tmp.sort();
            v = tmp;
        }
        _ => {
            let mut tmp: Vec<i32> = Vec::with_capacity(n);
            for _ in 0..n {
                tmp.push(rng.gen_range_i32(0, mask));
            }
            tmp.sort();
            v = tmp;
        }
    }
    // Ensure length n and all in [0, mask] and sorted
    while v.len() < n { v.push(0); }
    if v.len() > n { v.truncate(n); }
    for x in v.iter_mut() {
        if *x < 0 { *x = 0; }
        if *x > mask { *x = mask; }
    }
    v.sort();
    v
}

fn print_json(nums: &[i32], mb: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"maximum_bit\":{}}}", mb);
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
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let maximum_bit: i32 = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 8,
            4 => 20,
            5 => rng.gen_range_i32(1, 20),
            _ => rng.gen_range_i32(1, 10),
        };
        let mask = compute_mask(maximum_bit);
        let n: usize = match t % 8 {
            0 => 1,
            1 => 2,
            2 => 10,
            3 => 100,
            4 => 1000,
            5 => 100_000,
            6 => rng.gen_range_usize(1, 500),
            _ => rng.gen_range_usize(1, 2000),
        };
        let vals = make_sorted_vals(&mut rng, n, mask, mode);
        // sanity
        assert!(vals.len() == n);
        for i in 0..vals.len() {
            assert!(vals[i] >= 0 && vals[i] <= mask);
            if i > 0 { assert!(vals[i-1] <= vals[i]); }
        }
        let (nums, mb) = generate_test_case(n, maximum_bit, &vals, mask);
        print_json(&nums, mb);
    }
}