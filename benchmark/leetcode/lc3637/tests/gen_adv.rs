use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    prefix_len: usize,   // length of strictly increasing prefix (>= 2), peak index = prefix_len - 1
    mid_len: usize,      // length of strictly decreasing middle after peak (>= 2), valley index = prefix_len - 1 + mid_len - 1
    suf_len: usize,      // length of strictly increasing suffix after valley (>= 2)
    start_val: i32,      // starting value at index 0
    p_idx: usize,        // returned p
) -> (result: (Vec<i32>, usize))
    requires
        prefix_len >= 2,
        mid_len >= 2,
        suf_len >= 2,
        // Total length = prefix_len + (mid_len - 1) + (suf_len - 1)
        prefix_len + mid_len + suf_len <= 102,
        prefix_len + mid_len + suf_len >= 6,
        // Bounds: we need strictly inc/dec/inc values all in [-1000, 1000].
        // We use step size 1. Peak value = start_val + prefix_len - 1.
        // Valley = peak - (mid_len - 1). End = valley + (suf_len - 1).
        // Keep start_val chosen so everything stays in [-1000, 1000].
        -1000 <= start_val,
        start_val as int + (prefix_len as int - 1) <= 1000,
        start_val as int - (mid_len as int - 1) >= -1000,
        start_val as int + (prefix_len as int - 1) - (mid_len as int - 1) + (suf_len as int - 1) <= 1000,
        start_val as int - (mid_len as int - 1) + (suf_len as int - 1) <= 1000,
        p_idx == prefix_len - 1,
    ensures
        ({
            let nums = result.0;
            let p = result.1;
            &&& 3 <= nums.len() <= 100
            &&& forall|i: int| 0 <= i && i < nums.len() ==> -1000 <= #[trigger] nums[i] <= 1000
        }),
{
    let n: usize = prefix_len + (mid_len - 1) + (suf_len - 1);
    let mut nums: Vec<i32> = Vec::new();

    let peak_idx: usize = prefix_len - 1;
    let valley_idx: usize = prefix_len - 1 + (mid_len - 1);

    let mut i: usize = 0;
    while i < n
        invariant
            n == prefix_len + (mid_len - 1) + (suf_len - 1),
            prefix_len >= 2,
            mid_len >= 2,
            suf_len >= 2,
            peak_idx == prefix_len - 1,
            valley_idx == prefix_len - 1 + (mid_len - 1),
            nums.len() == i,
            i <= n,
            3 <= n <= 100,
            -1000 <= start_val,
            start_val as int + (prefix_len as int - 1) <= 1000,
            start_val as int - (mid_len as int - 1) >= -1000,
            start_val as int + (prefix_len as int - 1) - (mid_len as int - 1) + (suf_len as int - 1) <= 1000,
            start_val as int - (mid_len as int - 1) + (suf_len as int - 1) <= 1000,
            forall|k: int| 0 <= k && k < nums.len() ==> -1000 <= #[trigger] nums[k] <= 1000,
        decreases n - i,
    {
        let v: i32 = if i <= peak_idx {
            // increasing: start_val + i
            (start_val as i64 + i as i64) as i32
        } else if i <= valley_idx {
            // decreasing from peak: peak - (i - peak_idx)
            // peak = start_val + prefix_len - 1
            let peak_val: i64 = start_val as i64 + (prefix_len as i64 - 1);
            (peak_val - (i as i64 - peak_idx as i64)) as i32
        } else {
            // increasing from valley: valley_val + (i - valley_idx)
            let peak_val: i64 = start_val as i64 + (prefix_len as i64 - 1);
            let valley_val: i64 = peak_val - (mid_len as i64 - 1);
            (valley_val + (i as i64 - valley_idx as i64)) as i32
        };
        assert(-1000 <= v as int <= 1000);
        nums.push(v);
        i = i + 1;
    }

    assert(nums.len() == n);
    (nums, p_idx)
}

} // verus!

struct Rng { state: u64 }
impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (usize, usize, usize, i32) {
    // Returns (prefix_len, mid_len, suf_len, start_val) satisfying all preconditions.
    // total = prefix_len + mid_len + suf_len, must be in [6,102]
    // n = prefix_len + (mid_len-1) + (suf_len-1) = total - 2 in [4, 100]
    // Actually we need n in [3,100]. With prefix_len>=2, mid_len>=2, suf_len>=2, min n = 2+1+1=4.
    // So n in [4, 100].
    loop {
        let (pl, ml, sl): (usize, usize, usize) = match mode {
            0 => (2, 2, 2),
            1 => (2, 2, rng.gen_usize(2, 96)),
            2 => (rng.gen_usize(2, 96), 2, 2),
            3 => (2, rng.gen_usize(2, 96), 2),
            4 => {
                let a = rng.gen_usize(2, 30);
                let b = rng.gen_usize(2, 30);
                let c = rng.gen_usize(2, 30);
                (a, b, c)
            }
            5 => (50, 25, 25),
            6 => (33, 34, 33),
            7 => (2, 50, 48),
            8 => (48, 50, 2),
            9 => {
                let total_budget = rng.gen_usize(6, 102);
                let a = 2 + rng.gen_usize(0, (total_budget - 6) / 2);
                let remain = total_budget - a;
                if remain < 4 { (2,2,2) } else {
                    let b = 2 + rng.gen_usize(0, remain - 4);
                    let c = total_budget - a - b;
                    if c < 2 { (2,2,2) } else { (a,b,c) }
                }
            }
            _ => (rng.gen_usize(2, 30), rng.gen_usize(2, 30), rng.gen_usize(2, 30)),
        };
        if pl < 2 || ml < 2 || sl < 2 { continue; }
        let total = pl + ml + sl;
        if total < 6 || total > 102 { continue; }
        // Now find start_val such that all constraints hold.
        // Requirements:
        //   start_val >= -1000
        //   start_val + pl - 1 <= 1000
        //   start_val - (ml - 1) >= -1000  => start_val >= -1000 + (ml-1)
        //   start_val + (pl-1) - (ml-1) + (sl-1) <= 1000
        //   start_val - (ml-1) + (sl-1) <= 1000
        let lo1: i64 = -1000;
        let lo2: i64 = -1000 + (ml as i64 - 1);
        let lo: i64 = if lo1 > lo2 { lo1 } else { lo2 };
        let hi1: i64 = 1000 - (pl as i64 - 1);
        let hi2: i64 = 1000 - (pl as i64 - 1) + (ml as i64 - 1) - (sl as i64 - 1);
        let hi3: i64 = 1000 + (ml as i64 - 1) - (sl as i64 - 1);
        let mut hi: i64 = hi1;
        if hi2 < hi { hi = hi2; }
        if hi3 < hi { hi = hi3; }
        if lo > hi { continue; }
        let sv = if lo == hi { lo as i32 } else { rng.gen_i32(lo as i32, hi as i32) };
        return (pl, ml, sl, sv);
    }
}

fn print_json(nums: &Vec<i32>, p: usize) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"p\":{}}}", p);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (pl, ml, sl, sv) = pick_case(&mut rng, mode);
        let p_idx = pl - 1;
        let (nums, p) = generate_test_case(pl, ml, sl, sv, p_idx);
        print_json(&nums, p);
    }
}