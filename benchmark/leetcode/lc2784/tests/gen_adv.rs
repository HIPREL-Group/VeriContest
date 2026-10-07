use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    extra_len: usize,
    extras: &Vec<i32>,
    perm: &Vec<usize>,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 99,
        extra_len <= 99,
        n as int + 1 + extra_len as int <= 100,
        n as int + 1 + extra_len as int >= 1,
        extras.len() == extra_len,
        perm.len() == n as int + 1 + extra_len as int,
        forall |i: int| 0 <= i < extras.len() ==> 1 <= #[trigger] extras[i] <= 200,
        forall |i: int| 0 <= i < perm.len() ==> #[trigger] perm[i] < perm.len(),
    ensures
        1 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 200,
{
    // Build base array: [1, 2, ..., n, n] plus extras
    let total: usize = n + 1 + extra_len;
    let mut base: Vec<i32> = Vec::new();
    let mut i: usize = 1;
    while i <= n
        invariant
            1 <= i <= n + 1,
            1 <= n <= 99,
            base.len() == i - 1,
            forall |k: int| 0 <= k < base.len() ==> 1 <= #[trigger] base[k] <= 200,
        decreases (n + 1) - i,
    {
        base.push(i as i32);
        i = i + 1;
    }
    base.push(n as i32);
    // Append extras
    let mut j: usize = 0;
    while j < extra_len
        invariant
            0 <= j <= extra_len,
            extras.len() == extra_len,
            base.len() == n + 1 + j,
            forall |k: int| 0 <= k < base.len() ==> 1 <= #[trigger] base[k] <= 200,
            forall |i: int| 0 <= i < extras.len() ==> 1 <= #[trigger] extras[i] <= 200,
        decreases extra_len - j,
    {
        base.push(extras[j]);
        j = j + 1;
    }

    // Now permute using perm; perm may have duplicates, but that's fine since we just read values.
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < total
        invariant
            total == n + 1 + extra_len,
            base.len() == total,
            perm.len() == total,
            0 <= k <= total,
            nums.len() == k,
            forall |a: int| 0 <= a < base.len() ==> 1 <= #[trigger] base[a] <= 200,
            forall |a: int| 0 <= a < perm.len() ==> #[trigger] perm[a] < perm.len(),
            forall |a: int| 0 <= a < nums.len() ==> 1 <= #[trigger] nums[a] <= 200,
        decreases total - k,
    {
        let idx = perm[k];
        assert(idx < perm.len());
        assert(idx < base.len());
        nums.push(base[idx]);
        k = k + 1;
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
        lo + (self.next_u64() % span) as i32
    }
}

fn shuffle(rng: &mut Rng, v: &mut Vec<usize>) {
    let n = v.len();
    if n <= 1 { return; }
    let mut i = n - 1;
    while i > 0 {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
        i -= 1;
    }
}

fn build(rng: &mut Rng, n: usize, extra_len: usize, extras: Vec<i32>) -> (usize, usize, Vec<i32>, Vec<usize>) {
    let total = n + 1 + extra_len;
    let mut perm: Vec<usize> = (0..total).collect();
    shuffle(rng, &mut perm);
    (n, extra_len, extras, perm)
}

fn mode_case(rng: &mut Rng, mode: usize) -> (usize, usize, Vec<i32>, Vec<usize>) {
    match mode {
        0 => {
            // Good case: n random in [1..49], no extras
            let n = rng.gen_range_usize(1, 49);
            build(rng, n, 0, Vec::new())
        }
        1 => {
            // Good case small
            build(rng, 1, 0, Vec::new())
        }
        2 => {
            // Good case max size: n=99, total=100
            build(rng, 99, 0, Vec::new())
        }
        3 => {
            // Bad: too many elements (extras present)
            let n = rng.gen_range_usize(1, 40);
            let extra = rng.gen_range_usize(1, 100 - (n + 1));
            let mut ex = Vec::new();
            for _ in 0..extra {
                ex.push(rng.gen_range_i32(1, n as i32));
            }
            build(rng, n, extra, ex)
        }
        4 => {
            // Bad: extras with values > n (e.g., 200)
            let n = rng.gen_range_usize(1, 40);
            let extra = rng.gen_range_usize(1, 100 - (n + 1));
            let mut ex = Vec::new();
            for _ in 0..extra {
                ex.push(rng.gen_range_i32(n as i32 + 1, 200));
            }
            build(rng, n, extra, ex)
        }
        5 => {
            // Good case with n=2
            build(rng, 2, 0, Vec::new())
        }
        6 => {
            // Bad: extras equal to 1 (duplicates)
            let n = rng.gen_range_usize(2, 40);
            let extra = rng.gen_range_usize(1, 100 - (n + 1));
            let mut ex = Vec::new();
            for _ in 0..extra {
                ex.push(1);
            }
            build(rng, n, extra, ex)
        }
        7 => {
            // Single element [v] - length 1, not good
            let v = rng.gen_range_i32(1, 200);
            // simulate as n=0? Not allowed. Instead use n=1 + nothing, but that's good.
            // Make length 1 via... can't since min n=1 gives length 2. Skip: use good n=1.
            let _ = v;
            build(rng, 1, 0, Vec::new())
        }
        8 => {
            // Bad: all extras large values
            let n = rng.gen_range_usize(1, 30);
            let extra = rng.gen_range_usize(1, 100 - (n + 1));
            let mut ex = Vec::new();
            for _ in 0..extra {
                ex.push(200);
            }
            build(rng, n, extra, ex)
        }
        9 => {
            // Good large
            let n = rng.gen_range_usize(50, 99);
            build(rng, n, 0, Vec::new())
        }
        _ => {
            // Mixed random
            let n = rng.gen_range_usize(1, 60);
            let max_extra = 100 - (n + 1);
            let extra = if max_extra == 0 { 0 } else { rng.gen_range_usize(0, max_extra) };
            let mut ex = Vec::new();
            for _ in 0..extra {
                ex.push(rng.gen_range_i32(1, 200));
            }
            build(rng, n, extra, ex)
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("],\"target\":0,\"idx\":0}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (n, extra_len, extras, perm) = mode_case(&mut rng, mode);
        let nums = generate_test_case(n, extra_len, &extras, &perm);
        print_json(&nums);
    }
}