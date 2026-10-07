use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    x: i32,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 100,
        forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
        -1000 <= x <= 1000,
        forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] (nums1[i] as int) + (x as int) <= 1000,
    ensures
        1 <= result.0.len() <= 100,
        result.0.len() == result.1.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> #[trigger] result.0[i] as int + (result.1[0] as int - result.0[0] as int) == result.1[i] as int,
{
    let n = nums1.len();
    let mut nums2: Vec<i32> = Vec::new();
    let mut k: usize = 0;

    while k < n
        invariant
            n == nums1.len(),
            1 <= n <= 100,
            0 <= k <= n,
            nums2.len() == k,
            -1000 <= x <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] (nums1[i] as int) + (x as int) <= 1000,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums2[i] as int == nums1[i] as int + x as int,
            forall |i: int| 0 <= i < k as int ==> 0 <= #[trigger] nums2[i] <= 1000,
        decreases n - k,
    {
        let v: i32 = nums1[k] + x;
        assert(v as int == nums1[k as int] as int + x as int);
        assert(0 <= v <= 1000);
        nums2.push(v);
        k = k + 1;
    }

    proof {
        assert(nums2.len() == nums1.len());
        assert forall |i: int| 0 <= i < nums1.len() implies
            #[trigger] nums1[i] as int + (nums2[0] as int - nums1[0] as int) == nums2[i] as int
        by {
            assert(nums2[0] as int == nums1[0] as int + x as int);
            assert(nums2[i] as int == nums1[i] as int + x as int);
        }
    }

    (nums1, nums2)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: if seed == 0 { 1 } else { seed } }
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

fn build_nums1(rng: &mut Rng, n: usize, x: i32) -> Vec<i32> {
    // We need 0 <= nums1[i] + x <= 1000 and 0 <= nums1[i] <= 1000.
    // So nums1[i] in [max(0, -x), min(1000, 1000 - x)].
    let lo = if x < 0 { -x } else { 0 };
    let hi = if x > 0 { 1000 - x } else { 1000 };
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_range_i32(lo, hi));
    }
    v
}

fn pick_mode(rng: &mut Rng, mode: usize) -> (usize, i32, Vec<i32>) {
    let (n, x) = match mode {
        0 => (1usize, 0i32),
        1 => (1, rng.gen_range_i32(-1000, 1000)),
        2 => (100, 0),
        3 => (100, rng.gen_range_i32(-1000, 1000)),
        4 => (rng.gen_range_usize(1, 100), 1000),
        5 => (rng.gen_range_usize(1, 100), -1000),
        6 => (rng.gen_range_usize(1, 100), 1),
        7 => (rng.gen_range_usize(1, 100), -1),
        8 => (2, rng.gen_range_i32(-500, 500)),
        9 => (50, rng.gen_range_i32(-500, 500)),
        _ => (rng.gen_range_usize(1, 100), rng.gen_range_i32(-1000, 1000)),
    };
    let nums1 = build_nums1(rng, n, x);
    (n, x, nums1)
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 { print!(","); }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 { print!(","); }
        print!("{}", nums2[i]);
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
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (_n, x, nums1) = pick_mode(&mut rng, mode);
        let (out1, out2) = generate_test_case(nums1, x);
        print_json(&out1, &out2);
    }
}