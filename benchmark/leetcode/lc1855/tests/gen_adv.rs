use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len1: usize,
    len2: usize,
    val1: i32,
    val2: i32,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= len1 <= 100_000,
        1 <= len2 <= 100_000,
        1 <= val1 <= 100_000,
        1 <= val2 <= 100_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall |k: int| 0 <= k < result.0.len() ==> 1 <= #[trigger] result.0[k] <= 100_000,
        forall |k: int| 0 <= k < result.1.len() ==> 1 <= #[trigger] result.1[k] <= 100_000,
        forall |a: int, b: int| 0 <= a < b < result.0.len() ==> (#[trigger] result.0[a]) >= (#[trigger] result.0[b]),
        forall |a: int, b: int| 0 <= a < b < result.1.len() ==> (#[trigger] result.1[a]) >= (#[trigger] result.1[b]),
{
    let mut nums1: Vec<i32> = Vec::new();
    let mut nums2: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < len1
        invariant
            0 <= i <= len1,
            nums1.len() == i,
            1 <= val1 <= 100_000,
            forall |k: int| 0 <= k < i ==> #[trigger] nums1[k] == val1,
        decreases len1 - i,
    {
        nums1.push(val1);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < len2
        invariant
            0 <= j <= len2,
            nums2.len() == j,
            1 <= val2 <= 100_000,
            forall |k: int| 0 <= k < j ==> #[trigger] nums2[k] == val2,
        decreases len2 - j,
    {
        nums2.push(val2);
        j = j + 1;
    }

    (nums1, nums2)
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

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, usize, i32, i32) {
    match mode {
        0 => (1, 1, 1, 1),
        1 => (1, 1, 100_000, 100_000),
        2 => (1, 1, 1, 100_000),
        3 => (1, 1, 100_000, 1),
        4 => {
            let n = rng.gen_range_usize(2, 20);
            let m = rng.gen_range_usize(2, 20);
            (n, m, 1, 100_000)
        }
        5 => {
            let n = rng.gen_range_usize(2, 20);
            let m = rng.gen_range_usize(2, 20);
            (n, m, 100_000, 1)
        }
        6 => {
            let n = rng.gen_range_usize(2, 100);
            let m = rng.gen_range_usize(2, 100);
            let v = rng.gen_range_i32(1, 100_000);
            (n, m, v, v)
        }
        7 => (100_000, 100_000, 1, 100_000),
        8 => (100_000, 1, 1, 100_000),
        9 => (1, 100_000, 100_000, 1),
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            let m = rng.gen_range_usize(1, 1000);
            let v1 = rng.gen_range_i32(1, 100_000);
            let v2 = rng.gen_range_i32(1, 100_000);
            (n, m, v1, v2)
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (len1, len2, v1, v2) = pick_params(&mut rng, mode);
        let (nums1, nums2) = generate_test_case(len1, len2, v1, v2);
        print_json(&nums1, &nums2);
    }
}