use vstd::prelude::*;

verus! {

pub struct Solution;

pub fn generate_test_case(
    len1: usize,
    len2: usize,
    len3: usize,
    v1: i32,
    v2: i32,
    v3: i32,
    special1: i32,
    special2: i32,
    days: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= v1 <= 500,
        1 <= v2 <= 500,
        1 <= v3 <= 500,
        1 <= special1 <= 500,
        1 <= special2 <= 500,
        len1 + len2 + len3 + 2 <= 50_000,
        1 <= days <= len1 + len2 + len3 + 2,
    ensures
        1 <= res.1 <= res.0.len() <= 50_000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 500,
{
    let total_len: usize = len1 + len2 + len3 + 2;
    let mut weights: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < len1
        invariant
            0 <= i <= len1,
            weights.len() == i,
            total_len == len1 + len2 + len3 + 2,
            total_len <= 50_000,
            1 <= v1 <= 500,
            1 <= v2 <= 500,
            1 <= v3 <= 500,
            1 <= special1 <= 500,
            1 <= special2 <= 500,
            1 <= days <= total_len,
            forall |k: int| 0 <= k < weights.len() ==> #[trigger] weights[k] == v1,
        decreases len1 - i,
    {
        weights.push(v1);
        i = i + 1;
    }

    weights.push(special1);

    let mut j: usize = 0;
    while j < len2
        invariant
            0 <= j <= len2,
            weights.len() == len1 + 1 + j,
            total_len == len1 + len2 + len3 + 2,
            total_len <= 50_000,
            1 <= v1 <= 500,
            1 <= v2 <= 500,
            1 <= v3 <= 500,
            1 <= special1 <= 500,
            1 <= special2 <= 500,
            1 <= days <= total_len,
            forall |k: int| 0 <= k < len1 ==> #[trigger] weights[k] == v1,
            weights[len1 as int] == special1,
            forall |k: int| len1 as int + 1 <= k < weights.len() ==> #[trigger] weights[k] == v2,
        decreases len2 - j,
    {
        weights.push(v2);
        j = j + 1;
    }

    weights.push(special2);

    let mut k: usize = 0;
    while k < len3
        invariant
            0 <= k <= len3,
            weights.len() == len1 + 1 + len2 + 1 + k,
            total_len == len1 + len2 + len3 + 2,
            total_len <= 50_000,
            1 <= v1 <= 500,
            1 <= v2 <= 500,
            1 <= v3 <= 500,
            1 <= special1 <= 500,
            1 <= special2 <= 500,
            1 <= days <= total_len,
            forall |x: int| 0 <= x < len1 ==> #[trigger] weights[x] == v1,
            weights[len1 as int] == special1,
            forall |x: int| len1 as int + 1 <= x < len1 as int + 1 + len2 as int ==> #[trigger] weights[x] == v2,
            weights[len1 as int + 1 + len2 as int] == special2,
            forall |x: int| len1 as int + 1 + len2 as int + 1 <= x < weights.len() ==> #[trigger] weights[x] == v3,
        decreases len3 - k,
    {
        weights.push(v3);
        k = k + 1;
    }

    assert(weights.len() == total_len);
    assert(1 <= days <= weights.len());

    proof {
        assert forall |idx: int| 0 <= idx < weights.len() implies 1 <= #[trigger] weights[idx] <= 500 by {
            if idx < len1 as int {
                assert(weights[idx] == v1);
                assert(1 <= v1 <= 500);
            } else if idx == len1 as int {
                assert(weights[idx] == special1);
                assert(1 <= special1 <= 500);
            } else if idx < len1 as int + 1 + len2 as int {
                assert(weights[idx] == v2);
                assert(1 <= v2 <= 500);
            } else if idx == len1 as int + 1 + len2 as int {
                assert(weights[idx] == special2);
                assert(1 <= special2 <= 500);
            } else {
                assert(weights[idx] == v3);
                assert(1 <= v3 <= 500);
            }
        };
    }

    (weights, days)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
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
        lo + (self.next_u64() % span) as i32
    }
}

fn mode_case(rng: &mut Rng, mode: usize, idx: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            let n = 2 + (idx % 8);
            let len1 = 0;
            let len2 = n - 2;
            let len3 = 0;
            generate_test_case(len1, len2, len3, 1, 2, 3, 1, 1, n as i32)
        }
        1 => {
            let n = 50_000usize;
            let len1 = 20_000usize;
            let len2 = 9_998usize;
            let len3 = n - len1 - len2 - 2;
            generate_test_case(len1, len2, len3, 500, 500, 500, 500, 500, 1)
        }
        2 => {
            let n = 50_000usize;
            let len1 = 10_000usize;
            let len2 = 10_000usize;
            let len3 = n - len1 - len2 - 2;
            generate_test_case(len1, len2, len3, 1, 1, 1, 1, 1, n as i32)
        }
        3 => {
            let n = rng.gen_range_usize(2, 300);
            let len1 = n / 3;
            let len2 = n / 3;
            let len3 = n - len1 - len2 - 2;
            let days = rng.gen_range_i32(1, n as i32);
            generate_test_case(len1, len2, len3, 17, 233, 499, 500, 1, days)
        }
        4 => {
            let n = rng.gen_range_usize(2, 2000);
            let len1 = n - 2;
            generate_test_case(len1, 0, 0, 499, 1, 1, 500, 499, rng.gen_range_i32(1, n as i32))
        }
        5 => {
            let n = rng.gen_range_usize(2, 2000);
            let len3 = n - 2;
            generate_test_case(0, 0, len3, 1, 1, 2, 500, 500, rng.gen_range_i32(1, n as i32))
        }
        6 => {
            let n = rng.gen_range_usize(2, 5000);
            let len1 = rng.gen_range_usize(0, n - 2);
            let rem = n - 2 - len1;
            let len2 = rng.gen_range_usize(0, rem);
            let len3 = rem - len2;
            generate_test_case(len1, len2, len3, 7, 250, 13, 500, 500, 1)
        }
        7 => {
            let n = rng.gen_range_usize(2, 5000);
            let len1 = rng.gen_range_usize(0, n - 2);
            let rem = n - 2 - len1;
            let len2 = rng.gen_range_usize(0, rem);
            let len3 = rem - len2;
            generate_test_case(len1, len2, len3, 123, 321, 111, 500, 500, 2)
        }
        8 => {
            let n = rng.gen_range_usize(2, 10_000);
            let len1 = rng.gen_range_usize(0, n - 2);
            let rem = n - 2 - len1;
            let len2 = rng.gen_range_usize(0, rem);
            let len3 = rem - len2;
            let mut days = (n as i32) / 2;
            if days < 1 {
                days = 1;
            }
            generate_test_case(len1, len2, len3, 1, 500, 1, 1, 500, days)
        }
        _ => {
            let n = rng.gen_range_usize(2, 50_000);
            let len1 = rng.gen_range_usize(0, n - 2);
            let rem = n - 2 - len1;
            let len2 = rng.gen_range_usize(0, rem);
            let len3 = rem - len2;
            let special1 = if idx % 2 == 0 { 1 } else { 500 };
            let special2 = if idx % 3 == 0 { 500 } else { 1 };
            let days = rng.gen_range_i32(1, n as i32);
            let v1 = rng.gen_range_i32(1, 500);
            let v2 = rng.gen_range_i32(1, 500);
            let v3 = rng.gen_range_i32(1, 500);
            generate_test_case(len1, len2, len3, v1, v2, v3, special1, special2, days)
        }
    }
}

fn print_json(weights: &[i32], days: i32) {
    print!("{{\"weights\":[");
    for (i, w) in weights.iter().enumerate() {
        if i > 0 {
            print!(",");
        }
        print!("{}", w);
    }
    println!("],\"days\":{}}}", days);
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

    for i in 0..total {
        let mode = if i < 100 { i % 10 } else { (rng.next_u64() as usize) % 10 };
        let (weights, days) = mode_case(&mut rng, mode, i);
        print_json(&weights, days);
    }
}