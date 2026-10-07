use vstd::prelude::*;

verus! {

pub struct TestCase {
    pub arr: Vec<i32>,
    pub left: i32,
    pub right: i32,
    pub threshold: i32,
}

pub struct Solution;

impl Solution {
    pub open spec fn count_occurrences(arr: Seq<i32>, left: int, right: int, val: i32) -> int
        decreases right - left + 1
    {
        if left > right {
            0
        } else if arr[left] == val {
            1 + Self::count_occurrences(arr, left + 1, right, val)
        } else {
            Self::count_occurrences(arr, left + 1, right, val)
        }
    }
}

proof fn count_non_negative(arr: Seq<i32>, left: int, right: int, val: i32)
    ensures
        Solution::count_occurrences(arr, left, right, val) >= 0,
    decreases right - left + 1,
{
    if left > right {
    } else {
        count_non_negative(arr, left + 1, right, val);
    }
}

proof fn count_lower_bound(arr: Seq<i32>, left: int, right: int, val: i32, threshold: int)
    requires
        threshold >= 0,
        left + threshold <= right + 1,
        forall |j: int| left <= j < left + threshold ==> arr[j] == val,
    ensures
        Solution::count_occurrences(arr, left, right, val) >= threshold,
    decreases right - left + 1,
{
    if left > right {
    } else if threshold <= 0 {
        count_non_negative(arr, left, right, val);
    } else {
        assert(arr[left] == val);
        count_lower_bound(arr, left + 1, right, val, threshold - 1);
    }
}

pub fn generate_test_case(
    n: usize,
    major_val: i32,
    filler_val: i32,
    left: usize,
    right: usize,
    threshold: usize,
) -> (tc: TestCase)
    requires
        1 <= n <= 20_000,
        1 <= major_val <= 20_000,
        1 <= filler_val <= 20_000,
        major_val != filler_val,
        left <= right < n,
        1 <= threshold <= right - left + 1,
        2 * threshold > right - left + 1,
    ensures
        tc.arr.len() == n,
        tc.arr@.len() == n as int,
        tc.left == left as i32,
        tc.right == right as i32,
        tc.threshold == threshold as i32,
        1 <= tc.arr.len() <= 20_000,
        forall |i: int| 0 <= i < tc.arr@.len() ==> 1 <= #[trigger] tc.arr@[i] <= 20_000,
        0 <= tc.left <= tc.right,
        tc.right < tc.arr.len() as i32,
        tc.threshold >= 1,
        tc.threshold <= tc.right - tc.left + 1,
        2 * tc.threshold > tc.right - tc.left + 1,
        Solution::count_occurrences(tc.arr@, tc.left as int, tc.right as int, major_val) >= tc.threshold as int,
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            1 <= n <= 20_000,
            1 <= major_val <= 20_000,
            1 <= filler_val <= 20_000,
            left <= right < n,
            1 <= threshold <= right - left + 1,
            2 * threshold > right - left + 1,
            0 <= i <= n,
            arr.len() == i,
            forall |j: int| 0 <= j < arr@.len() ==> 1 <= #[trigger] arr@[j] <= 20_000,
            forall |j: int| 0 <= j < i as int && (left as int) <= j && j < (left as int) + (threshold as int) ==> #[trigger] arr@[j] == major_val,
            forall |j: int| 0 <= j < i as int && !((left as int) <= j && j < (left as int) + (threshold as int)) ==> #[trigger] arr@[j] == filler_val,
        decreases n - i,
    {
        if left <= i && i < left + threshold {
            arr.push(major_val);
        } else {
            arr.push(filler_val);
        }
        i = i + 1;
    }

    proof {
        assert(arr.len() == n);
        assert forall |j: int| 0 <= j < arr@.len() implies 1 <= #[trigger] arr@[j] <= 20_000 by {
        };

        assert(left + threshold <= right + 1);
        assert(left as int + threshold as int <= right as int + 1);

        assert forall |j: int| left as int <= j < left as int + threshold as int implies #[trigger] arr@[j] == major_val by {
        };

        count_lower_bound(arr@, left as int, right as int, major_val, threshold as int);
    }

    TestCase {
        arr,
        left: left as i32,
        right: right as i32,
        threshold: threshold as i32,
    }
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
        self.state = self
            .state
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

fn choose_threshold(len: usize, rng: &mut Rng) -> usize {
    let lo = len / 2 + 1;
    rng.gen_range_usize(lo, len)
}

fn mode_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, usize, usize, i32, i32) {
    match mode {
        0 => {
            let n = 1;
            let left = 0;
            let right = 0;
            let threshold = 1;
            let major = 1;
            let filler = 2;
            (n, left, right, threshold, major, filler)
        }
        1 => {
            let n = 20_000;
            let left = 0;
            let right = n - 1;
            let threshold = 10_001;
            let major = 20_000;
            let filler = 1;
            (n, left, right, threshold, major, filler)
        }
        2 => {
            let n = 64;
            let left = 0;
            let right = 31;
            let threshold = 17;
            let major = 7;
            let filler = 8;
            (n, left, right, threshold, major, filler)
        }
        3 => {
            let n = 64;
            let left = 32;
            let right = 63;
            let threshold = 17;
            let major = 9;
            let filler = 10;
            (n, left, right, threshold, major, filler)
        }
        4 => {
            let n = 127;
            let left = 13;
            let right = 13;
            let threshold = 1;
            let major = 123;
            let filler = 456;
            (n, left, right, threshold, major, filler)
        }
        5 => {
            let n = 257;
            let left = 100;
            let right = 200;
            let len = right - left + 1;
            let threshold = len / 2 + 1;
            let major = 111;
            let filler = 112;
            (n, left, right, threshold, major, filler)
        }
        6 => {
            let n = 300;
            let left = 50;
            let right = 249;
            let threshold = right - left + 1;
            let major = 19_999;
            let filler = 20_000;
            (n, left, right, threshold, major, filler)
        }
        7 => {
            let n = 99;
            let left = 20;
            let right = 78;
            let threshold = 30;
            let major = 5;
            let filler = 5;
            (n, left, right, threshold, major, filler)
        }
        8 => {
            let n = 512;
            let left = 1;
            let right = 510;
            let len = right - left + 1;
            let threshold = len;
            let major = 314;
            let filler = 2718;
            (n, left, right, threshold, major, filler)
        }
        9 => {
            let n = 777;
            let left = 123;
            let right = 456;
            let len = right - left + 1;
            let threshold = choose_threshold(len, rng);
            let major = 1 + (t as i32 % 20_000);
            let filler = 20_000 - (t as i32 % 20_000);
            (n, left, right, threshold, major, filler)
        }
        _ => {
            let n = rng.gen_range_usize(1, 20_000);
            let left = rng.gen_range_usize(0, n - 1);
            let right = rng.gen_range_usize(left, n - 1);
            let len = right - left + 1;
            let threshold = choose_threshold(len, rng);
            let major = rng.gen_range_i32(1, 20_000);
            let filler = rng.gen_range_i32(1, 20_000);
            (n, left, right, threshold, major, filler)
        }
    }
}

fn print_json(arr: &[i32], left: i32, right: i32, threshold: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr[i]);
    }
    println!("],\"left\":{},\"right\":{},\"threshold\":{}}}", left, right, threshold);
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
        let (n, left, right, threshold, major_val, filler_val) = mode_params(&mut rng, mode, t);
        let tc = generate_test_case(n, major_val, filler_val, left, right, threshold);
        print_json(&tc.arr, tc.left, tc.right, tc.threshold);
    }
}