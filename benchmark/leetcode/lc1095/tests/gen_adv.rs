use vstd::prelude::*;

verus! {

pub struct MountainArray {
    pub data: Vec<i32>,
}

impl MountainArray {
    pub fn get(&self, index: i32) -> (result: i32)
        requires
            0 <= index < self.data.len(),
        ensures
            result == self.data@[index as int],
    {
        self.data[index as usize]
    }

    pub fn length(&self) -> (result: i32)
        requires
            self.data@.len() <= 10_000,
        ensures
            result as int == self.data@.len(),
    {
        self.data.len() as i32
    }
}

pub struct TestCase {
    pub mountain_arr: MountainArray,
    pub target: i32,
}

pub struct Solution;

impl Solution {
    pub open spec fn is_mountain(s: Seq<i32>, peak: int) -> bool {
        s.len() >= 3
        && 0 < peak < s.len() - 1
        && (forall |a: int, b: int| 0 <= a < b <= peak ==> s[a] < s[b])
        && (forall |a: int, b: int| peak <= a < b < s.len() ==> s[a] > s[b])
    }
}

pub fn generate_test_case(
    left: &Vec<i32>,
    peak_val: i32,
    right: &Vec<i32>,
    target: i32,
) -> (tc: TestCase)
    requires
        1 <= left.len(),
        1 <= right.len(),
        left.len() + right.len() + 1 <= 10_000,
        0 <= target <= 1_000_000_000,
        0 <= peak_val <= 1_000_000_000,
        forall|i: int| 0 <= i < left.len() ==> 0 <= #[trigger] left[i] < peak_val,
        forall|i: int, j: int| 0 <= i < j < left.len() ==> #[trigger] left[i] < #[trigger] left[j],
        forall|i: int| 0 <= i < right.len() ==> 0 <= #[trigger] right[i] < peak_val,
        forall|i: int, j: int| 0 <= i < j < right.len() ==> #[trigger] right[i] > #[trigger] right[j],
    ensures
        3 <= tc.mountain_arr.data.len() <= 10_000,
        forall |i: int| 0 <= i < tc.mountain_arr.data.len() ==> 0 <= #[trigger] tc.mountain_arr.data@[i] <= 1_000_000_000,
        0 <= tc.target <= 1_000_000_000,
        exists |peak: int| Solution::is_mountain(tc.mountain_arr.data@, peak),
{
    let n: usize = left.len() + 1 + right.len();
    let peak_idx: usize = left.len();
    let mut data: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < left.len()
        invariant
            n == left.len() + 1 + right.len(),
            peak_idx == left.len(),
            1 <= left.len(),
            1 <= right.len(),
            n <= 10_000,
            0 <= i <= left.len(),
            data.len() == i,
            0 <= target <= 1_000_000_000,
            0 <= peak_val <= 1_000_000_000,
            forall|k: int| 0 <= k < left.len() ==> 0 <= #[trigger] left[k] < peak_val,
            forall|a: int, b: int| 0 <= a < b < left.len() ==> #[trigger] left[a] < #[trigger] left[b],
            forall|k: int| 0 <= k < right.len() ==> 0 <= #[trigger] right[k] < peak_val,
            forall|a: int, b: int| 0 <= a < b < right.len() ==> #[trigger] right[a] > #[trigger] right[b],
            forall|k: int| 0 <= k < i as int ==> #[trigger] data@[k] == left[k],
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] data@[k] < peak_val,
        decreases left.len() - i,
    {
        data.push(left[i]);
        i = i + 1;
    }

    data.push(peak_val);

    let mut j: usize = 0;
    while j < right.len()
        invariant
            n == left.len() + 1 + right.len(),
            peak_idx == left.len(),
            1 <= left.len(),
            1 <= right.len(),
            n <= 10_000,
            0 <= j <= right.len(),
            data.len() == left.len() + 1 + j,
            0 <= target <= 1_000_000_000,
            0 <= peak_val <= 1_000_000_000,
            forall|k: int| 0 <= k < left.len() ==> 0 <= #[trigger] left[k] < peak_val,
            forall|a: int, b: int| 0 <= a < b < left.len() ==> #[trigger] left[a] < #[trigger] left[b],
            forall|k: int| 0 <= k < right.len() ==> 0 <= #[trigger] right[k] < peak_val,
            forall|a: int, b: int| 0 <= a < b < right.len() ==> #[trigger] right[a] > #[trigger] right[b],
            data@[peak_idx as int] == peak_val,
            forall|k: int| 0 <= k < left.len() ==> #[trigger] data@[k] == left[k],
            forall|k: int| 0 <= k < j as int ==> #[trigger] data@[peak_idx as int + 1 + k] == right[k],
            forall|k: int| 0 <= k < data.len() ==> 0 <= #[trigger] data@[k] <= 1_000_000_000,
        decreases right.len() - j,
    {
        data.push(right[j]);
        j = j + 1;
    }

    proof {
        assert(data.len() == n);
        assert(3 <= data.len()) by {
            assert(left.len() >= 1);
            assert(right.len() >= 1);
        };
        assert(data@.len() == n as int);
        assert(peak_idx as int == left.len() as int);
        assert(0 < peak_idx as int) by {
            assert(left.len() >= 1);
        };
        assert((peak_idx as int) < (data@.len() - 1)) by {
            assert(data@.len() == left.len() as int + 1 + right.len() as int);
            assert(right.len() >= 1);
        };

        assert forall |k: int| 0 <= k < data@.len() implies 0 <= #[trigger] data@[k] <= 1_000_000_000 by {
            if k < peak_idx as int {
                assert(data@[k] == left[k]);
                assert(0 <= left[k] < peak_val);
            } else if k == peak_idx as int {
                assert(data@[k] == peak_val);
                assert(0 <= peak_val <= 1_000_000_000);
            } else {
                let r = k - peak_idx as int - 1;
                assert(0 <= r < right.len());
                assert(k == peak_idx as int + 1 + r);
                assert(data@[peak_idx as int + 1 + r] == right[r]);
                assert(data@[k] == right[r]);
                assert(0 <= right[r] < peak_val);
            }
        };

        assert forall |a: int, b: int| 0 <= a < b <= peak_idx as int implies data@[a] < data@[b] by {
            if b < peak_idx as int {
                assert(data@[a] == left[a]);
                assert(data@[b] == left[b]);
                assert(left[a] < left[b]);
            } else {
                assert(b == peak_idx as int);
                assert(data@[a] == left[a]);
                assert(data@[b] == peak_val);
                assert(left[a] < peak_val);
            }
        };

        assert forall |a: int, b: int| peak_idx as int <= a < b < data@.len() implies data@[a] > data@[b] by {
            if a == peak_idx as int {
                let rb = b - peak_idx as int - 1;
                assert(0 <= rb < right.len());
                assert(data@[a] == peak_val);
                assert(b == peak_idx as int + 1 + rb);
                assert(data@[peak_idx as int + 1 + rb] == right[rb]);
                assert(data@[b] == right[rb]);
                assert(right[rb] < peak_val);
            } else {
                let ra = a - peak_idx as int - 1;
                let rb = b - peak_idx as int - 1;
                assert(0 <= ra < rb < right.len());
                assert(a == peak_idx as int + 1 + ra);
                assert(b == peak_idx as int + 1 + rb);
                assert(data@[peak_idx as int + 1 + ra] == right[ra]);
                assert(data@[peak_idx as int + 1 + rb] == right[rb]);
                assert(data@[a] == right[ra]);
                assert(data@[b] == right[rb]);
                assert(right[ra] > right[rb]);
            }
        };

        assert(Solution::is_mountain(data@, peak_idx as int));
    }

    TestCase {
        mountain_arr: MountainArray { data },
        target,
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

fn build_case(mode: usize, rng: &mut Rng) -> (Vec<i32>, i32, Vec<i32>, i32) {
    let total_len = match mode {
        0 => 3,
        1 => 4,
        2 => 5,
        3 => 7,
        4 => 15,
        5 => 31,
        6 => 127,
        7 => 9999,
        8 => 10000,
        9 => 257,
        _ => rng.gen_range_usize(3, 10000),
    };

    let peak_idx = match mode {
        0 => 1,
        1 => 1,
        2 => total_len - 2,
        3 => total_len / 2,
        4 => 1,
        5 => total_len - 2,
        6 => total_len / 2,
        7 => 1,
        8 => total_len - 2,
        9 => total_len / 2,
        _ => rng.gen_range_usize(1, total_len - 2),
    };

    let left_len = peak_idx;
    let right_len = total_len - peak_idx - 1;

    let peak_val = match mode {
        0 => 2,
        1 => 1_000_000_000,
        2 => 1_000_000_000,
        3 => 10,
        4 => 1_000_000_000,
        5 => 1_000_000_000,
        6 => (total_len as i32) + 100,
        7 => 1_000_000_000,
        8 => 1_000_000_000,
        9 => 500_000_000,
        _ => {
            let min_peak = (left_len.max(right_len) + 1) as i32;
            let slack = 1_000_000_000 - min_peak;
            min_peak + (rng.next_u64() % (slack as u64 + 1)) as i32
        }
    };

    let mut left = Vec::with_capacity(left_len);
    let mut i = 0usize;
    while i < left_len {
        let v = match mode {
            0 => (i as i32),
            1 => peak_val - left_len as i32 + i as i32,
            2 => (i as i32),
            3 => (i as i32) + 1,
            4 => peak_val - left_len as i32 + i as i32,
            5 => (i as i32),
            6 => (i as i32),
            7 => peak_val - left_len as i32 + i as i32,
            8 => (i as i32),
            9 => peak_val - left_len as i32 + i as i32,
            _ => {
                if left_len == 0 {
                    0
                } else {
                    let start_max = peak_val - left_len as i32;
                    let start = if start_max > 0 {
                        rng.gen_range_i32(0, start_max)
                    } else {
                        0
                    };
                    start + i as i32
                }
            }
        };
        left.push(v);
        i += 1;
    }

    let mut right = Vec::with_capacity(right_len);
    let mut j = 0usize;
    while j < right_len {
        let v = match mode {
            0 => 0,
            1 => peak_val - 1 - j as i32,
            2 => peak_val - 1 - j as i32,
            3 => (right_len - j - 1) as i32,
            4 => peak_val - 1 - j as i32,
            5 => peak_val - 1 - j as i32,
            6 => (right_len - j - 1) as i32,
            7 => peak_val - 1 - j as i32,
            8 => (right_len - j - 1) as i32,
            9 => peak_val - 1 - j as i32,
            _ => (right_len - j - 1) as i32,
        };
        right.push(v);
        j += 1;
    }

    let target = match mode {
        0 => peak_val,
        1 => left[0],
        2 => right[right_len - 1],
        3 => left[left_len / 2],
        4 => right[0],
        5 => peak_val - 1,
        6 => 0,
        7 => 1_000_000_000,
        8 => peak_val,
        9 => 123456789,
        _ => {
            let choice = rng.gen_range_usize(0, 4);
            match choice {
                0 => peak_val,
                1 => left[rng.gen_range_usize(0, left_len - 1)],
                2 => right[rng.gen_range_usize(0, right_len - 1)],
                3 => 1_000_000_000,
                _ => 123456789,
            }
        }
    };

    (left, peak_val, right, target)
}

fn print_case(left: &[i32], peak: i32, right: &[i32], target: i32) {
    // Keys must match tests/reference_oracle.rs (MountainArray.data).
    print!("{{\"data\":[");
    let mut first = true;
    for &v in left {
        if !first {
            print!(",");
        }
        first = false;
        print!("{}", v);
    }
    if !first {
        print!(",");
    }
    print!("{}", peak);
    for &v in right {
        print!(",{}", v);
    }
    println!("],\"target\":{}}}", target);
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
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (left, peak, right, target) = build_case(mode, &mut rng);
        let _tc = generate_test_case(&left, peak, &right, target);
        print_case(&left, peak, &right, target);
    }
}