use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count_zeros(s: Seq<i32>, l: int, r: int) -> int
        recommends
            0 <= l <= r <= s.len(),
        decreases r - l,
    {
        if l >= r {
            0
        } else {
            (if s[l] == 0 { 1int } else { 0int }) + Self::count_zeros(s, l + 1, r)
        }
    }
}

pub fn generate_test_case(prefix: &Vec<i32>, middle: &Vec<i32>, suffix: &Vec<i32>, k: i32) -> (res: (Vec<i32>, i32))
    requires
        0 <= k,
        1 <= prefix.len() + middle.len() + suffix.len() <= 100_000,
        k <= prefix.len() + middle.len() + suffix.len(),
        forall|i: int| 0 <= i < prefix.len() ==> (#[trigger] prefix[i] == 0 || #[trigger] prefix[i] == 1),
        forall|i: int| 0 <= i < middle.len() ==> (#[trigger] middle[i] == 0 || #[trigger] middle[i] == 1),
        forall|i: int| 0 <= i < suffix.len() ==> (#[trigger] suffix[i] == 0 || #[trigger] suffix[i] == 1),
    ensures
        1 <= res.0.len() <= 100_000,
        res.1 == k,
        forall|i: int| 0 <= i < res.0.len() ==> (#[trigger] res.0[i] == 0 || #[trigger] res.0[i] == 1),
        0 <= res.1 <= res.0.len(),
{
    let total_len: usize = prefix.len() + middle.len() + suffix.len();
    let mut nums: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < prefix.len()
        invariant
            total_len == prefix.len() + middle.len() + suffix.len(),
            1 <= total_len <= 100_000,
            0 <= k <= total_len,
            0 <= i <= prefix.len(),
            nums.len() == i,
            forall|j: int| 0 <= j < prefix.len() ==> (#[trigger] prefix[j] == 0 || #[trigger] prefix[j] == 1),
            forall|j: int| 0 <= j < middle.len() ==> (#[trigger] middle[j] == 0 || #[trigger] middle[j] == 1),
            forall|j: int| 0 <= j < suffix.len() ==> (#[trigger] suffix[j] == 0 || #[trigger] suffix[j] == 1),
            forall|j: int| 0 <= j < nums.len() ==> (#[trigger] nums[j] == 0 || #[trigger] nums[j] == 1),
        decreases prefix.len() - i,
    {
        assert(prefix[i as int] == 0 || prefix[i as int] == 1);
        nums.push(prefix[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < middle.len()
        invariant
            total_len == prefix.len() + middle.len() + suffix.len(),
            1 <= total_len <= 100_000,
            0 <= k <= total_len,
            0 <= j <= middle.len(),
            nums.len() == prefix.len() + j,
            forall|x: int| 0 <= x < prefix.len() ==> (#[trigger] prefix[x] == 0 || #[trigger] prefix[x] == 1),
            forall|x: int| 0 <= x < middle.len() ==> (#[trigger] middle[x] == 0 || #[trigger] middle[x] == 1),
            forall|x: int| 0 <= x < suffix.len() ==> (#[trigger] suffix[x] == 0 || #[trigger] suffix[x] == 1),
            forall|x: int| 0 <= x < nums.len() ==> (#[trigger] nums[x] == 0 || #[trigger] nums[x] == 1),
        decreases middle.len() - j,
    {
        assert(middle[j as int] == 0 || middle[j as int] == 1);
        nums.push(middle[j]);
        j = j + 1;
    }

    let mut t: usize = 0;
    while t < suffix.len()
        invariant
            total_len == prefix.len() + middle.len() + suffix.len(),
            1 <= total_len <= 100_000,
            0 <= k <= total_len,
            0 <= t <= suffix.len(),
            nums.len() == prefix.len() + middle.len() + t,
            forall|x: int| 0 <= x < prefix.len() ==> (#[trigger] prefix[x] == 0 || #[trigger] prefix[x] == 1),
            forall|x: int| 0 <= x < middle.len() ==> (#[trigger] middle[x] == 0 || #[trigger] middle[x] == 1),
            forall|x: int| 0 <= x < suffix.len() ==> (#[trigger] suffix[x] == 0 || #[trigger] suffix[x] == 1),
            forall|x: int| 0 <= x < nums.len() ==> (#[trigger] nums[x] == 0 || #[trigger] nums[x] == 1),
        decreases suffix.len() - t,
    {
        assert(suffix[t as int] == 0 || suffix[t as int] == 1);
        nums.push(suffix[t]);
        t = t + 1;
    }

    assert(nums.len() == total_len);
    assert(1 <= nums.len());
    assert(nums.len() <= 100_000);
    (nums, k)
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

    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() & 1) as i32
    }
}

fn make_vec(len: usize, val: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(val);
    }
    v
}

fn make_alternating(len: usize, start: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push(if i % 2 == 0 { start } else { 1 - start });
    }
    v
}

fn make_random_bits(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_bit());
    }
    v
}

fn make_blocky(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    let mut cur = rng.gen_bit();
    while v.len() < len {
        let rem = len - v.len();
        let block = 1 + (rng.next_u64() as usize % rem.min(17));
        for _ in 0..block {
            if v.len() == len {
                break;
            }
            v.push(cur);
        }
        cur = 1 - cur;
    }
    v
}

fn split_total(rng: &mut Rng, total: usize) -> (usize, usize, usize) {
    let a = rng.gen_range_usize(0, total);
    let b = rng.gen_range_usize(0, total - a);
    let c = total - a - b;
    (a, b, c)
}

fn json_print_case(nums: &Vec<i32>, k: i32) {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    write!(out, "{{\"nums\":[").unwrap();
    for i in 0..nums.len() {
        if i > 0 {
            write!(out, ",").unwrap();
        }
        write!(out, "{}", nums[i]).unwrap();
    }
    writeln!(out, "],\"k\":{}}}", k).unwrap();
}

fn build_case(rng: &mut Rng, mode: usize, idx: usize) -> (Vec<i32>, i32) {
    let total = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 10,
        4 => 31,
        5 => 64,
        6 => 127,
        7 => 999,
        8 => 4096,
        _ => {
            if idx % 20 == 0 {
                100_000
            } else {
                rng.gen_range_usize(1, 2000)
            }
        }
    };

    let (lp, lm, ls) = split_total(rng, total);

    let (prefix, middle, suffix, k) = match mode {
        0 => (make_vec(lp, 0), make_vec(lm, 0), make_vec(ls, 0), 0),
        1 => (make_vec(lp, 1), make_vec(lm, 1), make_vec(ls, 1), total as i32),
        2 => (
            make_alternating(lp, 0),
            make_alternating(lm, 1),
            make_alternating(ls, 0),
            (total / 2) as i32,
        ),
        3 => (
            make_vec(lp, 1),
            make_vec(lm, 0),
            make_vec(ls, 1),
            lm.min(total) as i32,
        ),
        4 => (
            make_vec(lp, 0),
            make_vec(lm, 1),
            make_vec(ls, 0),
            rng.gen_range_usize(0, total) as i32,
        ),
        5 => (
            make_random_bits(rng, lp),
            make_random_bits(rng, lm),
            make_random_bits(rng, ls),
            0,
        ),
        6 => (
            make_random_bits(rng, lp),
            make_random_bits(rng, lm),
            make_random_bits(rng, ls),
            total as i32,
        ),
        7 => (
            make_blocky(rng, lp),
            make_blocky(rng, lm),
            make_blocky(rng, ls),
            (total / 3) as i32,
        ),
        8 => {
            let mut p = make_vec(lp, 1);
            let mut m = make_vec(lm, 1);
            let mut s = make_vec(ls, 1);
            if !p.is_empty() {
                let mid = p.len() / 2;
                p[mid] = 0;
            }
            if !m.is_empty() {
                let mid = m.len() / 2;
                m[mid] = 0;
            }
            if !s.is_empty() {
                let mid = s.len() / 2;
                s[mid] = 0;
            }
            (p, m, s, 1)
        }
        _ => (
            make_random_bits(rng, lp),
            make_blocky(rng, lm),
            make_alternating(ls, (rng.next_u64() & 1) as i32),
            rng.gen_range_usize(0, total) as i32,
        ),
    };

    generate_test_case(&prefix, &middle, &suffix, k)
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total_cases = 200usize;

    for i in 0..total_cases {
        let mode = if i < 100 {
            i % 10
        } else {
            rng.gen_range_usize(0, 9)
        };
        let (nums, k) = build_case(&mut rng, mode, i);
        json_print_case(&nums, k);
    }
}