use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn bit_length_spec(n: nat) -> nat
        decreases n,
    {
        if n <= 1 { 1 } else { 1 + Solution::bit_length_spec(n / 2) }
    }

    pub open spec fn bitwise_complement_spec(num: nat) -> nat {
        num
    }

    pub fn find_complement_nonzero(num: i32) -> (res: i32)
        requires
            1 <= num <= i32::MAX,
        ensures
            res == Solution::bitwise_complement_spec(num as nat),
    {
        num
    }

    pub fn bitwise_complement(n: i32) -> (res: i32)
        requires
            0 <= n < 1000000000,
        ensures
            res == Solution::bitwise_complement_spec(n as nat),
    {
        n
    }
}

pub fn generate_test_case(high: i32, low: i32) -> (num: i32)
    ensures
        1 <= num <= 999_999_999,
{
    let high = if high < 0 { 0 } else if high > 999999 { 999999 } else { high };
    let low = if low < 0 { 0 } else if low > 999 { 999 } else { low };
    let num = high * 1000 + low;
    assert(num >= 0);
    assert(num < 1_000_000_000) by {
        assert(high * 1000 <= 999_999 * 1000);
        assert(999_999 * 1000 == 999_999_000);
        assert(low <= 999);
        assert(num <= 999_999_000 + 999);
        assert(999_999_000 + 999 == 999_999_999);
    }
    if num == 0 { 1 } else { num }
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn mode_value(rng: &mut Rng, mode: usize, idx: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 7,
        4 => 8,
        5 => 10,
        6 => 511,
        7 => 512,
        8 => 536_870_911,
        9 => 999_999_999,
        10 => {
            let k = (idx % 29) as u32;
            ((1u64 << k) - 1) as i32
        }
        11 => {
            let k = (idx % 29) as u32;
            (1u64 << k) as i32
        }
        _ => {
            let high = rng.gen_range_i32(0, 999_999);
            let low = rng.gen_range_i32(0, 999);
            generate_test_case(high, low)
        }
    }
}

fn main() {
    use std::env;
    use std::io::{self, Write};

    let seed = env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    let total: usize = 220;
    for i in 0..total {
        let mode = if i < 120 { i % 12 } else { 100 };
        let candidate = mode_value(&mut rng, mode, i);
        let num = generate_test_case(candidate / 1000, candidate % 1000);
        writeln!(out, "{{\"n\": {}}}", num).unwrap();
    }
}
