use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn pascals_triangle(n: nat) -> Seq<i32>
        decreases n,
    {
        if n == 0 {
            seq![1]
        } else {
            let last = Self::pascals_triangle((n - 1) as nat);
            Seq::new(
                last.len() + 1,
                |i: int|
                    if i == 0 {
                        last[i]
                    } else if i == last.len() {
                        last[i - 1]
                    } else {
                        (last[i - 1] + last[i]) as i32
                    },
            )
        }
    }
}

pub fn generate_test_case(row_index: i32, bump: i32, noise: &Vec<i32>) -> (out: i32)
    requires
        0 <= row_index <= 33,
        bump == 0,
    ensures
        0 <= out <= 33,
{
    let mut i: usize = 0;
    while i < noise.len()
        invariant
            i <= noise.len(),
            0 <= row_index <= 33,
            bump == 0,
        decreases noise.len() - i,
    {
        i = i + 1;
    }
    let outv = row_index + bump;
    assert(outv == row_index);
    assert(0 <= outv <= 33);
    outv
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

    fn gen_range_u32(&mut self, lo: u32, hi: u32) -> u32 {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as u32
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn gen_next(last: &Vec<i32>) -> Vec<i32> {
    if last.is_empty() {
        return vec![1];
    }
    let mut row = Vec::with_capacity(last.len() + 1);
    row.push(1);
    let mut i = 1usize;
    while i < last.len() {
        row.push(last[i - 1] + last[i]);
        i += 1;
    }
    row.push(1);
    row
}

fn adversarial_row_index(rng: &mut Rng, mode: usize, t: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 33,
        5 => 32,
        6 => 16,
        7 => {
            let vals = [4i32, 5, 6, 7, 8, 9, 10];
            vals[t % vals.len()]
        }
        8 => {
            let vals = [11i32, 12, 13, 14, 15, 17, 18];
            vals[t % vals.len()]
        }
        9 => rng.gen_range_u32(0, 33) as i32,
        _ => {
            let vals = [19i32, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31];
            vals[t % vals.len()]
        }
    }
}

fn make_noise(rng: &mut Rng, mode: usize, row_index: i32) -> Vec<i32> {
    let len = match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 33,
        5 => 34,
        6 => 64,
        7 => 7,
        8 => 8,
        9 => rng.gen_range_usize(0, 40),
        _ => 16,
    };
    let mut v = Vec::with_capacity(len);
    let mut i = 0usize;
    while i < len {
        let x = match mode {
            0 => 0,
            1 => row_index,
            2 => -(i as i32),
            3 => i as i32,
            4 => 33 - i as i32,
            5 => if i % 2 == 0 { 1_000_000_000 } else { -1_000_000_000 },
            6 => ((rng.next_u64() >> 32) as i32).wrapping_add(row_index),
            7 => 1,
            8 => -1,
            9 => (rng.gen_range_u32(0, 1000) as i32) - 500,
            _ => (i as i32) * (i as i32) - row_index,
        };
        v.push(x);
        i += 1;
    }
    v
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
        let raw = adversarial_row_index(&mut rng, mode, t);
        let noise = make_noise(&mut rng, mode, raw);
        let row_index = generate_test_case(raw, 0, &noise);
        println!("{{\"row_index\":{}}}", row_index);
    }
}