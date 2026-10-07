use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn tribo_spec(n: nat) -> nat
        decreases n
    {
        if n <= 0 {
            0
        } else if n == 1 {
            1
        } else if n == 2 {
            1
        } else {
            Solution::tribo_spec((n - 3) as nat)
                + Solution::tribo_spec((n - 2) as nat)
                + Solution::tribo_spec((n - 1) as nat)
        }
    }
}

pub fn generate_test_case(n: i32) -> (out: i32)
    requires
        0 <= n <= 37,
        Solution::tribo_spec(n as nat) <= i32::MAX,
    ensures
        out == n,
        0 <= out <= 37,
        Solution::tribo_spec(out as nat) <= i32::MAX,
{
    n
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
        let span = (hi - lo) as u64 + 1;
        lo + (self.next_u64() % span) as u32
    }
}

fn tribonacci_i32(n: i32) -> i32 {
    if n == 0 {
        return 0;
    }
    if n == 1 || n == 2 {
        return 1;
    }
    let mut a: i32 = 0;
    let mut b: i32 = 1;
    let mut c: i32 = 1;
    let mut i: i32 = 3;
    while i <= n {
        let next_i64 = a as i64 + b as i64 + c as i64;
        let next = next_i64 as i32;
        a = b;
        b = c;
        c = next;
        i += 1;
    }
    c
}

fn choose_adversarial_n(rng: &mut Rng, mode: usize, idx: usize) -> i32 {
    match mode {
        0 => 0,
        1 => 1,
        2 => 2,
        3 => 3,
        4 => 4,
        5 => 25,
        6 => 37,
        7 => {
            let vals = [35, 36, 37];
            vals[idx % vals.len()]
        }
        8 => {
            let vals = [0, 37, 1, 36, 2, 35, 3, 34];
            vals[idx % vals.len()]
        }
        9 => rng.gen_range_u32(0, 37) as i32,
        _ => {
            let vals = [5, 6, 7, 8, 9, 10, 11, 12, 13, 14];
            vals[idx % vals.len()]
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
    let total: usize = 200;
    let modes: usize = 11;

    for i in 0..total {
        let mode = i % modes;
        let raw_n = choose_adversarial_n(&mut rng, mode, i);
        let n = generate_test_case(raw_n);
        let _expected = tribonacci_i32(n);
        println!("{{\"n\":{}}}", n);
    }
}