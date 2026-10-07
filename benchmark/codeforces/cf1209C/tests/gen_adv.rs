use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    digits: Vec<i32>,
) -> (res: Vec<i32>)
    requires
        1 <= digits.len() <= 200_000,
        forall|i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
    ensures
        1 <= res.len() <= 200_000,
        forall|i: int| 0 <= i < res.len() ==> 0 <= #[trigger] res[i] <= 9,
        res@ == digits@,
{
    digits
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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
    fn gen_digit(&mut self) -> i32 {
        (self.next_u64() % 10) as i32
    }
}

fn make_digits(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // random digits
            for _ in 0..n { v.push(rng.gen_digit()); }
        }
        1 => {
            // all same
            let d = rng.gen_digit();
            for _ in 0..n { v.push(d); }
        }
        2 => {
            // sorted non-decreasing
            let mut cur = 0i32;
            for _ in 0..n {
                let add = (rng.next_u64() % 3) as i32;
                cur = (cur + add).min(9);
                v.push(cur);
            }
        }
        3 => {
            // strictly decreasing-ish
            let mut cur = 9i32;
            for _ in 0..n {
                v.push(cur);
                if cur > 0 && rng.next_u64() % 2 == 0 { cur -= 1; }
            }
        }
        4 => {
            // only 0s and 9s
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { 0 } else { 9 });
            }
        }
        5 => {
            // only two digit values
            let a = (rng.next_u64() % 10) as i32;
            let b = (rng.next_u64() % 10) as i32;
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { a } else { b });
            }
        }
        6 => {
            // pattern that fails: e.g., 987-like
            for i in 0..n {
                v.push(((9 - (i as i32 % 10)).max(0)).min(9));
            }
        }
        7 => {
            // zigzag
            for i in 0..n {
                v.push(if i % 2 == 0 { 1 } else { 8 });
            }
        }
        8 => {
            // small digits only
            for _ in 0..n { v.push((rng.next_u64() % 3) as i32); }
        }
        9 => {
            // like the example 040425524644
            let pattern = [0,4,0,4,2,5,5,2,4,6,4,4];
            for i in 0..n {
                v.push(pattern[i % pattern.len()]);
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_digit()); }
        }
    }
    v
}

fn print_json(digits: &[i32]) {
    print!("{{\"digits\":[");
    for i in 0..digits.len() {
        if i > 0 { print!(","); }
        print!("{}", digits[i]);
    }
    print!("],\"colors\":[],\"n\":{}}}", digits.len());
    println!();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match t % 7 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(3, 20),
            3 => rng.gen_range_usize(20, 100),
            4 => rng.gen_range_usize(100, 1000),
            5 => 1000,
            _ => rng.gen_range_usize(1, 500),
        };
        let digits = make_digits(&mut rng, mode, n);
        let res = generate_test_case(digits);
        print_json(&res);
    }
}