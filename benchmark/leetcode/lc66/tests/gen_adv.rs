use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    first_digit: i32,
    rest: &Vec<i32>,
) -> (digits: Vec<i32>)
    requires
        1 <= first_digit <= 9,
        rest.len() <= 99,
        forall|i: int| 0 <= i < rest.len() ==> 0 <= #[trigger] rest[i] <= 9,
    ensures
        1 <= digits.len() <= 100,
        forall|i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
        digits.len() == 1 || digits[0] > 0,
{
    let mut result: Vec<i32> = Vec::new();
    result.push(first_digit);

    let mut i: usize = 0;
    while i < rest.len()
        invariant
            result.len() == i + 1,
            i <= rest.len(),
            result[0] == first_digit,
            1 <= first_digit <= 9,
            forall|k: int| 0 <= k < rest.len() ==> 0 <= #[trigger] rest[k] <= 9,
            forall|k: int| 0 <= k < result.len() ==> 0 <= #[trigger] result[k] <= 9,
        decreases rest.len() - i,
    {
        result.push(rest[i]);
        i = i + 1;
    }

    assert(result[0] == first_digit);
    assert(result[0] > 0);

    result
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_digit(&mut self) -> i32 {
        (self.next_u64() % 10) as i32
    }

    fn gen_nonzero_digit(&mut self) -> i32 {
        1 + (self.next_u64() % 9) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> (i32, Vec<i32>) {
    match mode {
        0 => {
            // Single digit, various values
            let d = (t % 9 + 1) as i32;
            (d, Vec::new())
        }
        1 => {
            // Single digit 9 (causes carry to extend length)
            (9, Vec::new())
        }
        2 => {
            // All 9s, length 2..100
            let n = rng.gen_range_usize(2, 100);
            let rest: Vec<i32> = (0..n - 1).map(|_| 9).collect();
            (9, rest)
        }
        3 => {
            // Ends in non-9 (no carry)
            let n = rng.gen_range_usize(2, 100);
            let mut rest: Vec<i32> = (0..n - 2).map(|_| rng.gen_digit()).collect();
            rest.push((rng.next_u64() % 9) as i32); // 0..=8
            (rng.gen_nonzero_digit(), rest)
        }
        4 => {
            // Ends in 9s partially, e.g., [1,2,9]
            let n = rng.gen_range_usize(2, 100);
            let k = rng.gen_range_usize(1, n - 1);
            let mut rest: Vec<i32> = (0..n - 1 - k).map(|_| rng.gen_digit()).collect();
            for _ in 0..k {
                rest.push(9);
            }
            (rng.gen_nonzero_digit(), rest)
        }
        5 => {
            // Length exactly 100, all 9s
            let rest: Vec<i32> = (0..99).map(|_| 9).collect();
            (9, rest)
        }
        6 => {
            // Length exactly 100, random
            let rest: Vec<i32> = (0..99).map(|_| rng.gen_digit()).collect();
            (rng.gen_nonzero_digit(), rest)
        }
        7 => {
            // Length 2, various
            let rest: Vec<i32> = vec![rng.gen_digit()];
            (rng.gen_nonzero_digit(), rest)
        }
        8 => {
            // Many zeros, e.g., [1,0,0,...,0]
            let n = rng.gen_range_usize(2, 100);
            let rest: Vec<i32> = (0..n - 1).map(|_| 0).collect();
            (1, rest)
        }
        9 => {
            // Pattern ending in 0
            let n = rng.gen_range_usize(2, 100);
            let mut rest: Vec<i32> = (0..n - 2).map(|_| rng.gen_digit()).collect();
            rest.push(0);
            (rng.gen_nonzero_digit(), rest)
        }
        _ => {
            // Random
            let n = rng.gen_range_usize(1, 100);
            let rest: Vec<i32> = (0..n - 1).map(|_| rng.gen_digit()).collect();
            (rng.gen_nonzero_digit(), rest)
        }
    }
}

fn print_json(first: i32, rest: &[i32]) {
    print!("{{\"digits\":[{}", first);
    for d in rest {
        print!(",{}", d);
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (first, rest) = build_case(&mut rng, mode, t);
        let digits = generate_test_case(first, &rest);
        let first_out = digits[0];
        let rest_out: Vec<i32> = digits[1..].to_vec();
        print_json(first_out, &rest_out);
    }
}