use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    values: &Vec<i32>,
) -> (digits: Vec<i32>)
    requires
        3 <= len <= 10,
        values.len() == len,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 9,
    ensures
        3 <= digits.len() <= 10,
        forall |i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
{
    let mut digits: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            len == values.len(),
            3 <= len <= 10,
            digits.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 9,
            forall |k: int| 0 <= k < digits.len() ==> 0 <= #[trigger] digits[k] <= 9,
            forall |k: int| 0 <= k < digits.len() ==> #[trigger] digits[k] == values[k],
        decreases len - i,
    {
        digits.push(values[i]);
        i = i + 1;
    }
    digits
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
}

fn make_values(rng: &mut Rng, mode: usize, len: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::new();
    match mode {
        0 => {
            // all zeros
            for _ in 0..len { v.push(0); }
        }
        1 => {
            // all nines
            for _ in 0..len { v.push(9); }
        }
        2 => {
            // all same even
            let d = (rng.gen_range_usize(0, 4) * 2) as i32;
            for _ in 0..len { v.push(d); }
        }
        3 => {
            // all same odd
            let d = (rng.gen_range_usize(0, 4) * 2 + 1) as i32;
            for _ in 0..len { v.push(d); }
        }
        4 => {
            // only odd digits
            for _ in 0..len {
                v.push((rng.gen_range_usize(0, 4) * 2 + 1) as i32);
            }
        }
        5 => {
            // only even digits
            for _ in 0..len {
                v.push((rng.gen_range_usize(0, 4) * 2) as i32);
            }
        }
        6 => {
            // many zeros
            for _ in 0..len {
                if rng.gen_range_usize(0, 2) == 0 {
                    v.push(0);
                } else {
                    v.push(rng.gen_range_usize(1, 9) as i32);
                }
            }
        }
        7 => {
            // sequential 0..len
            for i in 0..len {
                v.push((i % 10) as i32);
            }
        }
        8 => {
            // two distinct values
            let a = rng.gen_range_usize(0, 9) as i32;
            let b = rng.gen_range_usize(0, 9) as i32;
            for i in 0..len {
                v.push(if i % 2 == 0 { a } else { b });
            }
        }
        9 => {
            // pairs of duplicates
            for i in 0..len {
                v.push(((i / 2) % 10) as i32);
            }
        }
        _ => {
            // uniform random
            for _ in 0..len {
                v.push(rng.gen_range_usize(0, 9) as i32);
            }
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
        let len = match mode {
            0 => 3,
            1 => 10,
            2 => 3 + (t % 8),
            3 => 3 + (t % 8),
            _ => 3 + rng.gen_range_usize(0, 7),
        };
        let len = if len < 3 { 3 } else if len > 10 { 10 } else { len };

        let values = make_values(&mut rng, mode, len);
        let digits = generate_test_case(len, &values);
        print_json(&digits);
    }
}