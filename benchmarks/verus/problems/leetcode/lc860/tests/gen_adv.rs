use vstd::prelude::*;

verus! {

pub fn generate_test_case(bills: &Vec<i32>) -> (result: Vec<i32>)
    requires
        1 <= bills.len() <= 100_000,
        forall |i: int| 0 <= i < bills.len() ==> (#[trigger] bills[i]) == 5i32 || bills[i] == 10i32 || bills[i] == 20i32,
    ensures
        1 <= result.len() <= 100_000,
        forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i]) == 5i32 || result[i] == 10i32 || result[i] == 20i32,
{
    let mut result: Vec<i32> = Vec::new();
    let n = bills.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == bills.len(),
            1 <= n <= 100_000,
            0 <= i <= n,
            result.len() == i,
            forall |k: int| 0 <= k < bills.len() ==> (#[trigger] bills[k]) == 5i32 || bills[k] == 10i32 || bills[k] == 20i32,
            forall |k: int| 0 <= k < i ==> (#[trigger] result[k]) == bills[k],
        decreases n - i,
    {
        result.push(bills[i]);
        i = i + 1;
    }
    result
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

    fn pick_bill(&mut self) -> i32 {
        let r = self.next_u64() % 3;
        match r {
            0 => 5,
            1 => 10,
            _ => 20,
        }
    }
}

fn build_bills_mode(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // random
            for _ in 0..n {
                v.push(rng.pick_bill());
            }
        }
        1 => {
            // all 5s
            for _ in 0..n {
                v.push(5);
            }
        }
        2 => {
            // all 10s (impossible except if n=0)
            for _ in 0..n {
                v.push(10);
            }
        }
        3 => {
            // all 20s
            for _ in 0..n {
                v.push(20);
            }
        }
        4 => {
            // mostly 5s with some 10s and 20s
            for _ in 0..n {
                let r = rng.next_u64() % 10;
                if r < 7 { v.push(5); }
                else if r < 9 { v.push(10); }
                else { v.push(20); }
            }
        }
        5 => {
            // valid pattern: 5,5,5,10,20 repeated
            let pat = [5, 5, 5, 10, 20];
            for i in 0..n {
                v.push(pat[i % 5]);
            }
        }
        6 => {
            // tricky: 5,5,10,10,20 (example 2, should be false)
            let pat = [5, 5, 10, 10, 20];
            for i in 0..n {
                v.push(pat[i % 5]);
            }
        }
        7 => {
            // starts with 10 (invalid immediately)
            v.push(10);
            for _ in 1..n {
                v.push(rng.pick_bill());
            }
        }
        8 => {
            // starts with 20
            if n > 0 {
                v.push(20);
                for _ in 1..n {
                    v.push(rng.pick_bill());
                }
            }
        }
        9 => {
            // alternating 5,10
            for i in 0..n {
                if i % 2 == 0 { v.push(5); } else { v.push(10); }
            }
        }
        10 => {
            // many 5s front-loaded, then 20s at end
            let half = n / 2;
            for _ in 0..half {
                v.push(5);
            }
            for _ in half..n {
                v.push(20);
            }
        }
        _ => {
            for _ in 0..n {
                v.push(rng.pick_bill());
            }
        }
    }
    v
}

fn print_json(bills: &[i32]) {
    print!("{{\"bills\":[");
    for i in 0..bills.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", bills[i]);
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
        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => 5,
            3 => rng.gen_range_usize(1, 50),
            4 => rng.gen_range_usize(1, 500),
            5 => rng.gen_range_usize(1, 5000),
            _ => rng.gen_range_usize(1, 100_000),
        };
        let n = if n == 0 { 1 } else if n > 100_000 { 100_000 } else { n };
        let bills = build_bills_mode(&mut rng, mode, n);
        let out = generate_test_case(&bills);
        print_json(&out);
    }
}