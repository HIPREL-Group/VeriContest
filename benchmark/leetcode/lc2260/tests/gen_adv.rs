use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (cards: Vec<i32>)
    requires
        1 <= values.len() <= 100000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1000000,
    ensures
        1 <= cards.len() <= 100000,
        forall|i: int| 0 <= i < cards.len() ==> 0 <= #[trigger] cards[i] <= 1000000,
{
    let n = values.len();
    let mut cards: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            cards.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] cards[k] <= 1000000,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1000000,
        decreases n - i,
    {
        cards.push(values[i]);
        i = i + 1;
    }
    cards
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build(mode: usize, rng: &mut Rng, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5));
            }
            v
        }
        1 => {
            // single element - impossible
            vec![rng.gen_range_i32(0, 1_000_000)]
        }
        2 => {
            // all distinct
            let n = rng.gen_range_usize(2, 1000);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push(i as i32);
            }
            v
        }
        3 => {
            // all same
            let n = rng.gen_range_usize(2, 1000);
            let val = rng.gen_range_i32(0, 1_000_000);
            vec![val; n]
        }
        4 => {
            // two adjacent equal at end
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            for i in 0..n-2 {
                v.push(i as i32);
            }
            v.push(999_999);
            v.push(999_999);
            v
        }
        5 => {
            // two equal far apart
            let n = rng.gen_range_usize(10, 1000);
            let mut v = Vec::with_capacity(n);
            v.push(42);
            for i in 1..n-1 {
                v.push(1000 + i as i32);
            }
            v.push(42);
            v
        }
        6 => {
            // large random with small range (many duplicates)
            let n = rng.gen_range_usize(100, 10000);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
            v
        }
        7 => {
            // max size
            let n = 100000;
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                v.push((i as i32) % 1_000_001);
            }
            v
        }
        8 => {
            // boundary values 0 and 1_000_000
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                if rng.next_u64() % 2 == 0 {
                    v.push(0);
                } else {
                    v.push(1_000_000);
                }
            }
            v
        }
        9 => {
            // two equal adjacent at beginning
            let n = rng.gen_range_usize(2, 100);
            let mut v = Vec::with_capacity(n);
            v.push(7);
            v.push(7);
            for i in 2..n {
                v.push(100 + i as i32);
            }
            v
        }
        _ => {
            // medium random
            let n = rng.gen_range_usize(50, 500);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 1_000_000));
            }
            let _ = t;
            v
        }
    }
}

fn print_json(cards: &[i32]) {
    print!("{{\"cards\":[");
    for i in 0..cards.len() {
        if i > 0 { print!(","); }
        print!("{}", cards[i]);
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
    let total = 200usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build(mode, &mut rng, t);
        let cards = generate_test_case(&values);
        print_json(&cards);
    }
}