use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    money: i32,
    fillers: &Vec<i32>,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= len <= 50,
        len == fillers.len(),
        1 <= money <= 100,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
    ensures
        2 <= result.0.len() <= 50,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        1 <= result.1 <= 100,
        result.1 == money,
{
    let mut prices: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            0 <= i <= len,
            len == fillers.len(),
            2 <= len <= 50,
            prices.len() == i,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] prices[k] <= 100,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 100,
        decreases len - i,
    {
        prices.push(fillers[i]);
        i = i + 1;
    }
    (prices, money)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32) {
    let (len, money, fillers): (usize, i32, Vec<i32>) = match mode {
        0 => {
            // minimal
            let len = 2usize;
            let money = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            f.push(rng.gen_range_i32(1, 100));
            f.push(rng.gen_range_i32(1, 100));
            (len, money, f)
        }
        1 => {
            // max length
            let len = 50usize;
            let money = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            for _ in 0..len {
                f.push(rng.gen_range_i32(1, 100));
            }
            (len, money, f)
        }
        2 => {
            // all same price
            let len = rng.gen_range_usize(2, 50);
            let money = rng.gen_range_i32(1, 100);
            let v = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            for _ in 0..len {
                f.push(v);
            }
            (len, money, f)
        }
        3 => {
            // two cheap items, rest expensive - buy the two cheapest
            let len = rng.gen_range_usize(2, 50);
            let money = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            f.push(1);
            f.push(1);
            for _ in 2..len {
                f.push(100);
            }
            (len, money, f)
        }
        4 => {
            // all prices = 100, money small -> cannot buy
            let len = rng.gen_range_usize(2, 50);
            let money = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            for _ in 0..len {
                f.push(100);
            }
            (len, money, f)
        }
        5 => {
            // money exactly equals sum of two smallest
            let len = rng.gen_range_usize(2, 50);
            let a = rng.gen_range_i32(1, 50);
            let b = rng.gen_range_i32(1, 50);
            let money = a + b;
            let mut f = Vec::new();
            f.push(a);
            f.push(b);
            for _ in 2..len {
                f.push(rng.gen_range_i32(50, 100));
            }
            (len, money, f)
        }
        6 => {
            // money = 1 (smallest)
            let len = rng.gen_range_usize(2, 50);
            let mut f = Vec::new();
            for _ in 0..len {
                f.push(rng.gen_range_i32(1, 100));
            }
            (len, 1i32, f)
        }
        7 => {
            // money = 100 (largest)
            let len = rng.gen_range_usize(2, 50);
            let mut f = Vec::new();
            for _ in 0..len {
                f.push(rng.gen_range_i32(1, 100));
            }
            (len, 100i32, f)
        }
        8 => {
            // price ascending
            let len = rng.gen_range_usize(2, 50);
            let money = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            for i in 0..len {
                let v = ((i % 100) as i32) + 1;
                f.push(v);
            }
            (len, money, f)
        }
        9 => {
            // one very small, rest large
            let len = rng.gen_range_usize(2, 50);
            let money = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            f.push(1);
            for _ in 1..len {
                f.push(rng.gen_range_i32(90, 100));
            }
            (len, money, f)
        }
        _ => {
            // random
            let len = rng.gen_range_usize(2, 50);
            let money = rng.gen_range_i32(1, 100);
            let mut f = Vec::new();
            for _ in 0..len {
                f.push(rng.gen_range_i32(1, 100));
            }
            (len, money, f)
        }
    };

    generate_test_case(len, money, &fillers)
}

fn print_json(prices: &[i32], money: i32) {
    print!("{{\"prices\":[");
    for i in 0..prices.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", prices[i]);
    }
    println!("],\"money\":{}}}", money);
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
        let (prices, money) = build_case(&mut rng, mode);
        print_json(&prices, money);
    }
}