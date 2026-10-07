use vstd::prelude::*;

verus! {

pub fn generate_test_case(money: i32, children: i32) -> (result: (i32, i32))
    ensures
        1 <= result.0 <= 200,
        2 <= result.1 <= 30,
{
    let money = if money < 1 { 1 } else if money > 200 { 200 } else { money };
    let children = if children < 2 { 2 } else if children > 30 { 30 } else { children };
    (money, children)
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_case(rng: &mut Rng, mode: usize) -> (i32, i32) {
    match mode {
        0 => {
            // random
            let m = rng.gen_range_i32(1, 200);
            let c = rng.gen_range_i32(2, 30);
            (m, c)
        }
        1 => {
            // money < children (impossible)
            let c = rng.gen_range_i32(2, 30);
            let m = rng.gen_range_i32(1, c - 1);
            (m, c)
        }
        2 => {
            // money == children (all 1s)
            let c = rng.gen_range_i32(2, 30);
            (c, c)
        }
        3 => {
            // exactly 8*children
            let c = rng.gen_range_i32(2, 25);
            (8 * c, c)
        }
        4 => {
            // 8*(c-1) + 4 => should give c-2
            let c = rng.gen_range_i32(3, 25);
            (8 * (c - 1) + 4, c)
        }
        5 => {
            // 8*c + extra
            let c = rng.gen_range_i32(2, 20);
            let extra = rng.gen_range_i32(1, 10);
            let m = 8 * c + extra;
            if m <= 200 { (m, c) } else { (200, c) }
        }
        6 => {
            // boundary money = 1
            (1, rng.gen_range_i32(2, 30))
        }
        7 => {
            // money = 200, max
            (200, rng.gen_range_i32(2, 30))
        }
        8 => {
            // children = 2
            (rng.gen_range_i32(1, 200), 2)
        }
        9 => {
            // children = 30
            (rng.gen_range_i32(1, 200), 30)
        }
        _ => {
            // small cases likely to hit the 4-dollar edge
            let c = rng.gen_range_i32(2, 10);
            let m = rng.gen_range_i32(c, 8 * c + 5);
            let m = if m > 200 { 200 } else { m };
            (m, c)
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (money, children) = pick_case(&mut rng, mode);
        // clamp to be safe
        let money = if money < 1 { 1 } else if money > 200 { 200 } else { money };
        let children = if children < 2 { 2 } else if children > 30 { 30 } else { children };
        let (m, c) = generate_test_case(money, children);
        println!("{{\"money\": {}, \"children\": {}}}", m, c);
    }
}
