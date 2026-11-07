use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    target: i32,
    houses: Vec<i32>,
    cost: Vec<Vec<i32>>,
) -> (result: (Vec<i32>, Vec<Vec<i32>>, i32, i32, i32))
    requires
        1 <= m <= 100,
        1 <= n <= 20,
        1 <= target <= m,
        houses.len() == m as int,
        cost.len() == m as int,
        forall|i: int| 0 <= i < m as int ==> 0 <= #[trigger] houses[i] <= n,
        forall|i: int| 0 <= i < m as int ==> (#[trigger] cost[i]).len() == n as int,
        forall|i: int, j: int|
            0 <= i < m as int && 0 <= j < n as int ==> 1 <= #[trigger] cost[i]@[j] <= 10_000,
    ensures
        result.2 as int == result.0@.len(),
        result.2 as int == result.1@.len(),
        1 <= result.2 <= 100,
        1 <= result.3 <= 20,
        1 <= result.4 <= result.2,
        forall|i: int| 0 <= i < result.2 as int ==> 0 <= #[trigger] result.0@[i] <= result.3,
        forall|i: int| 0 <= i < result.2 as int ==> (#[trigger] result.1@[i])@.len() == result.3 as int,
        forall|i: int, j: int|
            0 <= i < result.2 as int && 0 <= j < result.3 as int
                ==> 1 <= #[trigger] result.1@[i]@[j] <= 10_000,
{
    (houses, cost, m, n, target)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, idx: usize) -> (Vec<i32>, Vec<Vec<i32>>, i32, i32, i32) {
    let (m, n, target, paint_prob): (i32, i32, i32, u32) = match mode {
        0 => (1, 1, 1, 0),
        1 => (1, 20, 1, 0),
        2 => (100, 1, 1, 0),
        3 => (100, 20, 100, 100),
        4 => (100, 20, 1, 0),
        5 => {
            let m = rng.gen_usize(1, 10) as i32;
            let n = rng.gen_usize(1, 5) as i32;
            let t = rng.gen_usize(1, m as usize) as i32;
            (m, n, t, 50)
        }
        6 => {
            let m = rng.gen_usize(50, 100) as i32;
            let n = rng.gen_usize(10, 20) as i32;
            let t = rng.gen_usize(1, m as usize) as i32;
            (m, n, t, 30)
        }
        7 => {
            let m = rng.gen_usize(1, 100) as i32;
            let n = rng.gen_usize(1, 20) as i32;
            let t = rng.gen_usize(1, m as usize) as i32;
            (m, n, t, 100)
        }
        8 => {
            let m = rng.gen_usize(1, 100) as i32;
            let n = rng.gen_usize(1, 20) as i32;
            (m, n, m, 0)
        }
        9 => {
            let m = rng.gen_usize(2, 100) as i32;
            let n = rng.gen_usize(2, 20) as i32;
            (m, n, 1, 0)
        }
        _ => {
            let m = rng.gen_usize(1, 100) as i32;
            let n = rng.gen_usize(1, 20) as i32;
            let t = rng.gen_usize(1, m as usize) as i32;
            let p = rng.gen_usize(0, 100) as u32;
            (m, n, t, p)
        }
    };

    let _ = idx;

    let mut houses: Vec<i32> = Vec::with_capacity(m as usize);
    for _ in 0..m {
        let r = rng.gen_usize(0, 99) as u32;
        if r < paint_prob {
            houses.push(rng.gen_i32(1, n));
        } else {
            houses.push(0);
        }
    }

    let mut cost: Vec<Vec<i32>> = Vec::with_capacity(m as usize);
    for _ in 0..m {
        let mut row: Vec<i32> = Vec::with_capacity(n as usize);
        for _ in 0..n {
            row.push(rng.gen_i32(1, 10_000));
        }
        cost.push(row);
    }

    generate_test_case(m, n, target, houses, cost)
}

fn print_json(houses: &[i32], cost: &[Vec<i32>], m: i32, n: i32, target: i32) {
    print!("{{\"houses\":[");
    for i in 0..houses.len() {
        if i > 0 { print!(","); }
        print!("{}", houses[i]);
    }
    print!("],\"cost\":[");
    for i in 0..cost.len() {
        if i > 0 { print!(","); }
        print!("[");
        for j in 0..cost[i].len() {
            if j > 0 { print!(","); }
            print!("{}", cost[i][j]);
        }
        print!("]");
    }
    println!("],\"m\":{},\"n\":{},\"target\":{}}}", m, n, target);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (h, c, m, n, tg) = build_case(&mut rng, mode, t);
        print_json(&h, &c, m, n, tg);
    }
}