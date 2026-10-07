use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>, other: &Vec<i32>) -> (result: (Vec<i32>, Vec<i32>))
    requires
        values.len() == other.len(),
        1 <= values.len() <= 1000,
        forall |i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 10,
        forall |i: int| 0 <= i < other.len() ==> 0 <= #[trigger] other[i] <= 10,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 1000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 10,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 10,
{
    let mut p1: Vec<i32> = Vec::new();
    let mut p2: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            n == other.len(),
            0 <= i <= n,
            p1.len() == i,
            p2.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] p1[k] == values[k],
            forall |k: int| 0 <= k < i as int ==> #[trigger] p2[k] == other[k],
            forall |k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 10,
            forall |k: int| 0 <= k < other.len() ==> 0 <= #[trigger] other[k] <= 10,
        decreases n - i,
    {
        p1.push(values[i]);
        p2.push(other[i]);
        i += 1;
    }
    (p1, p2)
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    let n = match mode {
        0 => 1,
        1 => 2,
        2 => rng.range_usize(1, 10),
        3 => 1000,
        4 => rng.range_usize(3, 20),
        5 => rng.range_usize(50, 200),
        6 => rng.range_usize(1, 1000),
        7 => 10,
        8 => 100,
        9 => rng.range_usize(1, 50),
        _ => rng.range_usize(1, 100),
    };
    let mut p1: Vec<i32> = Vec::with_capacity(n);
    let mut p2: Vec<i32> = Vec::with_capacity(n);
    for _ in 0..n {
        let (a, b) = match mode {
            0 | 1 => (rng.range_i32(0, 10), rng.range_i32(0, 10)),
            2 => {
                // all tens
                (10, 10)
            }
            3 => (rng.range_i32(0, 10), rng.range_i32(0, 10)),
            4 => {
                // all zeros for one player
                (0, rng.range_i32(0, 10))
            }
            5 => {
                // many tens
                let a = if rng.next_u64() % 2 == 0 { 10 } else { rng.range_i32(0, 9) };
                let b = if rng.next_u64() % 2 == 0 { 10 } else { rng.range_i32(0, 9) };
                (a, b)
            }
            6 => (rng.range_i32(0, 10), rng.range_i32(0, 10)),
            7 => {
                // alternating tens
                (if rng.next_u64() % 3 == 0 { 10 } else { rng.range_i32(0, 9) },
                 if rng.next_u64() % 3 == 0 { 10 } else { rng.range_i32(0, 9) })
            }
            8 => {
                // equal scores likely
                let v = rng.range_i32(0, 10);
                (v, v)
            }
            9 => {
                // boundary values
                let vals = [0i32, 10, 1, 9, 5];
                (vals[(rng.next_u64() as usize) % 5], vals[(rng.next_u64() as usize) % 5])
            }
            _ => (rng.range_i32(0, 10), rng.range_i32(0, 10)),
        };
        p1.push(a);
        p2.push(b);
    }
    (p1, p2)
}

fn print_json(p1: &[i32], p2: &[i32]) {
    print!("{{\"player1\":[");
    for i in 0..p1.len() {
        if i > 0 { print!(","); }
        print!("{}", p1[i]);
    }
    print!("],\"player2\":[");
    for i in 0..p2.len() {
        if i > 0 { print!(","); }
        print!("{}", p2[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let (p1, p2) = gen_mode(&mut rng, mode);
        let (o1, o2) = generate_test_case(&p1, &p2);
        print_json(&o1, &o2);
    }
}