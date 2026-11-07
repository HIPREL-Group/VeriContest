use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    start: i32,
    finish: i32,
    fuel: i32,
    offset: i32,
) -> (result: (Vec<i32>, i32, i32, i32))
    requires
        2 <= n <= 100,
        0 <= start < n as i32,
        0 <= finish < n as i32,
        1 <= fuel <= 200,
        1 <= offset as int,
        offset as int + n as int <= 1_000_000_000,
    ensures
        2 <= result.0.len() <= 100,
        result.0.len() == n,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall |i: int, j: int| #![trigger result.0[i], result.0[j]]
            0 <= i && i < j && j < result.0.len() ==> result.0[i] != result.0[j],
        0 <= result.1 < result.0.len() as i32,
        0 <= result.2 < result.0.len() as i32,
        1 <= result.3 <= 200,
        result.1 == start,
        result.2 == finish,
        result.3 == fuel,
{
    let mut locs: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n <= 100,
            locs.len() == i,
            1 <= offset as int,
            offset as int + n as int <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> #[trigger] locs[k] == offset as int + k,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] locs[k] <= 1_000_000_000,
        decreases n - i,
    {
        let v: i32 = offset + (i as i32);
        locs.push(v);
        i = i + 1;
    }

    assert forall |a: int, b: int| #![trigger locs[a], locs[b]]
        0 <= a && a < b && b < locs.len() implies locs[a] != locs[b]
    by {
        assert(locs[a] == offset as int + a);
        assert(locs[b] == offset as int + b);
    }

    (locs, start, finish, fuel)
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

fn print_json(locs: &[i32], start: i32, finish: i32, fuel: i32) {
    print!("{{\"locations\":[");
    for i in 0..locs.len() {
        if i > 0 { print!(","); }
        print!("{}", locs[i]);
    }
    println!("],\"start\":{},\"finish\":{},\"fuel\":{}}}", start, finish, fuel);
}

fn make_case(rng: &mut Rng, mode: usize) -> (Vec<i32>, i32, i32, i32) {
    let (n, start, finish, fuel, offset): (usize, i32, i32, i32, i32) = match mode {
        0 => {
            // minimal: n=2
            let s = rng.gen_range_i32(0, 1);
            let f = rng.gen_range_i32(0, 1);
            (2usize, s, f, rng.gen_range_i32(1, 200), rng.gen_range_i32(1, 1000))
        }
        1 => {
            // max n
            let n = 100usize;
            let s = rng.gen_range_i32(0, 99);
            let f = rng.gen_range_i32(0, 99);
            (n, s, f, rng.gen_range_i32(1, 200), 1)
        }
        2 => {
            // start == finish
            let n = rng.gen_range_usize(2, 100);
            let s = rng.gen_range_i32(0, n as i32 - 1);
            (n, s, s, rng.gen_range_i32(1, 200), rng.gen_range_i32(1, 1000))
        }
        3 => {
            // fuel = 1
            let n = rng.gen_range_usize(2, 100);
            let s = rng.gen_range_i32(0, n as i32 - 1);
            let f = rng.gen_range_i32(0, n as i32 - 1);
            (n, s, f, 1i32, rng.gen_range_i32(1, 100))
        }
        4 => {
            // fuel = 200 (max)
            let n = rng.gen_range_usize(2, 100);
            let s = rng.gen_range_i32(0, n as i32 - 1);
            let f = rng.gen_range_i32(0, n as i32 - 1);
            (n, s, f, 200i32, 1)
        }
        5 => {
            // large offset (locations near max)
            let n = rng.gen_range_usize(2, 50);
            let s = rng.gen_range_i32(0, n as i32 - 1);
            let f = rng.gen_range_i32(0, n as i32 - 1);
            let off: i32 = 1_000_000_000 - (n as i32);
            (n, s, f, rng.gen_range_i32(1, 200), off)
        }
        6 => {
            // start=0, finish=n-1
            let n = rng.gen_range_usize(2, 100);
            (n, 0i32, n as i32 - 1, rng.gen_range_i32(1, 200), rng.gen_range_i32(1, 1000))
        }
        7 => {
            // start=n-1, finish=0
            let n = rng.gen_range_usize(2, 100);
            (n, n as i32 - 1, 0i32, rng.gen_range_i32(1, 200), rng.gen_range_i32(1, 1000))
        }
        8 => {
            // small n, high fuel
            let n = rng.gen_range_usize(2, 5);
            let s = rng.gen_range_i32(0, n as i32 - 1);
            let f = rng.gen_range_i32(0, n as i32 - 1);
            (n, s, f, rng.gen_range_i32(150, 200), rng.gen_range_i32(1, 50))
        }
        9 => {
            // large n, high fuel (stress DP)
            let n = rng.gen_range_usize(80, 100);
            let s = rng.gen_range_i32(0, n as i32 - 1);
            let f = rng.gen_range_i32(0, n as i32 - 1);
            (n, s, f, rng.gen_range_i32(180, 200), 1)
        }
        _ => {
            // random
            let n = rng.gen_range_usize(2, 100);
            let s = rng.gen_range_i32(0, n as i32 - 1);
            let f = rng.gen_range_i32(0, n as i32 - 1);
            let max_off = 1_000_000_000 - n as i32;
            let off = rng.gen_range_i32(1, max_off);
            (n, s, f, rng.gen_range_i32(1, 200), off)
        }
    };

    let result = generate_test_case(n, start, finish, fuel, offset);
    (result.0, result.1, result.2, result.3)
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
        let (locs, s, f, fuel) = make_case(&mut rng, mode);
        print_json(&locs, s, f, fuel);
    }
}