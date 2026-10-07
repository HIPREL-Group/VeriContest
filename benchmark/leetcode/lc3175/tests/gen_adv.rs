use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    k: i32,
    offset: i32,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= n <= 100000,
        1 <= k <= 1_000_000_000,
        1 <= offset,
        (offset as int) + (n as int) - 1 <= 1_000_000,
    ensures
        ({
            let skills = result.0;
            let kk = result.1;
            &&& 2 <= skills.len() <= 100000
            &&& 1 <= kk <= 1_000_000_000
            &&& kk == k
            &&& skills.len() == n
            &&& forall |i: int| 0 <= i < skills.len() ==> 1 <= #[trigger] skills[i] <= 1_000_000
            &&& forall |i: int, j: int| 0 <= i < j < skills.len() ==> skills[i] != skills[j]
        }),
{
    let mut skills: Vec<i32> = Vec::new();
    let mut idx: usize = 0;
    while idx < n
        invariant
            2 <= n <= 100000,
            1 <= offset,
            (offset as int) + (n as int) - 1 <= 1_000_000,
            0 <= idx <= n,
            skills.len() == idx,
            forall |i: int| 0 <= i < idx as int ==> #[trigger] skills[i] == (offset as int) + i,
        decreases n - idx,
    {
        let v: i32 = offset + (idx as i32);
        skills.push(v);
        idx = idx + 1;
    }

    proof {
        assert forall |i: int| 0 <= i < skills.len() implies 1 <= #[trigger] skills[i] <= 1_000_000 by {
            assert(skills[i] == (offset as int) + i);
        }
        assert forall |i: int, j: int| 0 <= i < j < skills.len() implies skills[i] != skills[j] by {
            assert(skills[i] == (offset as int) + i);
            assert(skills[j] == (offset as int) + j);
        }
    }

    (skills, k)
}

}

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

fn pick_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32, i32) {
    // returns (n, k, offset)
    match mode {
        0 => (2, 1, 1),
        1 => (2, 1_000_000_000, rng.gen_range_i32(1, 999_999)),
        2 => (100_000, 1, 1),
        3 => (100_000, 1_000_000_000, 1),
        4 => {
            let n = rng.gen_range_usize(2, 20);
            (n, rng.gen_range_i32(1, 10), rng.gen_range_i32(1, 1_000_000 - n as i32 + 1))
        }
        5 => {
            let n = rng.gen_range_usize(100, 1000);
            (n, rng.gen_range_i32(1, n as i32 + 5), rng.gen_range_i32(1, 1_000_000 - n as i32 + 1))
        }
        6 => {
            let n = 3;
            (n, 3, rng.gen_range_i32(1, 999_997))
        }
        7 => {
            let n = rng.gen_range_usize(2, 100);
            (n, n as i32, rng.gen_range_i32(1, 1_000_000 - n as i32 + 1))
        }
        8 => {
            let n = rng.gen_range_usize(2, 100);
            (n, (n as i32) - 1, rng.gen_range_i32(1, 1_000_000 - n as i32 + 1))
        }
        9 => {
            // k much larger than n
            let n = rng.gen_range_usize(2, 50);
            (n, 1_000_000_000, rng.gen_range_i32(1, 1_000_000 - n as i32 + 1))
        }
        _ => {
            let n = 2 + (t % 10000);
            let max_off = 1_000_000 - n as i32 + 1;
            (n, rng.gen_range_i32(1, 1_000_000_000), rng.gen_range_i32(1, max_off))
        }
    }
}

// Shuffle the generated skills (this maintains uniqueness and range).
fn shuffle(rng: &mut Rng, v: &mut Vec<i32>) {
    let n = v.len();
    if n < 2 { return; }
    let mut i = n - 1;
    while i > 0 {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
        i -= 1;
    }
}

fn print_json(skills: &[i32], k: i32) {
    print!("{{\"skills\":[");
    for i in 0..skills.len() {
        if i > 0 { print!(","); }
        print!("{}", skills[i]);
    }
    println!("],\"k\":{}}}", k);
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
        let (n, k, offset) = pick_params(&mut rng, mode, t);
        let (mut skills, kk) = generate_test_case(n, k, offset);
        // Shuffle to produce varied orderings (still valid)
        shuffle(&mut rng, &mut skills);
        print_json(&skills, kk);
    }
}