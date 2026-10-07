use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    zero_idx: usize,
    one_idx: usize,
    raw: &Vec<i32>,
) -> (seats: Vec<i32>)
    requires
        2 <= n <= 20_000,
        raw.len() == n,
        zero_idx < n,
        one_idx < n,
        zero_idx != one_idx,
        forall|i: int| 0 <= i < raw.len() ==> 0 <= #[trigger] raw[i] <= 1,
    ensures
        2 <= seats.len() <= 20_000,
        seats.len() == n,
        forall|i: int| 0 <= i < seats.len() ==> 0 <= #[trigger] seats[i] <= 1,
        exists|i: int| 0 <= i < seats.len() && seats[i] == 0,
        exists|i: int| 0 <= i < seats.len() && seats[i] == 1,
{
    let mut seats: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            seats.len() == i,
            raw.len() == n,
            zero_idx < n,
            one_idx < n,
            zero_idx != one_idx,
            forall|k: int| 0 <= k < raw.len() ==> 0 <= #[trigger] raw[k] <= 1,
            forall|k: int| 0 <= k < i as int && k == zero_idx as int ==> #[trigger] seats[k] == 0,
            forall|k: int| 0 <= k < i as int && k == one_idx as int ==> #[trigger] seats[k] == 1,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] seats[k] <= 1,
        decreases n - i,
    {
        if i == zero_idx {
            seats.push(0);
        } else if i == one_idx {
            seats.push(1);
        } else {
            seats.push(raw[i]);
        }
        i = i + 1;
    }

    proof {
        assert(seats[zero_idx as int] == 0);
        assert(seats[one_idx as int] == 1);
    }

    seats
}

}

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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_bool_prob(&mut self, num: u64, den: u64) -> bool {
        self.next_u64() % den < num
    }
}

fn choose_two(rng: &mut Rng, n: usize) -> (usize, usize) {
    let i = rng.gen_range_usize(0, n - 1);
    let mut j = rng.gen_range_usize(0, n - 2);
    if j >= i { j += 1; }
    (i, j)
}

fn build_raw(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // mostly zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // mostly ones
            for _ in 0..n { v.push(1); }
        }
        2 => {
            // random 50/50
            for _ in 0..n {
                v.push(if rng.gen_bool_prob(1, 2) { 1 } else { 0 });
            }
        }
        3 => {
            // sparse ones
            for _ in 0..n {
                v.push(if rng.gen_bool_prob(1, 10) { 1 } else { 0 });
            }
        }
        4 => {
            // sparse zeros
            for _ in 0..n {
                v.push(if rng.gen_bool_prob(1, 10) { 0 } else { 1 });
            }
        }
        5 => {
            // alternating
            for k in 0..n {
                v.push((k % 2) as i32);
            }
        }
        6 => {
            // blocks
            let block = rng.gen_range_usize(2, 20);
            for k in 0..n {
                v.push(((k / block) % 2) as i32);
            }
        }
        7 => {
            // one at front, rest zeros
            for k in 0..n {
                v.push(if k == 0 { 1 } else { 0 });
            }
        }
        8 => {
            // one at end, rest zeros
            for k in 0..n {
                v.push(if k == n - 1 { 1 } else { 0 });
            }
        }
        9 => {
            // one in middle
            let mid = n / 2;
            for k in 0..n {
                v.push(if k == mid { 1 } else { 0 });
            }
        }
        _ => {
            // two ones at ends
            for k in 0..n {
                v.push(if k == 0 || k == n - 1 { 1 } else { 0 });
            }
        }
    }
    v
}

fn print_json(seats: &[i32]) {
    print!("{{\"seats\":[");
    for i in 0..seats.len() {
        if i > 0 { print!(","); }
        print!("{}", seats[i]);
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
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match t % 7 {
            0 => 2,
            1 => 3,
            2 => rng.gen_range_usize(4, 20),
            3 => rng.gen_range_usize(20, 200),
            4 => rng.gen_range_usize(200, 2000),
            5 => rng.gen_range_usize(2000, 19999),
            _ => 20_000,
        };

        let raw = build_raw(&mut rng, n, mode);
        // Pick two distinct indices to guarantee at least one 0 and at least one 1.
        let (zero_idx, one_idx) = choose_two(&mut rng, n);
        let seats = generate_test_case(n, zero_idx, one_idx, &raw);
        print_json(&seats);
    }
}