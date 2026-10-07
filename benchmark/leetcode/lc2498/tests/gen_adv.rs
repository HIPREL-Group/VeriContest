use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    step: i32,
) -> (stones: Vec<i32>)
    requires
        2 <= n <= 100_000,
        1 <= step <= 10_000,
    ensures
        2 <= stones.len() <= 100_000,
        stones.len() == n,
        forall |i: int| 0 <= i < stones.len() ==> 0 <= #[trigger] stones[i] <= 1_000_000_000,
        stones[0] == 0,
        forall |i: int, j: int| 0 <= i < j < stones.len() ==> stones[i] < stones[j],
{
    // We generate stones[i] = i * step. Need (n-1) * step <= 1_000_000_000.
    // With n <= 100_000 and step <= 10_000, (n-1)*step <= 99_999 * 10_000 = 999_990_000 <= 1_000_000_000.
    let mut stones: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            2 <= n <= 100_000,
            1 <= step <= 10_000,
            0 <= i <= n,
            stones.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] stones[k] == k * (step as int),
        decreases n - i,
    {
        proof {
            assert((i as int) <= 99_999);
            assert((step as int) <= 10_000);
            assert((i as int) * (step as int) <= 99_999 * 10_000) by (nonlinear_arith)
                requires (i as int) <= 99_999, (step as int) <= 10_000, (i as int) >= 0, (step as int) >= 0;
            assert((i as int) * (step as int) >= 0) by (nonlinear_arith)
                requires (i as int) >= 0, (step as int) >= 0;
        }
        let v: i32 = (i as i32) * step;
        stones.push(v);
        i = i + 1;
    }

    proof {
        assert(stones.len() == n);
        assert forall |k: int| 0 <= k < stones.len() implies 0 <= #[trigger] stones[k] <= 1_000_000_000 by {
            assert(stones[k] == k * (step as int));
            assert(k * (step as int) >= 0) by (nonlinear_arith)
                requires k >= 0, (step as int) >= 0;
            assert(k <= 99_999);
            assert(k * (step as int) <= 99_999 * 10_000) by (nonlinear_arith)
                requires k <= 99_999, (step as int) <= 10_000, k >= 0, (step as int) >= 0;
        }
        assert(stones[0] == 0 * (step as int));
        assert(stones[0] == 0);
        assert forall |a: int, b: int| 0 <= a < b < stones.len() implies stones[a] < stones[b] by {
            assert(stones[a] == a * (step as int));
            assert(stones[b] == b * (step as int));
            assert((b - a) * (step as int) >= 1 * (step as int)) by (nonlinear_arith)
                requires b - a >= 1, (step as int) >= 1;
            assert(b * (step as int) - a * (step as int) == (b - a) * (step as int)) by (nonlinear_arith);
            assert(b * (step as int) > a * (step as int));
        }
    }

    stones
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

fn pick_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, i32) {
    match mode {
        0 => (2, 1),
        1 => (2, 10_000),
        2 => (100_000, 1),
        3 => (100_000, 10_000),
        4 => (3, 1_000_000),
        5 => {
            let n = rng.gen_range_usize(2, 100);
            let s = rng.gen_range_usize(1, 10_000) as i32;
            (n, s)
        }
        6 => {
            let n = rng.gen_range_usize(2, 100_000);
            (n, 1)
        }
        7 => {
            let n = rng.gen_range_usize(1000, 10_000);
            let s = rng.gen_range_usize(1, 100) as i32;
            (n, s)
        }
        8 => {
            let n = 5 + (t % 20);
            (n, 7)
        }
        9 => {
            let n = rng.gen_range_usize(2, 50_000);
            let s = rng.gen_range_usize(1, 20) as i32;
            (n, s)
        }
        _ => {
            let n = rng.gen_range_usize(2, 1000);
            let s = rng.gen_range_usize(1, 1000) as i32;
            (n, s)
        }
    }
}

fn print_json(stones: &[i32]) {
    print!("{{\"stones\":[");
    for i in 0..stones.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", stones[i]);
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

    // Clamp step so (n-1)*step <= 1e9. With n<=100_000, step<=10_000 suffices.
    for t in 0..total {
        let mode = t % modes;
        let (mut n, mut step) = pick_params(&mut rng, mode, t);
        if n < 2 { n = 2; }
        if n > 100_000 { n = 100_000; }
        if step < 1 { step = 1; }
        if step > 10_000 { step = 10_000; }

        let stones = generate_test_case(n, step);
        print_json(&stones);
    }
}