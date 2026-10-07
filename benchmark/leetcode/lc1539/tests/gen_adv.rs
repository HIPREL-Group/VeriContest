use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    start: i32,
    step: i32,
    k: i32,
) -> (res: (Vec<i32>, i32))
    requires
        1 <= n <= 1000,
        1 <= start <= 500,
        1 <= step <= 1,
        1 <= k <= 1000,
        start as int + (n as int - 1) * (step as int) <= 1000,
    ensures
        1 <= res.0.len() <= 1000,
        forall |i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 1000,
        1 <= res.1 <= 1000,
        forall |i: int, j: int| 0 <= i < j < res.0.len() ==> res.0[i] < res.0[j],
        res.1 == k,
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 1000,
            1 <= start <= 500,
            step == 1,
            start as int + (n as int - 1) * (step as int) <= 1000,
            arr.len() == i,
            forall |j: int| 0 <= j < i as int ==> #[trigger] arr[j] == start as int + j,
            forall |j: int| 0 <= j < i as int ==> 1 <= #[trigger] arr[j] <= 1000,
            forall |a: int, b: int| 0 <= a < b < i as int ==> arr[a] < arr[b],
        decreases n - i,
    {
        let v: i32 = start + (i as i32);
        assert(v as int == start as int + i as int);
        assert(1 <= v);
        assert(v as int <= start as int + (n as int - 1));
        assert(v as int <= 1000);
        arr.push(v);
        i = i + 1;
    }

    (arr, k)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn pick_params(rng: &mut Rng, mode: usize) -> (usize, i32, i32, i32) {
    // step is always 1 to satisfy invariants; we shrink n/start so start + (n-1) <= 1000
    let step: i32 = 1;
    match mode {
        0 => {
            // minimal: n=1
            let start = rng.gen_range_i32(1, 500);
            let k = rng.gen_range_i32(1, 1000);
            (1, start, step, k)
        }
        1 => {
            // maximum n
            let start = 1;
            let k = rng.gen_range_i32(1, 1000);
            (1000, start, step, k)
        }
        2 => {
            // k = 1 (smallest)
            let n = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(1, 500);
            (n, start, step, 1)
        }
        3 => {
            // k = 1000 (largest)
            let n = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(1, 500);
            (n, start, step, 1000)
        }
        4 => {
            // arr starts at 1, so missing must come after array
            let n = rng.gen_range_usize(1, 500);
            let k = rng.gen_range_i32(1, 1000);
            (n, 1, step, k)
        }
        5 => {
            // arr starts high so many missing at front
            let start = rng.gen_range_i32(400, 500);
            let n = rng.gen_range_usize(1, 100);
            let k = rng.gen_range_i32(1, 1000);
            (n, start, step, k)
        }
        6 => {
            // k equals n
            let n = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(1, 500);
            (n, start, step, n as i32)
        }
        7 => {
            // small arr, large k
            let n = rng.gen_range_usize(1, 10);
            let start = rng.gen_range_i32(1, 10);
            let k = rng.gen_range_i32(900, 1000);
            (n, start, step, k)
        }
        8 => {
            // medium everything
            let n = rng.gen_range_usize(100, 500);
            let start = rng.gen_range_i32(1, 400);
            let k = rng.gen_range_i32(1, 500);
            (n, start, step, k)
        }
        9 => {
            // start = 2 -- k=1 missing is 1
            let n = rng.gen_range_usize(1, 500);
            let k = rng.gen_range_i32(1, 1000);
            (n, 2, step, k)
        }
        _ => {
            let n = rng.gen_range_usize(1, 500);
            let start = rng.gen_range_i32(1, 400);
            let k = rng.gen_range_i32(1, 1000);
            (n, start, step, k)
        }
    }
}

fn print_json(arr: &[i32], k: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr[i]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (mut n, mut start, step, k) = pick_params(&mut rng, mode);
        // ensure start + (n-1)*step <= 1000
        while (start as i64) + (n as i64 - 1) * (step as i64) > 1000 {
            if n > 1 {
                n -= 1;
            } else {
                start = 1;
                break;
            }
        }
        if n < 1 {
            n = 1;
        }
        if start < 1 {
            start = 1;
        }
        if start > 500 {
            start = 500;
        }
        let (arr, kk) = generate_test_case(n, start, step, k);
        print_json(&arr, kk);
    }
}