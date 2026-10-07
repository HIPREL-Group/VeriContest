use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    start: i32,
    step: i32,
    n: usize,
    k: i32,
    x: i32,
) -> (res: (Vec<i32>, i32, i32))
    requires
        1 <= n <= 10000,
        1 <= k <= n as i32,
        1 <= step <= 20,
        -10000 <= x <= 10000,
        -10000 <= start <= 10000,
        start as int + (n as int - 1) * (step as int) <= 10000,
    ensures
        ({
            let arr = res.0;
            let kk = res.1;
            let xx = res.2;
            &&& 1 <= kk <= arr.len() as i32
            &&& 1 <= arr.len() <= 10000
            &&& (forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j])
            &&& (forall|i: int| 0 <= i < arr.len() ==> -10000 <= #[trigger] arr[i] <= 10000)
            &&& -10000 <= xx <= 10000
        }),
{
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            1 <= n <= 10000,
            1 <= step <= 20,
            -10000 <= start <= 10000,
            start as int + (n as int - 1) * (step as int) <= 10000,
            arr.len() == i,
            forall|j: int| 0 <= j < i as int ==> #[trigger] arr[j] == start as int + j * (step as int),
            forall|j: int| 0 <= j < i as int ==> -10000 <= #[trigger] arr[j] <= 10000,
        decreases n - i,
    {
        proof {
            assert(i < n);
            assert(i as int <= n as int - 1);
            assert(step as int >= 1);
            assert(i as int * step as int <= (n as int - 1) * step as int) by (nonlinear_arith)
                requires i as int <= n as int - 1, step as int >= 1, n as int >= 1;
            assert(i as int * step as int >= 0) by (nonlinear_arith)
                requires i as int >= 0, step as int >= 1;
            assert(start as int + i as int * step as int <= 10000);
            assert(start as int + i as int * step as int >= -10000);
        }
        let prod: i32 = (i as i32) * step;
        let v: i32 = start + prod;
        arr.push(v);
        proof {
            assert(arr[i as int] == v);
            assert(v as int == start as int + i as int * step as int);
        }
        i = i + 1;
    }

    proof {
        assert(arr.len() == n);
        assert forall|a: int, b: int| 0 <= a < b < arr.len() implies arr[a] <= arr[b] by {
            assert(arr[a] == start as int + a * (step as int));
            assert(arr[b] == start as int + b * (step as int));
            assert((b - a) * (step as int) >= 0) by (nonlinear_arith)
                requires b - a >= 1, step as int >= 1;
            assert(b * (step as int) - a * (step as int) == (b - a) * (step as int)) by (nonlinear_arith);
        }
        assert forall|j: int| 0 <= j < arr.len() implies -10000 <= #[trigger] arr[j] <= 10000 by {
        }
    }

    (arr, k, x)
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
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

fn print_json(arr: &[i32], k: i32, x: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"k\":{},\"x\":{}}}", k, x);
}

// pick params (start, step, n, k, x) satisfying requires
fn pick_params(rng: &mut Rng, mode: usize) -> (i32, i32, usize, i32, i32) {
    // Ensure start + (n-1)*step <= 10000 and start >= -10000
    match mode {
        0 => {
            // small n, k=1
            let n = rng.gen_range_usize(1, 5);
            let step = 1;
            let start = rng.gen_range_i32(-10000, 10000 - (n as i32 - 1) * step);
            let k = 1;
            let x = rng.gen_range_i32(-10000, 10000);
            (start, step, n, k, x)
        }
        1 => {
            // k == n
            let n = rng.gen_range_usize(1, 100);
            let step = 1;
            let start = rng.gen_range_i32(-10000, 10000 - (n as i32 - 1) * step);
            let k = n as i32;
            let x = rng.gen_range_i32(-10000, 10000);
            (start, step, n, k, x)
        }
        2 => {
            // x less than all
            let n = rng.gen_range_usize(5, 50);
            let step = 1;
            let start = rng.gen_range_i32(0, 10000 - (n as i32 - 1) * step);
            let k = rng.gen_range_usize(1, n) as i32;
            let x = rng.gen_range_i32(-10000, -1);
            (start, step, n, k, x)
        }
        3 => {
            // x greater than all
            let n = rng.gen_range_usize(5, 50);
            let step = 1;
            let start = rng.gen_range_i32(-10000, -1000);
            let max_end = start as i64 + (n as i64 - 1) * step as i64;
            if max_end > 10000 {
                return pick_params(rng, 0);
            }
            let k = rng.gen_range_usize(1, n) as i32;
            let x = rng.gen_range_i32(10000 - 10, 10000);
            (start, step, n, k, x)
        }
        4 => {
            // all same value (step=0 not allowed, so step=1 with tiny range - use step=1)
            // Actually we need sorted, duplicates allowed. Use step=1 instead.
            let n = rng.gen_range_usize(2, 100);
            let step = 1;
            let start = rng.gen_range_i32(-5000, 5000 - n as i32);
            let k = rng.gen_range_usize(1, n) as i32;
            let x = start + (n as i32 / 2);
            (start, step, n, k, x)
        }
        5 => {
            // large n
            let n = 10000;
            let step = 1;
            let start = -5000;
            // start + (n-1)*step = -5000 + 9999 = 4999, ok
            let k = rng.gen_range_usize(1, n) as i32;
            let x = rng.gen_range_i32(-10000, 10000);
            (start, step, n, k, x)
        }
        6 => {
            // x exactly in array
            let n = rng.gen_range_usize(5, 100);
            let step = 2;
            let max_start = 10000 - (n as i32 - 1) * step;
            if max_start < -10000 {
                return pick_params(rng, 0);
            }
            let start = rng.gen_range_i32(-10000, max_start);
            let k = rng.gen_range_usize(1, n) as i32;
            let idx = rng.gen_range_usize(0, n - 1);
            let x = start + (idx as i32) * step;
            (start, step, n, k, x)
        }
        7 => {
            // spread out
            let step = rng.gen_range_i32(1, 20);
            let n = rng.gen_range_usize(2, 50);
            let max_start = 10000 - (n as i32 - 1) * step;
            if max_start < -10000 {
                return pick_params(rng, 0);
            }
            let start = rng.gen_range_i32(-10000, max_start);
            let k = rng.gen_range_usize(1, n) as i32;
            let x = rng.gen_range_i32(-10000, 10000);
            (start, step, n, k, x)
        }
        8 => {
            // n=1
            let n = 1;
            let step = 1;
            let start = rng.gen_range_i32(-10000, 10000);
            let k = 1;
            let x = rng.gen_range_i32(-10000, 10000);
            (start, step, n, k, x)
        }
        9 => {
            // k=1, ties possible
            let n = rng.gen_range_usize(3, 100);
            let step = 2;
            let max_start = 10000 - (n as i32 - 1) * step;
            if max_start < -10000 {
                return pick_params(rng, 0);
            }
            let start = rng.gen_range_i32(-10000, max_start);
            let k = 1;
            // x between two elements (odd midpoint)
            let idx = rng.gen_range_usize(0, n - 2);
            let x = start + (idx as i32) * step + 1; // equidistant from two
            (start, step, n, k, x)
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let step = rng.gen_range_i32(1, 5);
            let max_start = 10000 - (n as i32 - 1) * step;
            if max_start < -10000 {
                return pick_params(rng, 0);
            }
            let start = rng.gen_range_i32(-10000, max_start);
            let k = rng.gen_range_usize(1, n) as i32;
            let x = rng.gen_range_i32(-10000, 10000);
            (start, step, n, k, x)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let (start, step, n, k, x) = pick_params(&mut rng, mode);
        // safety check
        let end = start as i64 + (n as i64 - 1) * step as i64;
        if end > 10000 || start < -10000 || n < 1 || n > 10000 || k < 1 || k > n as i32 || step < 1 || step > 20 {
            continue;
        }
        let (arr, kk, xx) = generate_test_case(start, step, n, k, x);
        print_json(&arr, kk, xx);
    }
}