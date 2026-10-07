use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (machines: Vec<i32>)
    requires
        1 <= values.len() <= 10000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 100000,
    ensures
        1 <= machines.len() <= 10000,
        forall|i: int| 0 <= i < machines.len() ==> 0 <= #[trigger] machines[i] <= 100000,
{
    let n = values.len();
    let mut machines: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            machines.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 100000,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] machines[k] <= 100000,
        decreases n - i,
    {
        machines.push(values[i]);
        i = i + 1;
    }
    machines
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn clamp(v: i32) -> i32 {
    if v < 0 { 0 } else if v > 100000 { 100000 } else { v }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // n=1
            let v = rng.gen_range_i32(0, 100000);
            vec![v]
        }
        1 => {
            // small random
            let n = rng.gen_range_usize(2, 10);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 10));
            }
            v
        }
        2 => {
            // all zeros
            let n = rng.gen_range_usize(1, 100);
            vec![0i32; n]
        }
        3 => {
            // uniform equal (already balanced)
            let n = rng.gen_range_usize(1, 200);
            let v = rng.gen_range_i32(0, 100000);
            vec![v; n]
        }
        4 => {
            // one big, rest zero
            let n = rng.gen_range_usize(2, 500);
            let mut v = vec![0i32; n];
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = rng.gen_range_i32(0, 100000);
            v
        }
        5 => {
            // two ends
            let n = rng.gen_range_usize(2, 1000);
            let mut v = vec![0i32; n];
            v[0] = rng.gen_range_i32(0, 100000);
            v[n - 1] = rng.gen_range_i32(0, 100000);
            v
        }
        6 => {
            // sum not divisible
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 5));
            }
            v
        }
        7 => {
            // large n random small values
            let n = 10000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100));
            }
            v
        }
        8 => {
            // large n max values
            let n = 10000;
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(99000, 100000));
            }
            v
        }
        9 => {
            // alternating
            let n = rng.gen_range_usize(2, 500);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(0, 100000));
                } else {
                    v.push(0);
                }
            }
            v
        }
        10 => {
            // balanced sum - guarantee divisibility
            let n = rng.gen_range_usize(2, 500);
            let avg = rng.gen_range_i32(0, 50000);
            let mut v = vec![avg; n];
            // perturb
            for _ in 0..(n / 2) {
                let i = rng.gen_range_usize(0, n - 1);
                let j = rng.gen_range_usize(0, n - 1);
                if i != j {
                    let d = rng.gen_range_i32(0, 1000);
                    let ni = clamp(v[i] + d);
                    let nj = clamp(v[j] - d);
                    let actual = (ni - v[i]) + (nj - v[j]);
                    if actual == 0 {
                        v[i] = ni;
                        v[j] = nj;
                    }
                }
            }
            v
        }
        11 => {
            // single value spike
            let n = rng.gen_range_usize(1, 100);
            let mut v = vec![rng.gen_range_i32(0, 100); n];
            if n > 1 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = 100000;
            }
            v
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(0, 100000));
            }
            v
        }
    }
}

fn print_json(machines: &[i32]) {
    print!("{{\"machines\":[");
    for i in 0..machines.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", machines[i]);
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
    let modes = 13usize;
    let total = 208usize;

    for t in 0..total {
        let mode = t % modes;
        let values = gen_mode(&mut rng, mode);
        // sanity clamp
        let mut clamped = Vec::with_capacity(values.len());
        for v in &values {
            clamped.push(clamp(*v));
        }
        if clamped.is_empty() {
            clamped.push(0);
        }
        if clamped.len() > 10000 {
            clamped.truncate(10000);
        }
        let machines = generate_test_case(&clamped);
        print_json(&machines);
    }
}