use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (bulbs: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
    ensures
        1 <= bulbs.len() <= 100,
        forall|i: int| 0 <= i < bulbs.len() ==> 1 <= #[trigger] bulbs[i] <= 100,
{
    let mut bulbs: Vec<i32> = Vec::new();
    let n = values.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            bulbs.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100,
            forall|k: int| 0 <= k < bulbs.len() ==> 1 <= #[trigger] bulbs[k] <= 100,
            forall|k: int| 0 <= k < bulbs.len() ==> #[trigger] bulbs[k] == values[k],
        decreases n - i,
    {
        bulbs.push(values[i]);
        i = i + 1;
    }
    bulbs
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build(mode: usize, rng: &mut Rng) -> Vec<i32> {
    match mode {
        0 => {
            // minimum length
            vec![rng.gen_range_i32(1, 100)]
        }
        1 => {
            // max length random
            let mut v = Vec::with_capacity(100);
            for _ in 0..100 {
                v.push(rng.gen_range_i32(1, 100));
            }
            v
        }
        2 => {
            // all same value (toggles many times)
            let x = rng.gen_range_i32(1, 100);
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| x).collect()
        }
        3 => {
            // all 1s, even count -> empty output
            let n = rng.gen_range_usize(1, 50) * 2;
            (0..n).map(|_| 1i32).collect()
        }
        4 => {
            // all 1s, odd count -> [1]
            let n = rng.gen_range_usize(0, 49) * 2 + 1;
            (0..n).map(|_| 1i32).collect()
        }
        5 => {
            // all 100s
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| 100i32).collect()
        }
        6 => {
            // sorted ascending
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v.sort();
            v
        }
        7 => {
            // sorted descending
            let n = rng.gen_range_usize(1, 100);
            let mut v = Vec::new();
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 100));
            }
            v.sort();
            v.reverse();
            v
        }
        8 => {
            // distinct values 1..=k
            let k = rng.gen_range_usize(1, 100);
            (1..=k as i32).collect()
        }
        9 => {
            // pairs of duplicates
            let k = rng.gen_range_usize(1, 50);
            let mut v = Vec::new();
            for _ in 0..k {
                let x = rng.gen_range_i32(1, 100);
                v.push(x);
                v.push(x);
            }
            v
        }
        _ => {
            // random
            let n = rng.gen_range_usize(1, 100);
            (0..n).map(|_| rng.gen_range_i32(1, 100)).collect()
        }
    }
}

fn print_json(bulbs: &[i32]) {
    print!("{{\"bulbs\":[");
    for i in 0..bulbs.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", bulbs[i]);
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
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build(mode, &mut rng);
        // safety clamp
        if values.is_empty() || values.len() > 100 {
            continue;
        }
        let mut ok = true;
        for &x in &values {
            if x < 1 || x > 100 {
                ok = false;
                break;
            }
        }
        if !ok {
            continue;
        }
        let bulbs = generate_test_case(&values);
        print_json(&bulbs);
    }
}