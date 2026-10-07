use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (colors: Vec<i32>)
    requires
        3 <= values.len() <= 100,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1,
    ensures
        3 <= colors.len() <= 100,
        forall|i: int| 0 <= i < colors.len() ==> 0 <= #[trigger] colors[i] <= 1,
{
    let n = values.len();
    let mut colors: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            3 <= n <= 100,
            i <= n,
            colors.len() == i,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] colors[k] <= 1,
        decreases n - i,
    {
        colors.push(values[i]);
        i = i + 1;
    }
    colors
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
    fn gen_bit(&mut self) -> i32 {
        (self.next_u64() % 2) as i32
    }
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 3,
        1 => 4,
        2 => 5,
        3 => 100,
        4 => 99,
        5 => rng.gen_range_usize(3, 10),
        6 => rng.gen_range_usize(3, 100),
        7 => rng.gen_range_usize(3, 100),
        8 => rng.gen_range_usize(3, 100),
        9 => rng.gen_range_usize(3, 100),
        _ => rng.gen_range_usize(3, 100),
    };
    let mut v: Vec<i32> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // all ones
            for _ in 0..n { v.push(1); }
        }
        2 => {
            // perfect alternation starting 0
            for i in 0..n { v.push((i % 2) as i32); }
        }
        3 => {
            // perfect alternation starting 1
            for i in 0..n { v.push(((i + 1) % 2) as i32); }
        }
        4 => {
            // alternation but odd length (won't fully wrap)
            for i in 0..n { v.push((i % 2) as i32); }
        }
        5 => {
            // two blocks
            let half = n / 2;
            for i in 0..n {
                if i < half { v.push(0); } else { v.push(1); }
            }
        }
        6 => {
            // single 1 in zeros
            for _ in 0..n { v.push(0); }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 1;
        }
        7 => {
            // single 0 in ones
            for _ in 0..n { v.push(1); }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 0;
        }
        8 => {
            // random
            for _ in 0..n { v.push(rng.gen_bit()); }
        }
        9 => {
            // alternation with one flip breaking it
            for i in 0..n { v.push((i % 2) as i32); }
            let idx = rng.gen_range_usize(0, n - 1);
            v[idx] = 1 - v[idx];
        }
        _ => {
            // mostly alternating with random noise
            for i in 0..n {
                if (rng.next_u64() % 5) == 0 {
                    v.push(rng.gen_bit());
                } else {
                    v.push((i % 2) as i32);
                }
            }
        }
    }
    let _ = t;
    v
}

fn print_json(colors: &[i32]) {
    print!("{{\"colors\":[");
    for i in 0..colors.len() {
        if i > 0 { print!(","); }
        print!("{}", colors[i]);
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
        let values = build_case(&mut rng, mode, t);
        // Safety: ensure 3 <= len <= 100 and values in [0,1]
        if values.len() < 3 || values.len() > 100 {
            continue;
        }
        let mut ok = true;
        for &x in &values {
            if x < 0 || x > 1 { ok = false; break; }
        }
        if !ok { continue; }
        let colors = generate_test_case(&values);
        print_json(&colors);
    }
}