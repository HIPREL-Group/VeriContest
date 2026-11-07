use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    values: &Vec<i32>,
) -> (arr: Vec<i32>)
    requires
        2 <= values.len() <= 500,
        forall |k: int| 0 <= k < values.len() ==> -1000 <= #[trigger] values[k] <= 1000,
    ensures
        2 <= arr.len() <= 500,
        forall |k: int| 0 <= k < arr.len() ==> -1000 <= #[trigger] arr[k] <= 1000,
{
    let n = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            2 <= n <= 500,
            0 <= i <= n,
            arr.len() == i,
            forall |k: int| 0 <= k < values.len() ==> -1000 <= #[trigger] values[k] <= 1000,
            forall |k: int| 0 <= k < arr.len() ==> arr[k] == values[k],
            forall |k: int| 0 <= k < arr.len() ==> -1000 <= #[trigger] arr[k] <= 1000,
        decreases n - i,
    {
        arr.push(values[i]);
        i = i + 1;
    }
    arr
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

fn clamp(v: i32) -> i32 {
    if v < -1000 { -1000 } else if v > 1000 { 1000 } else { v }
}

fn make_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => 500,
        3 => rng.gen_range_usize(2, 20),
        4 => rng.gen_range_usize(2, 500),
        5 => rng.gen_range_usize(10, 100),
        6 => 2,
        7 => 500,
        8 => rng.gen_range_usize(2, 50),
        9 => rng.gen_range_usize(2, 500),
        _ => rng.gen_range_usize(2, 500),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);

    match mode {
        0 => {
            // simple small: two values where one is double the other
            let x = rng.gen_range_i32(-500, 500);
            v.push(clamp(x));
            v.push(clamp(x * 2));
        }
        1 => {
            // includes zero: [0,0,...] -- two zeros satisfy the condition (0 == 2*0)
            v.push(0);
            v.push(0);
            v.push(clamp(rng.gen_range_i32(-1000, 1000)));
        }
        2 => {
            // large all random in full range
            for _ in 0..n {
                v.push(clamp(rng.gen_range_i32(-1000, 1000)));
            }
        }
        3 => {
            // negative values: ensure one is double another (double of negative)
            let x = rng.gen_range_i32(-500, -1);
            for _ in 0..n {
                v.push(clamp(rng.gen_range_i32(-1000, 1000)));
            }
            v[0] = clamp(x);
            if n >= 2 { v[1] = clamp(x * 2); }
        }
        4 => {
            // all the same odd number => no doubles exist
            let x = rng.gen_range_i32(-500, 500) * 2 + 1;
            let xc = clamp(x);
            for _ in 0..n {
                v.push(xc);
            }
        }
        5 => {
            // single zero - should not match
            for _ in 0..n {
                let mut x = rng.gen_range_i32(-1000, 1000);
                if x == 0 { x = 1; }
                v.push(x);
            }
            v[0] = 0;
        }
        6 => {
            // extreme boundary values
            v.push(1000);
            v.push(500);
        }
        7 => {
            // all zeros - 0 == 2*0 so lots of matches
            for _ in 0..n {
                v.push(0);
            }
        }
        8 => {
            // arr[i] == arr[j] but not double
            let x = rng.gen_range_i32(-500, 500);
            for _ in 0..n {
                v.push(clamp(x));
            }
        }
        9 => {
            // adversarial: double exists but only with distinct indices, e.g., only one occurrence of 0
            for _ in 0..n {
                v.push(clamp(rng.gen_range_i32(-1000, 1000)));
            }
            // force a double pair somewhere
            let i = rng.gen_range_usize(0, n - 1);
            let mut j = rng.gen_range_usize(0, n - 2);
            if j >= i { j += 1; }
            let x = rng.gen_range_i32(-500, 500);
            v[i] = clamp(x);
            v[j] = clamp(x * 2);
        }
        _ => {
            for _ in 0..n {
                v.push(clamp(rng.gen_range_i32(-1000, 1000)));
            }
        }
    }

    // Final clamping safety
    for k in 0..v.len() {
        v[k] = clamp(v[k]);
    }
    // Ensure length 2..=500
    while v.len() < 2 {
        v.push(0);
    }
    while v.len() > 500 {
        v.pop();
    }
    v
}

fn print_json(arr: &[i32]) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let vals = make_case(&mut rng, mode);
        let arr = generate_test_case(&vals);
        print_json(&arr);
    }
}