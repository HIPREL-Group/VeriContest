use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall|i: int| 0 <= i < values.len() ==> 0 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= arr.len() <= 100_000,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 1_000_000_000,
{
    let n = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            0 <= i <= n,
            arr.len() == i,
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] arr[k] <= 1_000_000_000,
            forall|k: int| 0 <= k < values.len() ==> 0 <= #[trigger] values[k] <= 1_000_000_000,
        decreases n - i,
    {
        let v = values[i];
        assert(0 <= v <= 1_000_000_000);
        arr.push(v);
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
    fn gen_i32_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build_random(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32_range(0, 1_000_000_000));
    }
    v
}

fn build_small_values(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.gen_i32_range(0, 5));
    }
    v
}

fn build_sorted(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur: i32 = 0;
    for _ in 0..n {
        let step = rng.gen_i32_range(0, 1000);
        cur = cur.saturating_add(step);
        if cur > 1_000_000_000 {
            cur = 1_000_000_000;
        }
        v.push(cur);
    }
    v
}

fn build_reverse_sorted(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        let val = (n - i) as i32;
        v.push(val.max(0));
    }
    v
}

fn build_constant(n: usize, c: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(c);
    }
    v
}

fn build_sorted_then_junk(rng: &mut Rng, n: usize) -> Vec<i32> {
    // Prefix sorted, then decreasing suffix, then sorted again
    let mut v = Vec::with_capacity(n);
    let third = n / 3;
    let mut cur: i32 = 0;
    for _ in 0..third {
        let step = rng.gen_i32_range(0, 100);
        cur = cur.saturating_add(step);
        v.push(cur);
    }
    let mut high: i32 = 1_000_000;
    for _ in third..(2 * third) {
        v.push(high);
        high = (high - rng.gen_i32_range(1, 100)).max(0);
    }
    let mut c2: i32 = 0;
    while v.len() < n {
        let step = rng.gen_i32_range(0, 100);
        c2 = c2.saturating_add(step);
        v.push(c2);
    }
    v
}

fn build_one_spike(rng: &mut Rng, n: usize) -> Vec<i32> {
    // sorted array with one big spike somewhere
    let mut v = build_sorted(rng, n);
    if n > 0 {
        let idx = rng.gen_range_usize(0, n - 1);
        v[idx] = 1_000_000_000;
    }
    v
}

fn build_one_dip(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = build_sorted(rng, n);
    if n > 0 {
        let idx = rng.gen_range_usize(0, n - 1);
        v[idx] = 0;
    }
    v
}

fn build_two_sorted_halves(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let half = n / 2;
    let mut cur: i32 = 500_000_000;
    for _ in 0..half {
        let step = rng.gen_i32_range(0, 1000);
        cur = cur.saturating_add(step);
        v.push(cur.min(1_000_000_000));
    }
    let mut c2: i32 = 0;
    while v.len() < n {
        let step = rng.gen_i32_range(0, 1000);
        c2 = c2.saturating_add(step);
        v.push(c2.min(1_000_000_000));
    }
    v
}

fn build_extremes(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        if rng.next_u64() % 2 == 0 {
            v.push(0);
        } else {
            v.push(1_000_000_000);
        }
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
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 20),
            1 => 2 + (t % 50),
            2 => 100,
            3 => 1000,
            4 => 10 + (t % 90),
            5 => 50,
            6 => if t % 3 == 0 { 100_000 } else { 500 + (t * 7) % 5000 },
            7 => 256,
            8 => 1024,
            _ => 1 + (rng.next_u64() as usize % 300),
        };
        let n = n.max(1).min(100_000);

        let values = match mode {
            0 => build_random(&mut rng, n),
            1 => build_small_values(&mut rng, n),
            2 => build_sorted(&mut rng, n),
            3 => build_reverse_sorted(n),
            4 => build_constant(n, rng.gen_i32_range(0, 1_000_000_000)),
            5 => build_sorted_then_junk(&mut rng, n),
            6 => build_one_spike(&mut rng, n),
            7 => build_one_dip(&mut rng, n),
            8 => build_two_sorted_halves(&mut rng, n),
            _ => build_extremes(&mut rng, n),
        };

        let arr = generate_test_case(&values);
        print_json(&arr);
    }
}