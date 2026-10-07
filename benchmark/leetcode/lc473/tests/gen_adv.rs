use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: usize,
    values: &Vec<i32>,
) -> (res: Vec<i32>)
    requires
        1 <= n <= 15,
        values.len() == n,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100_000_000,
    ensures
        1 <= res.len() <= 15,
        forall |i: int| 0 <= i < res.len() ==> 1 <= #[trigger] res[i] <= 100_000_000,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == values.len(),
            1 <= n <= 15,
            i <= n,
            out.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100_000_000,
            forall |k: int| 0 <= k < out.len() ==> out[k] == values[k],
            forall |k: int| 0 <= k < out.len() ==> 1 <= #[trigger] out[k] <= 100_000_000,
        decreases n - i,
    {
        out.push(values[i]);
        i = i + 1;
    }
    out
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
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build(n: usize, values: Vec<i32>) -> Vec<i32> {
    // Defensive clamp to satisfy preconditions
    let mut clamped: Vec<i32> = Vec::new();
    for i in 0..n {
        let v = if i < values.len() { values[i] } else { 1 };
        let v = if v < 1 { 1 } else if v > 100_000_000 { 100_000_000 } else { v };
        clamped.push(v);
    }
    generate_test_case(n, &clamped)
}

fn print_case(nums: &Vec<i32>) {
    print!("{{\"matchsticks\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn mode_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // Valid square: 4 equal sides split from smaller pieces
            let side = rng.range_i32(1, 25);
            let mut v = Vec::new();
            // 2 sticks per side, summing to side
            for _ in 0..4 {
                let a = rng.range_i32(1, side.max(2) - 1).max(1);
                let b = (side - a).max(1);
                v.push(a);
                v.push(b);
            }
            // trim or pad to <= 15
            if v.len() > 15 { v.truncate(15); }
            if v.is_empty() { v.push(1); }
            let n = v.len();
            build(n, v)
        }
        1 => {
            // [1,1,2,2,2]
            build(5, vec![1,1,2,2,2])
        }
        2 => {
            // [3,3,3,3,4]
            build(5, vec![3,3,3,3,4])
        }
        3 => {
            // length 1 edge case
            let x = rng.range_i32(1, 100_000_000);
            build(1, vec![x])
        }
        4 => {
            // length 15 with equal values
            let x = rng.range_i32(1, 100);
            let mut v = Vec::new();
            for _ in 0..15 { v.push(x); }
            build(15, v)
        }
        5 => {
            // four equal large values - valid
            let x = rng.range_i32(1, 100_000_000);
            build(4, vec![x, x, x, x])
        }
        6 => {
            // big values, total not divisible by 4
            let a = rng.range_i32(1, 100_000_000);
            let b = rng.range_i32(1, 100_000_000);
            build(5, vec![a, b, a, b, 1])
        }
        7 => {
            // many small
            let n = rng.range_usize(4, 15);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(1, 5)); }
            build(n, v)
        }
        8 => {
            // One big, rest small — likely impossible
            let mut v = Vec::new();
            v.push(100_000_000);
            let n = rng.range_usize(4, 15);
            for _ in 1..n { v.push(1); }
            build(n, v)
        }
        9 => {
            // valid with side s = sum of specific pieces
            // sides of 4 each split into pieces: 1+3, 2+2, 4, 1+1+2
            build(10, vec![1,3,2,2,4,1,1,2,2,2])
        }
        _ => {
            let n = rng.range_usize(1, 15);
            let mut v = Vec::new();
            for _ in 0..n { v.push(rng.range_i32(1, 1000)); }
            build(n, v)
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;
    for t in 0..total {
        let mode = t % modes;
        let v = mode_case(&mut rng, mode);
        print_case(&v);
    }
}