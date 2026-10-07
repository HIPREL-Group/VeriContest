use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    apple_vals: &Vec<i32>,
    capacity_vals: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= apple_vals.len() <= 50,
        1 <= capacity_vals.len() <= 50,
        forall |i: int| 0 <= i < apple_vals.len() ==> 1 <= #[trigger] apple_vals[i] <= 50,
        forall |i: int| 0 <= i < capacity_vals.len() ==> 1 <= #[trigger] capacity_vals[i] <= 50,
        Solution::sum_prefix(apple_vals@, apple_vals.len() as int) <= Solution::sum_prefix(capacity_vals@, capacity_vals.len() as int),
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1.len() <= 50,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 50,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 50,
        Solution::sum_prefix(result.0@, result.0.len() as int) <= Solution::sum_prefix(result.1@, result.1.len() as int),
        result.0@ == apple_vals@,
        result.1@ == capacity_vals@,
{
    let mut a: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < apple_vals.len()
        invariant
            0 <= i <= apple_vals.len(),
            a.len() == i,
            forall |k: int| 0 <= k < i as int ==> a[k] == apple_vals[k],
        decreases apple_vals.len() - i,
    {
        a.push(apple_vals[i]);
        i += 1;
    }
    assert(a@ =~= apple_vals@);

    let mut c: Vec<i32> = Vec::new();
    let mut j: usize = 0;
    while j < capacity_vals.len()
        invariant
            0 <= j <= capacity_vals.len(),
            c.len() == j,
            forall |k: int| 0 <= k < j as int ==> c[k] == capacity_vals[k],
        decreases capacity_vals.len() - j,
    {
        c.push(capacity_vals[j]);
        j += 1;
    }
    assert(c@ =~= capacity_vals@);

    (a, c)
}

pub struct Solution;

impl Solution {
    pub open spec fn sum_prefix(s: Seq<i32>, n: int) -> int
        decreases n,
    {
        if n <= 0 {
            0
        } else if n > s.len() {
            Self::sum_prefix(s, s.len() as int)
        } else {
            Self::sum_prefix(s, n - 1) + s[n - 1] as int
        }
    }
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
}

fn compute_sum(v: &Vec<i32>) -> i64 {
    let mut s: i64 = 0;
    for &x in v {
        s += x as i64;
    }
    s
}

fn build_apple_capacity(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    loop {
        let (apple, capacity) = match mode {
            0 => {
                // small random
                let n = rng.gen_range_usize(1, 5);
                let m = rng.gen_range_usize(1, 5);
                let mut a = Vec::new();
                for _ in 0..n {
                    a.push(rng.gen_range_usize(1, 10) as i32);
                }
                let mut c = Vec::new();
                for _ in 0..m {
                    c.push(rng.gen_range_usize(1, 10) as i32);
                }
                (a, c)
            }
            1 => {
                // max sizes
                let mut a = Vec::new();
                for _ in 0..50 {
                    a.push(rng.gen_range_usize(1, 50) as i32);
                }
                let mut c = Vec::new();
                for _ in 0..50 {
                    c.push(rng.gen_range_usize(1, 50) as i32);
                }
                (a, c)
            }
            2 => {
                // all max
                let a = vec![50i32; 50];
                let c = vec![50i32; 50];
                (a, c)
            }
            3 => {
                // minimal
                let a = vec![1i32];
                let c = vec![1i32];
                (a, c)
            }
            4 => {
                // tiny apples, big capacity
                let n = rng.gen_range_usize(1, 50);
                let m = rng.gen_range_usize(1, 50);
                let a = vec![1i32; n];
                let c = vec![50i32; m];
                (a, c)
            }
            5 => {
                // one box covers all
                let n = rng.gen_range_usize(1, 50);
                let mut a = Vec::new();
                for _ in 0..n {
                    a.push(rng.gen_range_usize(1, 50) as i32);
                }
                let total: i64 = a.iter().map(|&x| x as i64).sum();
                let mut c = Vec::new();
                c.push(total.min(50) as i32);
                let m = rng.gen_range_usize(1, 49);
                for _ in 0..m {
                    c.push(rng.gen_range_usize(1, 50) as i32);
                }
                (a, c)
            }
            6 => {
                // tight fit
                let n = rng.gen_range_usize(1, 20);
                let m = rng.gen_range_usize(1, 20);
                let mut a = Vec::new();
                for _ in 0..n {
                    a.push(rng.gen_range_usize(1, 5) as i32);
                }
                let mut c = Vec::new();
                for _ in 0..m {
                    c.push(rng.gen_range_usize(1, 5) as i32);
                }
                (a, c)
            }
            7 => {
                // sorted ascending capacity
                let n = rng.gen_range_usize(1, 10);
                let mut a = Vec::new();
                for _ in 0..n {
                    a.push(rng.gen_range_usize(1, 20) as i32);
                }
                let m = rng.gen_range_usize(5, 50);
                let mut c: Vec<i32> = Vec::new();
                for i in 0..m {
                    c.push(((i % 50) + 1) as i32);
                }
                (a, c)
            }
            8 => {
                // descending
                let n = rng.gen_range_usize(1, 10);
                let mut a = Vec::new();
                for _ in 0..n {
                    a.push(rng.gen_range_usize(1, 20) as i32);
                }
                let m = rng.gen_range_usize(5, 50);
                let mut c: Vec<i32> = Vec::new();
                for i in 0..m {
                    c.push((50 - (i % 50)) as i32);
                }
                (a, c)
            }
            9 => {
                // equal values
                let n = rng.gen_range_usize(1, 50);
                let m = rng.gen_range_usize(1, 50);
                let v = rng.gen_range_usize(1, 50) as i32;
                let a = vec![v; n];
                let c = vec![v; m];
                (a, c)
            }
            _ => {
                let n = rng.gen_range_usize(1, 50);
                let m = rng.gen_range_usize(1, 50);
                let mut a = Vec::new();
                for _ in 0..n {
                    a.push(rng.gen_range_usize(1, 50) as i32);
                }
                let mut c = Vec::new();
                for _ in 0..m {
                    c.push(rng.gen_range_usize(1, 50) as i32);
                }
                (a, c)
            }
        };

        // Check feasibility: sum(apple) <= sum(capacity)
        let sum_a = compute_sum(&apple);
        let sum_c = compute_sum(&capacity);
        if sum_a <= sum_c
            && apple.len() >= 1 && apple.len() <= 50
            && capacity.len() >= 1 && capacity.len() <= 50
            && apple.iter().all(|&x| x >= 1 && x <= 50)
            && capacity.iter().all(|&x| x >= 1 && x <= 50)
        {
            return (apple, capacity);
        }
        // else: try again with fallback - pad capacity
        // simplest: add max caps until feasible, if m < 50
        let mut apple2 = apple;
        let mut capacity2 = capacity;
        while compute_sum(&apple2) > compute_sum(&capacity2) && capacity2.len() < 50 {
            capacity2.push(50);
        }
        // if still infeasible, shrink apple to 1
        if compute_sum(&apple2) > compute_sum(&capacity2) {
            apple2 = vec![1i32];
        }
        let sum_a2 = compute_sum(&apple2);
        let sum_c2 = compute_sum(&capacity2);
        if sum_a2 <= sum_c2
            && apple2.len() >= 1 && apple2.len() <= 50
            && capacity2.len() >= 1 && capacity2.len() <= 50
            && apple2.iter().all(|&x| x >= 1 && x <= 50)
            && capacity2.iter().all(|&x| x >= 1 && x <= 50)
        {
            return (apple2, capacity2);
        }
    }
}

fn print_json(apple: &[i32], capacity: &[i32]) {
    print!("{{\"apple\":[");
    for i in 0..apple.len() {
        if i > 0 { print!(","); }
        print!("{}", apple[i]);
    }
    print!("],\"capacity\":[");
    for i in 0..capacity.len() {
        if i > 0 { print!(","); }
        print!("{}", capacity[i]);
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
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (apple, capacity) = build_apple_capacity(&mut rng, mode);
        // Call the verified generator to assemble.
        let (a, c) = generate_test_case(&apple, &capacity);
        print_json(&a, &c);
    }
}