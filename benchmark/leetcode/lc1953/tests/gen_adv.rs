use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (milestones: Vec<i32>)
    requires
        1 <= values.len() <= 100_000,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1_000_000_000,
    ensures
        1 <= milestones.len() <= 100_000,
        forall |i: int| 0 <= i < milestones.len() ==> 1 <= #[trigger] milestones[i] <= 1_000_000_000,
{
    let mut res: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    let n = values.len();
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            res.len() == i,
            1 <= n <= 100_000,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1_000_000_000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] res[k] <= 1_000_000_000,
        decreases n - i,
    {
        res.push(values[i]);
        i = i + 1;
    }
    res
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
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn gen_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_values(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_usize(1, 10);
            (0..n).map(|_| rng.gen_i32(1, 10)).collect()
        }
        1 => {
            // single element
            vec![rng.gen_i32(1, 1_000_000_000)]
        }
        2 => {
            // all ones
            let n = rng.gen_usize(1, 100);
            vec![1; n]
        }
        3 => {
            // one huge element dominating
            let n = rng.gen_usize(2, 10);
            let mut v: Vec<i32> = (0..n-1).map(|_| rng.gen_i32(1, 5)).collect();
            v.push(1_000_000_000);
            v
        }
        4 => {
            // two elements equal
            let x = rng.gen_i32(1, 1_000_000_000);
            vec![x, x]
        }
        5 => {
            // two elements: max and 1
            vec![1_000_000_000, 1]
        }
        6 => {
            // large n all ones
            vec![1; 100_000]
        }
        7 => {
            // large n with big values
            let n = rng.gen_usize(1000, 100_000);
            (0..n).map(|_| rng.gen_i32(1, 1_000_000_000)).collect()
        }
        8 => {
            // one dominant in large array
            let n = rng.gen_usize(2, 1000);
            let mut v: Vec<i32> = (0..n-1).map(|_| 1).collect();
            v.push(1_000_000_000);
            v
        }
        9 => {
            // balanced big
            let n = rng.gen_usize(2, 50);
            vec![500_000_000; n]
        }
        _ => {
            let n = rng.gen_usize(1, 200);
            (0..n).map(|_| rng.gen_i32(1, 1000 + (t as i32))).collect()
        }
    }
}

fn print_json(milestones: &[i32]) {
    print!("{{\"milestones\":[");
    for i in 0..milestones.len() {
        if i > 0 { print!(","); }
        print!("{}", milestones[i]);
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
        let values = make_values(&mut rng, mode, t);
        let milestones = generate_test_case(&values);
        print_json(&milestones);
    }
}