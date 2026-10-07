use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= values.len() <= 100,
        forall |i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 1000,
    ensures
        1 <= arr.len() <= 100,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 1000,
{
    let n = values.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == values.len(),
            1 <= n <= 100,
            arr.len() == i,
            forall |k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 1000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] arr[k] <= 1000,
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
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as i32)
    }
    fn gen_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + ((self.next_u64() % span) as usize)
    }
}

fn build(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 3,
        3 => 100,
        4 => 99,
        5 => rng.gen_usize(1, 100),
        6 => rng.gen_usize(1, 10),
        7 => 50,
        8 => { if t % 2 == 0 { 1 } else { 100 } }
        9 => rng.gen_usize(4, 20),
        _ => rng.gen_usize(1, 100),
    };

    let mut v: Vec<i32> = Vec::with_capacity(n);
    for i in 0..n {
        let x = match mode {
            0 => rng.gen_range(1, 1000),
            1 => 1,
            2 => 1000,
            3 => 1,
            4 => 1000,
            5 => rng.gen_range(1, 1000),
            6 => if i % 2 == 0 { 1 } else { 1000 },
            7 => ((i as i32) % 1000) + 1,
            8 => rng.gen_range(1, 10),
            9 => rng.gen_range(900, 1000),
            _ => rng.gen_range(1, 1000),
        };
        v.push(x);
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
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let values = build(&mut rng, mode, t);
        let arr = generate_test_case(&values);
        print_json(&arr);
    }
}