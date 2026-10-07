use vstd::prelude::*;

verus! {

pub fn generate_test_case(vals: &Vec<i32>) -> (arr: Vec<i32>)
    requires
        1 <= vals.len() <= 500,
        forall|i: int| 0 <= i < vals.len() ==> 0 <= #[trigger] vals[i] <= 10000,
    ensures
        1 <= arr.len() <= 500,
        forall|i: int| 0 <= i < arr.len() ==> 0 <= #[trigger] arr[i] <= 10000,
{
    let n = vals.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == vals.len(),
            1 <= n <= 500,
            0 <= i <= n,
            arr.len() == i,
            forall|k: int| 0 <= k < vals.len() ==> 0 <= #[trigger] vals[k] <= 10000,
            forall|k: int| 0 <= k < i as int ==> #[trigger] arr[k] == vals[k],
            forall|k: int| 0 <= k < i as int ==> 0 <= #[trigger] arr[k] <= 10000,
        decreases n - i,
    {
        arr.push(vals[i]);
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_vals(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // all same nonzero
            let x = rng.gen_range_i32(1, 10000);
            for _ in 0..n { v.push(x); }
        }
        2 => {
            // powers of 2 (1 bit each)
            let powers: [i32; 14] = [1,2,4,8,16,32,64,128,256,512,1024,2048,4096,8192];
            for _ in 0..n {
                v.push(powers[rng.gen_range_usize(0, 13)]);
            }
        }
        3 => {
            // sequential 0..n-1
            for i in 0..n { v.push((i as i32) % 10001); }
        }
        4 => {
            // descending
            for i in 0..n { v.push(((n - 1 - i) as i32) % 10001); }
        }
        5 => {
            // max values
            for _ in 0..n { v.push(10000); }
        }
        6 => {
            // mix of 0 and 10000
            for _ in 0..n {
                v.push(if rng.next_u64() % 2 == 0 { 0 } else { 10000 });
            }
        }
        7 => {
            // numbers with many bits set
            let many: [i32; 6] = [1023, 2047, 4095, 8191, 511, 255];
            for _ in 0..n {
                v.push(many[rng.gen_range_usize(0, 5)]);
            }
        }
        8 => {
            // single element cases will be filtered by n
            for _ in 0..n { v.push(rng.gen_range_i32(0, 10000)); }
        }
        9 => {
            // duplicates with same bit count
            let base: [i32; 4] = [3, 5, 6, 9];
            for _ in 0..n {
                v.push(base[rng.gen_range_usize(0, 3)]);
            }
        }
        _ => {
            for _ in 0..n { v.push(rng.gen_range_i32(0, 10000)); }
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
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 10),
            1 => 500,
            2 => 50,
            3 => 100,
            4 => 250,
            5 => 1,
            6 => 500,
            7 => 25,
            8 => 1 + (t % 5),
            9 => 200,
            _ => 10 + (t % 490),
        };
        let n = if n < 1 { 1 } else if n > 500 { 500 } else { n };
        let vals = make_vals(&mut rng, mode, n);
        let arr = generate_test_case(&vals);
        print_json(&arr);
    }
}