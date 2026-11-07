use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    filler: &Vec<i32>,
) -> (arr: Vec<i32>)
    requires
        1 <= filler.len() <= 50,
        forall|i: int| 0 <= i < filler.len() ==> -1000 <= #[trigger] filler[i] <= 1000,
    ensures
        1 <= arr.len() <= 50,
        forall|i: int| 0 <= i < arr.len() ==> -1000 <= #[trigger] arr[i] <= 1000,
{
    let n = filler.len();
    let mut arr: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == filler.len(),
            1 <= n <= 50,
            0 <= i <= n,
            arr.len() == i,
            forall|k: int| 0 <= k < filler.len() ==> -1000 <= #[trigger] filler[k] <= 1000,
            forall|k: int| 0 <= k < i as int ==> arr[k] == filler[k],
            forall|k: int| 0 <= k < i as int ==> -1000 <= #[trigger] arr[k] <= 1000,
        decreases n - i,
    {
        arr.push(filler[i]);
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_vec(v: Vec<i32>) -> Vec<i32> {
    v.into_iter()
        .map(|x| if x < -1000 { -1000 } else if x > 1000 { 1000 } else { x })
        .collect()
}

fn print_json(arr: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..arr.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", arr[i]);
    }
    println!("]}}");
}

fn gen_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // singleton
            vec![rng.gen_range_i32(-1000, 1000)]
        }
        1 => {
            // already sorted ascending
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            let mut cur = rng.gen_range_i32(-1000, -500);
            for _ in 0..n {
                v.push(cur);
                let inc = rng.gen_range_i32(0, 30);
                cur = (cur as i64 + inc as i64).min(1000) as i32;
            }
            v
        }
        2 => {
            // strictly decreasing
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            let mut cur = rng.gen_range_i32(500, 1000);
            for _ in 0..n {
                v.push(cur);
                let dec = rng.gen_range_i32(1, 30);
                cur = (cur as i64 - dec as i64).max(-1000) as i32;
            }
            v
        }
        3 => {
            // all same value
            let n = rng.gen_range_usize(1, 50);
            let val = rng.gen_range_i32(-1000, 1000);
            vec![val; n]
        }
        4 => {
            // all extreme values
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                let pick = rng.next_u64() % 3;
                v.push(match pick { 0 => -1000, 1 => 1000, _ => 0 });
            }
            v
        }
        5 => {
            // length boundary - max 50
            let mut v = Vec::with_capacity(50);
            for _ in 0..50 {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
            v
        }
        6 => {
            // negatives only
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, -1));
            }
            v
        }
        7 => {
            // alternating
            let n = rng.gen_range_usize(2, 50);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 2 == 0 {
                    v.push(rng.gen_range_i32(500, 1000));
                } else {
                    v.push(rng.gen_range_i32(-1000, -500));
                }
            }
            v
        }
        8 => {
            // example-like: [5,2,3,1]
            vec![5, 2, 3, 1]
        }
        9 => {
            // small sizes 1..5
            let n = rng.gen_range_usize(1, 5);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-10, 10));
            }
            v
        }
        _ => {
            // random
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                v.push(rng.gen_range_i32(-1000, 1000));
            }
            v
        }
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let filler = build_vec(gen_mode(&mut rng, mode));
        let filler = if filler.is_empty() { vec![0i32] } else { filler };
        let filler = if filler.len() > 50 { filler[..50].to_vec() } else { filler };
        let arr = generate_test_case(&filler);
        print_json(&arr);
    }
}