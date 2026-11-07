use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    pairs: &Vec<(u8, u8)>,
) -> (nums: Vec<i32>)
    requires
        1 <= pairs.len() <= 50,
        forall|i: int| 0 <= i < pairs.len() ==> 1 <= (#[trigger] pairs[i]).0 <= 100,
        forall|i: int| 0 <= i < pairs.len() ==> 1 <= (#[trigger] pairs[i]).1 <= 100,
    ensures
        2 <= nums.len() <= 100,
        nums.len() % 2 == 0,
        nums.len() == 2 * pairs.len(),
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
{
    let mut nums: Vec<i32> = Vec::new();
    let n = pairs.len();
    let mut i: usize = 0;

    while i < n
        invariant
            n == pairs.len(),
            0 <= i <= n,
            1 <= n <= 50,
            nums.len() == 2 * i,
            forall|k: int| 0 <= k < pairs.len() ==> 1 <= (#[trigger] pairs[k]).0 <= 100,
            forall|k: int| 0 <= k < pairs.len() ==> 1 <= (#[trigger] pairs[k]).1 <= 100,
            forall|k: int| 0 <= k < nums.len() ==> 1 <= #[trigger] nums[k] <= 100,
        decreases n - i,
    {
        let p = pairs[i];
        let freq: i32 = p.0 as i32;
        let val: i32 = p.1 as i32;
        nums.push(freq);
        nums.push(val);
        i = i + 1;
    }

    nums
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

    fn gen_u8(&mut self, lo: u8, hi: u8) -> u8 {
        let span = (hi - lo + 1) as u64;
        (lo as u64 + self.next_u64() % span) as u8
    }
}

fn make_pairs_mode(rng: &mut Rng, mode: usize) -> Vec<(u8, u8)> {
    match mode {
        0 => {
            // minimum length
            let f = rng.gen_u8(1, 100);
            let v = rng.gen_u8(1, 100);
            vec![(f, v)]
        }
        1 => {
            // maximum length
            let mut p = Vec::with_capacity(50);
            for _ in 0..50 {
                p.push((rng.gen_u8(1, 100), rng.gen_u8(1, 100)));
            }
            p
        }
        2 => {
            // all frequencies 1
            let len = rng.gen_range_usize(1, 50);
            let mut p = Vec::with_capacity(len);
            for _ in 0..len {
                p.push((1u8, rng.gen_u8(1, 100)));
            }
            p
        }
        3 => {
            // all frequencies 100
            let len = rng.gen_range_usize(1, 50);
            let mut p = Vec::with_capacity(len);
            for _ in 0..len {
                p.push((100u8, rng.gen_u8(1, 100)));
            }
            p
        }
        4 => {
            // all values same
            let len = rng.gen_range_usize(1, 50);
            let v = rng.gen_u8(1, 100);
            let mut p = Vec::with_capacity(len);
            for _ in 0..len {
                p.push((rng.gen_u8(1, 100), v));
            }
            p
        }
        5 => {
            // freq=1 val=1 everywhere
            let len = rng.gen_range_usize(1, 50);
            let mut p = Vec::with_capacity(len);
            for _ in 0..len {
                p.push((1u8, 1u8));
            }
            p
        }
        6 => {
            // freq=100 val=100
            let len = rng.gen_range_usize(1, 50);
            let mut p = Vec::with_capacity(len);
            for _ in 0..len {
                p.push((100u8, 100u8));
            }
            p
        }
        7 => {
            // single pair with max freq
            vec![(100u8, rng.gen_u8(1, 100))]
        }
        8 => {
            // boundaries of freq/val
            let len = rng.gen_range_usize(1, 50);
            let mut p = Vec::with_capacity(len);
            for i in 0..len {
                let f = if i % 2 == 0 { 1u8 } else { 100u8 };
                let v = if i % 2 == 0 { 100u8 } else { 1u8 };
                p.push((f, v));
            }
            p
        }
        9 => {
            // like example 1: [1,2,3,4]
            vec![(1u8, 2u8), (3u8, 4u8)]
        }
        _ => {
            // random typical
            let len = rng.gen_range_usize(1, 50);
            let mut p = Vec::with_capacity(len);
            for _ in 0..len {
                p.push((rng.gen_u8(1, 100), rng.gen_u8(1, 100)));
            }
            p
        }
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
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
        let pairs = make_pairs_mode(&mut rng, mode);
        let nums = generate_test_case(&pairs);
        print_json(&nums);
    }
}