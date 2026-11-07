use vstd::prelude::*;

verus! {

pub struct Gen;

impl Gen {
    pub open spec fn in_range_1_1000(x: i32) -> bool {
        1 <= x as int && x as int <= 1000
    }
}

pub fn generate_test_case(
    peak: i32,
    valley: i32,
    len: usize,
    peak_on_even: bool,
    noise: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= len <= 1000,
        1 <= peak as int <= 1000,
        1 <= valley as int <= 1000,
        valley < peak,
        noise.len() == len,
        forall|i: int| 0 <= i < noise.len() ==> 1 <= #[trigger] noise[i] as int <= 1000,
    ensures
        1 <= nums@.len() <= 1000,
        forall |i: int| 0 <= i < nums@.len() ==> 1 <= #[trigger] nums@[i] <= 1000,
{
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < len
        invariant
            len <= 1000,
            0 <= i <= len,
            out.len() == i,
            1 <= peak as int <= 1000,
            1 <= valley as int <= 1000,
            valley < peak,
            noise.len() == len,
            forall|k: int| 0 <= k < noise.len() ==> 1 <= #[trigger] noise[k] as int <= 1000,
            forall|k: int| 0 <= k < out.len() ==> 1 <= #[trigger] out[k] as int <= 1000,
        decreases len - i,
    {
        let use_peak = if peak_on_even { i % 2 == 0 } else { i % 2 == 1 };
        let v = if use_peak {
            peak
        } else {
            let nv = noise[i];
            if nv < peak { nv } else { valley }
        };
        assert(1 <= v as int && v as int <= 1000);
        out.push(v);
        i = i + 1;
    }

    proof {
        assert(out.len() == len);
    }

    out
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 0
    }
}

fn make_noise(len: usize, mode: usize, rng: &mut Rng, peak: i32, valley: i32) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    match mode {
        0 => {
            for _ in 0..len {
                v.push(peak - 1);
            }
        }
        1 => {
            for _ in 0..len {
                v.push(valley);
            }
        }
        2 => {
            for i in 0..len {
                v.push(if i % 2 == 0 { 1 } else { 1000.min(peak - 1) });
            }
        }
        3 => {
            for i in 0..len {
                v.push(if i % 3 == 0 { peak - 1 } else { valley });
            }
        }
        4 => {
            for i in 0..len {
                let x = 1 + ((i * 37 + 17) % 1000) as i32;
                v.push(x.min(peak - 1).max(1));
            }
        }
        5 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, peak - 1));
            }
        }
        6 => {
            for i in 0..len {
                let x = if i % 4 == 0 { peak - 1 } else if i % 4 == 1 { valley } else if i % 4 == 2 { 1 } else { (peak / 2).max(1) };
                v.push(x);
            }
        }
        7 => {
            for i in 0..len {
                let x = if i + 1 == len { peak - 1 } else { valley };
                v.push(x);
            }
        }
        8 => {
            for i in 0..len {
                let x = if i == 0 { peak - 1 } else { 1 + ((len - i) % (peak as usize - 1).max(1)) as i32 };
                v.push(x.min(peak - 1).max(1));
            }
        }
        9 => {
            for i in 0..len {
                let x = match i % 5 {
                    0 => 1,
                    1 => 2.min(peak - 1),
                    2 => (peak - 1).max(1),
                    3 => valley,
                    _ => ((peak + valley) / 2).clamp(1, peak - 1),
                };
                v.push(x);
            }
        }
        _ => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 1000));
            }
        }
    }
    v
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
    let total = 220usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let len = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => 4,
            4 => 5,
            5 => 17,
            6 => 64,
            7 => 127,
            8 => 511,
            9 => 999,
            _ => 1000,
        };

        let (peak, valley, peak_on_even) = match mode {
            0 => (2, 1, true),
            1 => (1000, 999, false),
            2 => (1000, 1, true),
            3 => (500, 499, false),
            4 => (3, 1, rng.gen_bool()),
            5 => (1000, 1, rng.gen_bool()),
            6 => (700, 350, true),
            7 => (10, 9, false),
            8 => (999, 1, true),
            9 => (1000, 500, false),
            _ => {
                let peak = rng.gen_range_i32(2, 1000);
                let valley = rng.gen_range_i32(1, peak - 1);
                (peak, valley, rng.gen_bool())
            }
        };

        let noise = make_noise(len, mode, &mut rng, peak, valley);
        let nums = generate_test_case(peak, valley, len, peak_on_even, &noise);
        print_json(&nums);
    }
}