use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    ranges: Vec<i32>,
) -> (result: (i32, Vec<i32>))
    requires
        1 <= n <= 10_000,
        ranges.len() == n + 1,
        forall|i: int| 0 <= i < ranges.len() ==> 0 <= #[trigger] ranges[i] <= 100,
    ensures
        1 <= result.0 <= 10_000,
        result.1.len() == result.0 + 1,
        forall|i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 100,
{
    (n, ranges)
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
        self.state = self.state
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
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn build_ranges(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    let len = n + 1;
    let mut ranges: Vec<i32> = Vec::with_capacity(len);

    match mode {
        0 => {
            // all zeros - impossible
            for _ in 0..len {
                ranges.push(0);
            }
        }
        1 => {
            // large at index 0 covers whole garden
            for i in 0..len {
                if i == 0 {
                    let v = if n <= 100 { n as i32 } else { 100 };
                    ranges.push(v);
                } else {
                    ranges.push(0);
                }
            }
        }
        2 => {
            // all ones
            for _ in 0..len {
                ranges.push(1);
            }
        }
        3 => {
            // random small 0..3
            for _ in 0..len {
                ranges.push(rng.gen_range_i32(0, 3));
            }
        }
        4 => {
            // random 0..100
            for _ in 0..len {
                ranges.push(rng.gen_range_i32(0, 100));
            }
        }
        5 => {
            // alternating 0 and 2
            for i in 0..len {
                ranges.push(if i % 2 == 0 { 2 } else { 0 });
            }
        }
        6 => {
            // one gap in the middle
            for i in 0..len {
                if i == len / 2 {
                    ranges.push(0);
                } else {
                    ranges.push(rng.gen_range_i32(0, 5));
                }
            }
        }
        7 => {
            // max at every position
            for _ in 0..len {
                ranges.push(100);
            }
        }
        8 => {
            // single large tap at end
            for i in 0..len {
                if i == len - 1 {
                    let v = if n <= 100 { n as i32 } else { 100 };
                    ranges.push(v);
                } else {
                    ranges.push(0);
                }
            }
        }
        9 => {
            // one big in middle, zeros elsewhere (may not cover)
            for i in 0..len {
                if i == len / 2 {
                    ranges.push(100);
                } else {
                    ranges.push(0);
                }
            }
        }
        _ => {
            // sparse with many zeros
            for _ in 0..len {
                let r = rng.gen_range_i32(0, 10);
                ranges.push(if r < 7 { 0 } else { rng.gen_range_i32(1, 10) });
            }
        }
    }

    ranges
}

fn print_json(n: i32, ranges: &[i32]) {
    print!("{{\"n\":{},\"ranges\":[", n);
    for i in 0..ranges.len() {
        if i > 0 { print!(","); }
        print!("{}", ranges[i]);
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
        let n: usize = match mode {
            0 => 1 + (t % 20),
            1 => 1 + (t % 100),
            2 => 1 + (t % 50),
            3 => 2 + (t % 200),
            4 => 1 + rng.gen_range_usize(0, 500),
            5 => 2 + (t % 30),
            6 => 3 + (t % 100),
            7 => 1 + rng.gen_range_usize(0, 9999),
            8 => 1 + (t % 100),
            9 => 1 + (t % 500),
            _ => {
                let pick = t % 4;
                match pick {
                    0 => 1,
                    1 => 2,
                    2 => 10_000,
                    _ => rng.gen_range_usize(1, 10_000),
                }
            }
        };
        let n_clamped = if n < 1 { 1 } else if n > 10_000 { 10_000 } else { n };

        let ranges = build_ranges(&mut rng, mode, n_clamped);
        let n_i32 = n_clamped as i32;

        let (out_n, out_ranges) = generate_test_case(n_i32, ranges);
        print_json(out_n, &out_ranges);
    }
}