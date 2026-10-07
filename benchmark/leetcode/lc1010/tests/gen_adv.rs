use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    special1: i32,
    special2: i32,
    idx1: usize,
    idx2: usize,
    fillers: &Vec<i32>,
) -> (time: Vec<i32>)
    requires
        1 <= special1 <= 500,
        1 <= special2 <= 500,
        1 <= fillers.len() + 2 <= 60_000,
        idx1 < fillers.len() + 2,
        idx2 < fillers.len() + 2,
        idx1 != idx2,
        forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 500,
    ensures
        1 <= time.len() <= 60_000,
        forall|i: int| 0 <= i < time.len() ==> 1 <= #[trigger] time[i] <= 500,
{
    let n: usize = fillers.len() + 2;
    let mut time: Vec<i32> = Vec::new();
    let mut pos: usize = 0;
    let mut fi: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 2,
            1 <= n <= 60_000,
            idx1 < n,
            idx2 < n,
            idx1 != idx2,
            0 <= pos <= n,
            time.len() == pos,
            0 <= fi <= fillers.len(),
            fi == pos - (if idx1 < pos { 1usize } else { 0usize })
                      - (if idx2 < pos { 1usize } else { 0usize }),
            1 <= special1 <= 500,
            1 <= special2 <= 500,
            forall|i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 500,
            forall|k: int| 0 <= k < pos as int && k == idx1 as int ==> #[trigger] time[k] == special1,
            forall|k: int| 0 <= k < pos as int && k == idx2 as int ==> #[trigger] time[k] == special2,
            forall|k: int| 0 <= k < pos as int && k != idx1 as int && k != idx2 as int ==> 1 <= #[trigger] time[k] <= 500,
        decreases n - pos,
    {
        if pos == idx1 {
            time.push(special1);
        } else if pos == idx2 {
            time.push(special2);
        } else {
            assert(fi < fillers.len());
            let val = fillers[fi];
            assert(1 <= val <= 500);
            time.push(val);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    assert(time.len() == n);
    assert(1 <= time.len() <= 60_000);

    assert forall|i: int| 0 <= i < time.len() implies 1 <= #[trigger] time[i] <= 500 by {
        if i == idx1 as int {
            assert(time[i] == special1);
            assert(1 <= special1 <= 500);
        } else if i == idx2 as int {
            assert(time[i] == special2);
            assert(1 <= special2 <= 500);
        } else {
            assert(i != idx1 as int && i != idx2 as int);
            assert(1 <= time[i] <= 500);
        }
    };

    time
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        let s = if seed == 0 { 1 } else { seed };
        Self { state: s }
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
}

fn make_fillers(mode: usize, n: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(60);
            }
        }
        1 => {
            for i in 0..n {
                v.push(if i % 2 == 0 { 30 } else { 90 });
            }
        }
        2 => {
            for i in 0..n {
                v.push(match i % 3 {
                    0 => 20,
                    1 => 40,
                    _ => 80,
                });
            }
        }
        3 => {
            for i in 0..n {
                v.push((i % 500 + 1) as i32);
            }
        }
        4 => {
            for i in 0..n {
                v.push((500 - (i % 500)) as i32);
            }
        }
        5 => {
            for _ in 0..n {
                v.push(1);
            }
        }
        6 => {
            for _ in 0..n {
                v.push(500);
            }
        }
        7 => {
            for i in 0..n {
                let rem = i % 60;
                let x = if rem == 0 { 60 } else { rem as i32 };
                v.push(x);
            }
        }
        8 => {
            for i in 0..n {
                let rem = (59 - (i % 60)) as i32;
                let x = if rem == 0 { 60 } else { rem };
                v.push(x);
            }
        }
        9 => {
            for _ in 0..n {
                v.push(rng.gen_range_i32(1, 500));
            }
        }
        _ => {
            for i in 0..n {
                let base = ((i * 37 + 17) % 500 + 1) as i32;
                v.push(base);
            }
        }
    }
    v
}

fn print_json_line(time: &Vec<i32>) {
    print!("{{\"time\":[");
    for i in 0..time.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", time[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total_cases = 200usize;

    for case_id in 0..total_cases {
        let mode = case_id % 10;
        let n = match mode {
            0 => 2,
            1 => 3,
            2 => 5,
            3 => 59,
            4 => 60,
            5 => 61,
            6 => 499,
            7 => 5000,
            8 => 60_000,
            _ => rng.gen_range_usize(2, 60_000),
        };

        let special_pair = match mode {
            0 => (60, 60),
            1 => (30, 30),
            2 => (20, 40),
            3 => (1, 59),
            4 => (120, 180),
            5 => (500, 40),
            6 => (300, 60),
            7 => (150, 30),
            8 => (240, 120),
            _ => {
                let a = rng.gen_range_i32(1, 500);
                let r = a % 60;
                let b = if r == 0 { 60 } else { 60 - r };
                let bb = if b <= 500 { b } else { 60 };
                (a, bb)
            }
        };

        let idx1 = match mode {
            0 => 0,
            1 => 0,
            2 => 0,
            3 => n - 2,
            4 => 0,
            5 => n / 2,
            6 => rng.gen_range_usize(0, n - 1),
            7 => 0,
            8 => n - 1,
            _ => rng.gen_range_usize(0, n - 1),
        };

        let mut idx2 = match mode {
            0 => 1,
            1 => 1,
            2 => 1,
            3 => n - 1,
            4 => n - 1,
            5 => if idx1 == 0 { 1 } else { 0 },
            6 => {
                let mut j = rng.gen_range_usize(0, n - 2);
                if j >= idx1 {
                    j += 1;
                }
                j
            }
            7 => n - 1,
            8 => 0,
            _ => {
                let mut j = rng.gen_range_usize(0, n - 2);
                if j >= idx1 {
                    j += 1;
                }
                j
            }
        };

        if idx1 == idx2 {
            idx2 = (idx1 + 1) % n;
        }

        let fillers = make_fillers(mode, n - 2, &mut rng);
        let time = generate_test_case(special_pair.0, special_pair.1, idx1, idx2, &fillers);
        print_json_line(&time);
    }
}