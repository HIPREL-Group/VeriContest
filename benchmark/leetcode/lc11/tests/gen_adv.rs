use vstd::prelude::*;

verus! {

pub struct Gen;

impl Gen {
    pub open spec fn valid_height(x: i32) -> bool {
        0 <= x <= 10_000
    }
}

pub fn generate_test_case(
    left_height: i32,
    right_height: i32,
    idx_left: usize,
    idx_right: usize,
    fillers: &Vec<i32>,
) -> (height: Vec<i32>)
    requires
        0 <= left_height <= 10_000,
        0 <= right_height <= 10_000,
        2 <= fillers.len() + 2 <= 100_000,
        idx_left < fillers.len() + 2,
        idx_right < fillers.len() + 2,
        idx_left != idx_right,
        forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 10_000,
    ensures
        2 <= height.len() <= 100_000,
        forall|i: int| 0 <= i < height.len() ==> 0 <= #[trigger] height[i] <= 10_000,
{
    let n: usize = fillers.len() + 2;
    let mut height: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 2,
            2 <= n <= 100_000,
            0 <= pos <= n,
            height.len() == pos,
            idx_left < n,
            idx_right < n,
            idx_left != idx_right,
            0 <= fi <= fillers.len(),
            fi == pos - (if idx_left < pos { 1usize } else { 0usize })
                      - (if idx_right < pos { 1usize } else { 0usize }),
            0 <= left_height <= 10_000,
            0 <= right_height <= 10_000,
            forall|i: int| 0 <= i < fillers.len() ==> 0 <= #[trigger] fillers[i] <= 10_000,
            forall|k: int| 0 <= k < pos as int && k == idx_left as int ==> #[trigger] height[k] == left_height,
            forall|k: int| 0 <= k < pos as int && k == idx_right as int ==> #[trigger] height[k] == right_height,
            forall|k: int|
                0 <= k < pos as int && k != idx_left as int && k != idx_right as int
                    ==> 0 <= #[trigger] height[k] <= 10_000,
        decreases n - pos,
    {
        if pos == idx_left {
            height.push(left_height);
        } else if pos == idx_right {
            height.push(right_height);
        } else {
            assert(fi < fillers.len());
            height.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    height
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
}

fn choose_distinct_indices(rng: &mut Rng, n: usize) -> (usize, usize) {
    let i = rng.gen_range_usize(0, n - 1);
    let mut j = rng.gen_range_usize(0, n - 2);
    if j >= i {
        j += 1;
    }
    (i, j)
}

fn make_fillers(count: usize, mode: usize, rng: &mut Rng) -> Vec<i32> {
    let mut v = Vec::with_capacity(count);
    match mode {
        0 => {
            for _ in 0..count {
                v.push(0);
            }
        }
        1 => {
            for _ in 0..count {
                v.push(10_000);
            }
        }
        2 => {
            for i in 0..count {
                v.push((i % 10_001) as i32);
            }
        }
        3 => {
            for i in 0..count {
                v.push((10_000 - (i % 10_001)) as i32);
            }
        }
        4 => {
            for i in 0..count {
                v.push(if i % 2 == 0 { 0 } else { 10_000 });
            }
        }
        5 => {
            let mid = 5000;
            for i in 0..count {
                let d = (i % 101) as i32;
                v.push(if i % 2 == 0 { mid + d } else { mid - d });
            }
        }
        6 => {
            for _ in 0..count {
                v.push(rng.gen_range_i32(0, 3));
            }
        }
        7 => {
            for _ in 0..count {
                v.push(rng.gen_range_i32(9997, 10_000));
            }
        }
        8 => {
            for _ in 0..count {
                v.push(rng.gen_range_i32(0, 10_000));
            }
        }
        9 => {
            for i in 0..count {
                let x = ((i as u64 * i as u64 + 17 * i as u64 + 23) % 10_001) as i32;
                v.push(x);
            }
        }
        _ => {
            for i in 0..count {
                let block = (i / 7) % 5;
                let val = match block {
                    0 => 0,
                    1 => 1,
                    2 => 9999,
                    3 => 10_000,
                    _ => 5000,
                };
                v.push(val);
            }
        }
    }
    v
}

fn build_case(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    let n = match mode {
        0 => 2,
        1 => 3,
        2 => 4,
        3 => 5,
        4 => 17,
        5 => 64,
        6 => 257,
        7 => 1024,
        8 => 4096,
        9 => 100_000,
        _ => 2 + (t * 7919 % 99999),
    };

    let (idx_left, idx_right) = match mode {
        0 => (0, 1),
        1 => (0, n - 1),
        2 => (n / 2 - 1, n / 2),
        3 => (0, n / 2),
        4 => (1, n - 2),
        5 => (n - 2, n - 1),
        6 => choose_distinct_indices(rng, n),
        7 => (0, n - 1),
        8 => (n / 3, 2 * n / 3),
        9 => (1, n - 2),
        _ => choose_distinct_indices(rng, n),
    };

    let (left_height, right_height) = match mode {
        0 => (0, 0),
        1 => (10_000, 10_000),
        2 => (0, 10_000),
        3 => (1, 1),
        4 => (123, 9876),
        5 => (10_000, 0),
        6 => (rng.gen_range_i32(0, 10_000), rng.gen_range_i32(0, 10_000)),
        7 => (9999, 10_000),
        8 => (5000, 5000),
        9 => (10_000, 10_000),
        _ => (rng.gen_range_i32(0, 10_000), rng.gen_range_i32(0, 10_000)),
    };

    let fillers = make_fillers(n - 2, mode, rng);
    generate_test_case(left_height, right_height, idx_left, idx_right, &fillers)
}

fn print_json(height: &[i32]) {
    print!("{{\"height\":[");
    for i in 0..height.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", height[i]);
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
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let height = build_case(&mut rng, mode, t);
        print_json(&height);
    }
}