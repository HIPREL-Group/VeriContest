use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_stones(s: Seq<i32>) -> bool {
        1 <= s.len() <= 30
        && forall |i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 100
    }
}

pub fn generate_test_case(
    special1: i32,
    special2: i32,
    idx1: usize,
    idx2: usize,
    fillers: &Vec<i32>,
) -> (stones: Vec<i32>)
    requires
        1 <= special1 <= 100,
        1 <= special2 <= 100,
        fillers.len() <= 28,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
        idx1 < fillers.len() + 2,
        idx2 < fillers.len() + 2,
        idx1 != idx2,
    ensures
        1 <= stones.len() <= 30,
        forall |i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 100,
        Solution::valid_stones(stones@),
{
    let n: usize = fillers.len() + 2;
    let mut stones: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 2,
            2 <= n <= 30,
            idx1 < n,
            idx2 < n,
            idx1 != idx2,
            0 <= pos <= n,
            stones.len() == pos,
            0 <= fi <= fillers.len(),
            fi == pos - (if idx1 < pos { 1usize } else { 0usize })
                      - (if idx2 < pos { 1usize } else { 0usize }),
            1 <= special1 <= 100,
            1 <= special2 <= 100,
            fillers.len() <= 28,
            forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100,
            forall |k: int| 0 <= k < stones.len() ==> 1 <= #[trigger] stones[k] <= 100,
        decreases n - pos,
    {
        if pos == idx1 {
            stones.push(special1);
        } else if pos == idx2 {
            stones.push(special2);
        } else {
            assert(fi < fillers.len());
            stones.push(fillers[fi]);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    assert(stones.len() == n);
    assert(1 <= stones.len() <= 30);
    assert(forall |i: int| 0 <= i < stones.len() ==> 1 <= #[trigger] stones[i] <= 100);
    stones
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
            .wrapping_mul(6364136223846793005u64)
            .wrapping_add(1442695040888963407u64);
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

    fn shuffle_i32(&mut self, a: &mut [i32]) {
        let mut i = a.len();
        while i > 1 {
            i -= 1;
            let j = self.gen_range_usize(0, i);
            a.swap(i, j);
        }
    }
}

fn make_fillers(rng: &mut Rng, len: usize, mode: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(len);
    match mode {
        0 => {
            for _ in 0..len {
                v.push(1);
            }
        }
        1 => {
            for _ in 0..len {
                v.push(100);
            }
        }
        2 => {
            for i in 0..len {
                v.push(if i % 2 == 0 { 1 } else { 100 });
            }
        }
        3 => {
            for i in 0..len {
                v.push((i % 100 + 1) as i32);
            }
        }
        4 => {
            for i in 0..len {
                v.push((100 - (i % 100)) as i32);
            }
        }
        5 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 3));
            }
        }
        6 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(98, 100));
            }
        }
        7 => {
            for _ in 0..len {
                v.push(rng.gen_range_i32(1, 100));
            }
        }
        8 => {
            let base = rng.gen_range_i32(1, 100);
            for i in 0..len {
                let delta = (i % 3) as i32;
                let val = if base + delta <= 100 { base + delta } else { 100 };
                v.push(val);
            }
        }
        _ => {
            for i in 0..len {
                let x = ((i * 37 + 17) % 100 + 1) as i32;
                v.push(x);
            }
        }
    }
    v
}

fn build_case(rng: &mut Rng, mode: usize) -> Vec<i32> {
    let (n, s1, s2, idx1, idx2, filler_mode) = match mode {
        0 => (1usize, 1i32, 1i32, 0usize, 0usize, 0usize),
        1 => (2, 1, 1, 0, 1, 0),
        2 => (2, 100, 100, 0, 1, 1),
        3 => (2, 1, 100, 0, 1, 2),
        4 => (30, 1, 1, 0, 29, 0),
        5 => (30, 100, 100, 0, 29, 1),
        6 => (30, 1, 100, 14, 15, 2),
        7 => {
            let i = rng.gen_range_usize(0, 29);
            let mut j = rng.gen_range_usize(0, 28);
            if j >= i {
                j += 1;
            }
            (30, 50, 50, i, j, 7)
        }
        8 => {
            let i = rng.gen_range_usize(0, 29);
            let mut j = rng.gen_range_usize(0, 28);
            if j >= i {
                j += 1;
            }
            (30, 1, 100, i, j, 3)
        }
        9 => (29, 99, 100, 0, 28, 4),
        _ => {
            let n = rng.gen_range_usize(2, 30);
            let s1 = rng.gen_range_i32(1, 100);
            let s2 = rng.gen_range_i32(1, 100);
            let i = rng.gen_range_usize(0, n - 1);
            let mut j = rng.gen_range_usize(0, n - 2);
            if j >= i {
                j += 1;
            }
            let filler_mode = rng.gen_range_usize(0, 9);
            (n, s1, s2, i, j, filler_mode)
        }
    };

    if n == 1 {
        return vec![s1];
    }

    let filler_len = n - 2;
    let mut fillers = make_fillers(rng, filler_len, filler_mode);

    if mode == 7 || mode == 8 || mode >= 10 {
        rng.shuffle_i32(&mut fillers);
    }

    generate_test_case(s1, s2, idx1, idx2, &fillers)
}

fn print_json_line(stones: &[i32]) {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    write!(out, "{{\"stones\":[").unwrap();
    for (i, x) in stones.iter().enumerate() {
        if i > 0 {
            write!(out, ",").unwrap();
        }
        write!(out, "{}", x).unwrap();
    }
    writeln!(out, "]}}").unwrap();
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);

    for mode in 0..10usize {
        for _ in 0..12usize {
            let stones = build_case(&mut rng, mode);
            print_json_line(&stones);
        }
    }

    for _ in 0..80usize {
        let stones = build_case(&mut rng, 10);
        print_json_line(&stones);
    }
}