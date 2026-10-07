use vstd::prelude::*;

verus! {

pub fn generate_test_case(num_rows: i32) -> (out: i32)
    requires
        1 <= num_rows <= 30,
    ensures
        1 <= out <= 30,
{
    let out = num_rows;
    assert(1 <= out <= 30);
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
}

fn gen_next(last: &Vec<i32>) -> Vec<i32> {
    if last.is_empty() {
        return vec![1];
    }
    let mut row = Vec::with_capacity(last.len() + 1);
    row.push(1);
    let mut i = 1usize;
    while i < last.len() {
        row.push(last[i - 1] + last[i]);
        i += 1;
    }
    row.push(1);
    row
}

fn build_triangle(num_rows: i32) -> Vec<Vec<i32>> {
    let mut tri: Vec<Vec<i32>> = Vec::new();
    let mut cur = vec![1];
    let mut r = 0i32;
    while r < num_rows {
        tri.push(cur.clone());
        cur = gen_next(&cur);
        r += 1;
    }
    tri
}

fn choose_case(rng: &mut Rng, mode: usize, idx: usize) -> i32 {
    match mode {
        0 => 1,
        1 => 30,
        2 => 2,
        3 => 29,
        4 => 15,
        5 => 3 + (idx % 5) as i32,
        6 => 26 + (idx % 5) as i32,
        7 => {
            let vals = [1, 2, 5, 10, 20, 30];
            vals[idx % vals.len()]
        }
        8 => {
            let vals = [4, 6, 7, 8, 9, 11, 12, 13, 14, 16];
            vals[idx % vals.len()]
        }
        9 => rng.gen_range_i32(1, 30),
        _ => {
            if idx % 2 == 0 {
                rng.gen_range_i32(1, 3)
            } else {
                rng.gen_range_i32(28, 30)
            }
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
        let num_rows = choose_case(&mut rng, mode, t);
        let valid_num_rows = generate_test_case(num_rows);
        let _triangle = build_triangle(valid_num_rows);
        println!("{{\"num_rows\":{}}}", valid_num_rows);
    }
}