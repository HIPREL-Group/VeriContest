use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    seats: Vec<i32>,
    students: Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= seats.len() <= 100,
        students.len() == seats.len(),
        forall |i: int| 0 <= i < seats.len() ==> 1 <= #[trigger] seats[i] <= 100,
        forall |i: int| 0 <= i < students.len() ==> 1 <= #[trigger] students[i] <= 100,
    ensures
        1 <= result.0.len() <= 100,
        result.1.len() == result.0.len(),
        result.0@.len() <= 100,
        result.1@.len() == result.0@.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 100,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 100,
{
    (seats, students)
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn build_random(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut s = Vec::with_capacity(n);
    let mut t = Vec::with_capacity(n);
    for _ in 0..n {
        s.push(rng.gen_range_i32(1, 100));
        t.push(rng.gen_range_i32(1, 100));
    }
    (s, t)
}

fn build_all_same(n: usize, v: i32) -> (Vec<i32>, Vec<i32>) {
    let s = vec![v; n];
    let t = vec![v; n];
    (s, t)
}

fn build_min_max(n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut s = Vec::with_capacity(n);
    let mut t = Vec::with_capacity(n);
    for i in 0..n {
        if i % 2 == 0 {
            s.push(1);
            t.push(100);
        } else {
            s.push(100);
            t.push(1);
        }
    }
    (s, t)
}

fn build_sorted(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut s: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
    let mut t: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
    s.sort();
    t.sort();
    (s, t)
}

fn build_reverse(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let mut s: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
    let mut t: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
    s.sort();
    t.sort();
    t.reverse();
    (s, t)
}

fn build_clustered(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let base = rng.gen_range_i32(1, 100);
    let lo = if base > 5 { base - 5 } else { 1 };
    let hi = if base < 96 { base + 5 } else { 100 };
    let mut s = Vec::with_capacity(n);
    let mut t = Vec::with_capacity(n);
    for _ in 0..n {
        s.push(rng.gen_range_i32(lo, hi));
        t.push(rng.gen_range_i32(lo, hi));
    }
    (s, t)
}

fn build_identical(rng: &mut Rng, n: usize) -> (Vec<i32>, Vec<i32>) {
    let v: Vec<i32> = (0..n).map(|_| rng.gen_range_i32(1, 100)).collect();
    (v.clone(), v)
}

fn build_at_boundary(n: usize) -> (Vec<i32>, Vec<i32>) {
    let s = vec![1; n];
    let t = vec![100; n];
    (s, t)
}

fn build_single(rng: &mut Rng) -> (Vec<i32>, Vec<i32>) {
    let s = vec![rng.gen_range_i32(1, 100)];
    let t = vec![rng.gen_range_i32(1, 100)];
    (s, t)
}

fn print_json(seats: &[i32], students: &[i32]) {
    print!("{{\"seats\":[");
    for i in 0..seats.len() {
        if i > 0 { print!(","); }
        print!("{}", seats[i]);
    }
    print!("],\"students\":[");
    for i in 0..students.len() {
        if i > 0 { print!(","); }
        print!("{}", students[i]);
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

    for t in 0..total {
        let mode = t % 10;
        let n = match mode {
            0 => rng.gen_range_usize(1, 10),
            1 => rng.gen_range_usize(1, 100),
            2 => 100,
            3 => 1,
            4 => rng.gen_range_usize(2, 20),
            5 => rng.gen_range_usize(2, 50),
            6 => rng.gen_range_usize(2, 100),
            7 => rng.gen_range_usize(1, 30),
            8 => 100,
            _ => rng.gen_range_usize(1, 100),
        };

        let (s, st) = match mode {
            0 => build_random(&mut rng, n),
            1 => build_random(&mut rng, n),
            2 => build_all_same(n, rng.gen_range_i32(1, 100)),
            3 => build_single(&mut rng),
            4 => build_min_max(n),
            5 => build_sorted(&mut rng, n),
            6 => build_reverse(&mut rng, n),
            7 => build_clustered(&mut rng, n),
            8 => build_at_boundary(n),
            _ => build_identical(&mut rng, n),
        };

        let (seats, students) = generate_test_case(s, st);
        print_json(&seats, &students);
    }
}