use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    students_bits: &Vec<u8>,
    sandwiches_bits: &Vec<u8>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        students_bits.len() == sandwiches_bits.len(),
        1 <= students_bits.len() <= 100,
        forall|i: int| 0 <= i < students_bits.len() ==> (#[trigger] students_bits[i]) <= 1,
        forall|i: int| 0 <= i < sandwiches_bits.len() ==> (#[trigger] sandwiches_bits[i]) <= 1,
    ensures
        result.0.len() == result.1.len(),
        1 <= result.0.len() <= 100,
        forall|i: int| 0 <= i < result.0.len() ==> result.0[i] == 0 || result.0[i] == 1,
        forall|i: int| 0 <= i < result.1.len() ==> result.1[i] == 0 || result.1[i] == 1,
{
    let n = students_bits.len();
    let mut students: Vec<i32> = Vec::new();
    let mut sandwiches: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            n == students_bits.len(),
            n == sandwiches_bits.len(),
            0 <= i <= n,
            students.len() == i,
            sandwiches.len() == i,
            forall|k: int| 0 <= k < students_bits.len() ==> (#[trigger] students_bits[k]) <= 1,
            forall|k: int| 0 <= k < sandwiches_bits.len() ==> (#[trigger] sandwiches_bits[k]) <= 1,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] students[k]) == 0 || students[k] == 1,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] sandwiches[k]) == 0 || sandwiches[k] == 1,
        decreases n - i,
    {
        let sb = students_bits[i];
        let tb = sandwiches_bits[i];
        let sv: i32 = if sb == 0 { 0 } else { 1 };
        let tv: i32 = if tb == 0 { 0 } else { 1 };
        students.push(sv);
        sandwiches.push(tv);
        i = i + 1;
    }

    (students, sandwiches)
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bit(&mut self) -> u8 {
        (self.next_u64() & 1) as u8
    }
}

fn build(students_bits: Vec<u8>, sandwiches_bits: Vec<u8>) -> (Vec<i32>, Vec<i32>) {
    generate_test_case(&students_bits, &sandwiches_bits)
}

fn print_json(students: &[i32], sandwiches: &[i32]) {
    print!("{{\"students\":[");
    for i in 0..students.len() {
        if i > 0 { print!(","); }
        print!("{}", students[i]);
    }
    print!("],\"sandwiches\":[");
    for i in 0..sandwiches.len() {
        if i > 0 { print!(","); }
        print!("{}", sandwiches[i]);
    }
    println!("]}}");
}

fn gen_mode(rng: &mut Rng, mode: usize, t: usize) -> (Vec<u8>, Vec<u8>) {
    let n: usize = match mode {
        0 => 1,
        1 => 2,
        2 => 100,
        3 => rng.gen_range_usize(1, 100),
        4 => rng.gen_range_usize(1, 10),
        5 => 100,
        6 => 100,
        7 => rng.gen_range_usize(1, 100),
        8 => 50 + (t % 51),
        9 => rng.gen_range_usize(1, 100),
        _ => rng.gen_range_usize(1, 100),
    };
    let mut s = Vec::with_capacity(n);
    let mut w = Vec::with_capacity(n);
    match mode {
        0 | 3 | 4 => {
            for _ in 0..n {
                s.push(rng.gen_bit());
                w.push(rng.gen_bit());
            }
        }
        1 => {
            // all zeros
            for _ in 0..n { s.push(0); w.push(0); }
        }
        2 => {
            // all ones
            for _ in 0..n { s.push(1); w.push(1); }
        }
        5 => {
            // students all 0, sandwiches all 1 (deadlock)
            for _ in 0..n { s.push(0); w.push(1); }
        }
        6 => {
            // students all 1, sandwiches all 0 (deadlock)
            for _ in 0..n { s.push(1); w.push(0); }
        }
        7 => {
            // alternating
            for i in 0..n {
                s.push((i % 2) as u8);
                w.push(((i + 1) % 2) as u8);
            }
        }
        8 => {
            // equal counts: half 0, half 1 each
            let half = n / 2;
            for i in 0..n {
                s.push(if i < half { 0 } else { 1 });
                w.push(if i % 2 == 0 { 0 } else { 1 });
            }
        }
        9 => {
            // students reversed of sandwiches
            for _ in 0..n { w.push(rng.gen_bit()); }
            for i in 0..n { s.push(w[n - 1 - i]); }
        }
        _ => {
            // skewed
            for _ in 0..n {
                s.push(if rng.next_u64() % 4 == 0 { 1 } else { 0 });
                w.push(if rng.next_u64() % 4 == 0 { 0 } else { 1 });
            }
        }
    }
    (s, w)
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
        let (sb, wb) = gen_mode(&mut rng, mode, t);
        let (students, sandwiches) = build(sb, wb);
        print_json(&students, &sandwiches);
    }
}