use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    n: i32,
    roll_max: Vec<i32>,
) -> (result: (i32, Vec<i32>))
    requires
        1 <= n <= 5000,
        roll_max.len() == 6,
        forall |j: int| 0 <= j < 6 ==> 1 <= #[trigger] roll_max[j] <= 15,
    ensures
        1 <= result.0 <= 5000,
        result.1.len() == 6,
        forall |j: int| 0 <= j < 6 ==> 1 <= #[trigger] result.1[j] <= 15,
{
    (n, roll_max)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn build_roll_max(rng: &mut Rng, pattern: usize) -> Vec<i32> {
    let mut rm: Vec<i32> = Vec::with_capacity(6);
    match pattern {
        0 => { for _ in 0..6 { rm.push(1); } }
        1 => { for _ in 0..6 { rm.push(15); } }
        2 => { for _ in 0..6 { rm.push(2); } }
        3 => { for _ in 0..6 { rm.push(3); } }
        4 => {
            rm.push(1); rm.push(1); rm.push(2); rm.push(2); rm.push(2); rm.push(3);
        }
        5 => {
            rm.push(1); rm.push(1); rm.push(1); rm.push(2); rm.push(2); rm.push(3);
        }
        6 => {
            rm.push(1); rm.push(15); rm.push(1); rm.push(15); rm.push(1); rm.push(15);
        }
        7 => {
            rm.push(15); rm.push(1); rm.push(15); rm.push(1); rm.push(15); rm.push(1);
        }
        8 => {
            rm.push(5); rm.push(5); rm.push(5); rm.push(5); rm.push(5); rm.push(5);
        }
        _ => {
            for _ in 0..6 {
                rm.push(rng.gen_range_i32(1, 15));
            }
        }
    }
    rm
}

fn print_json(n: i32, rm: &[i32]) {
    print!("{{\"n\": {}, \"roll_max\": [", n);
    for i in 0..rm.len() {
        if i > 0 { print!(","); }
        print!("{}", rm[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let total = 200usize;

    // A few fixed edge-case tests
    let fixed: Vec<(i32, usize)> = vec![
        (1, 0), (1, 1), (2, 4), (2, 0), (3, 5),
        (5000, 1), (5000, 0), (5000, 2), (5000, 8),
        (1, 1), (2, 1), (3, 0), (100, 4), (1000, 3),
        (4999, 1), (4998, 8),
    ];

    for (i, (n, pat)) in fixed.iter().enumerate() {
        let rm = build_roll_max(&mut rng, *pat);
        let (on, orm) = generate_test_case(*n, rm);
        print_json(on, &orm);
        let _ = i;
    }

    let remaining = total - fixed.len();
    for t in 0..remaining {
        let mode = t % 10;
        let n: i32 = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_i32(4, 20),
            4 => rng.gen_range_i32(20, 200),
            5 => rng.gen_range_i32(200, 1000),
            6 => rng.gen_range_i32(1000, 3000),
            7 => rng.gen_range_i32(3000, 5000),
            8 => 5000,
            _ => rng.gen_range_i32(1, 5000),
        };
        let pat = (t * 7 + mode) % 10;
        let rm = build_roll_max(&mut rng, pat);
        let (on, orm) = generate_test_case(n, rm);
        print_json(on, &orm);
    }
}