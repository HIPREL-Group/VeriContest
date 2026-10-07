use vstd::prelude::*;

verus! {

pub fn generate_test_case(values: Vec<i32>) -> (result: Vec<i32>)
    ensures
        1 <= result.len() <= 100000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
{
    let n = if values.len() < 1 { 1usize }
            else if values.len() > 100000 { 100000usize } else { values.len() };
    let mut result = Vec::new();
    let mut i = 0usize;
    while i < n
        invariant
            1 <= n <= 100000,
            0 <= i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100000,
        decreases n - i,
    {
        let value = if i < values.len() { values[i] } else { 1 };
        let value = if value < 1 { 1 } else if value > 100000 { 100000 } else { value };
        result.push(value);
        i += 1;
    }
    result
}


pub fn generate_candidate(
    n: usize,
    fillers: &Vec<i32>,
) -> (grades: Vec<i32>)
    requires
        1 <= n <= 100000,
        fillers.len() == n,
        forall |i: int| 0 <= i < fillers.len() ==> 1 <= #[trigger] fillers[i] <= 100000,
    ensures
        1 <= grades.len() <= 100000,
        forall |i: int| 0 <= i < grades.len() ==> 1 <= #[trigger] grades[i] <= 100000,
{
    let mut grades: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == fillers.len(),
            grades.len() == i,
            forall |k: int| 0 <= k < fillers.len() ==> 1 <= #[trigger] fillers[k] <= 100000,
            forall |k: int| 0 <= k < i as int ==> 1 <= #[trigger] grades[k] <= 100000,
        decreases n - i,
    {
        grades.push(fillers[i]);
        i = i + 1;
    }
    grades
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

fn make_fillers(rng: &mut Rng, n: usize, mode: usize) -> Vec<i32> {
    let mut res = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                res.push(rng.gen_range_i32(1, 100000));
            }
        }
        1 => {
            for _ in 0..n {
                res.push(1);
            }
        }
        2 => {
            for _ in 0..n {
                res.push(100000);
            }
        }
        3 => {
            for i in 0..n {
                res.push(((i % 100000) + 1) as i32);
            }
        }
        4 => {
            for i in 0..n {
                res.push((100000 - (i % 100000)) as i32);
            }
        }
        5 => {
            let v = rng.gen_range_i32(1, 100000);
            for _ in 0..n {
                res.push(v);
            }
        }
        6 => {
            for _ in 0..n {
                res.push(rng.gen_range_i32(1, 10));
            }
        }
        7 => {
            for _ in 0..n {
                res.push(rng.gen_range_i32(99990, 100000));
            }
        }
        8 => {
            for i in 0..n {
                if i % 2 == 0 {
                    res.push(1);
                } else {
                    res.push(100000);
                }
            }
        }
        _ => {
            for _ in 0..n {
                res.push(rng.gen_range_i32(1, 100000));
            }
        }
    }
    res
}

fn pick_n(rng: &mut Rng, t: usize, mode: usize) -> usize {
    // Triangular numbers: 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120...
    // T(k) = k*(k+1)/2. Near these boundaries is adversarial.
    let tris = [1usize, 3, 6, 10, 15, 21, 28, 36, 45, 55, 66, 78, 91, 105, 120, 136, 153, 171, 190, 210, 231, 253, 276, 300];
    match mode % 11 {
        0 => 1,
        1 => 2,
        2 => 100000,
        3 => {
            let idx = t % tris.len();
            tris[idx]
        }
        4 => {
            let idx = t % tris.len();
            if tris[idx] > 0 { tris[idx] - 1 } else { 1 }
        }
        5 => {
            let idx = t % tris.len();
            tris[idx] + 1
        }
        6 => rng.gen_range_usize(1, 100),
        7 => rng.gen_range_usize(1, 1000),
        8 => rng.gen_range_usize(50000, 100000),
        9 => 99999,
        _ => rng.gen_range_usize(1, 10000),
    }
}

fn print_json(grades: &[i32]) {
    let grades = generate_test_case(grades.to_vec());
    print!("{{\"grades\":[");
    for i in 0..grades.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", grades[i]);
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
        let mode_n = t % 11;
        let mode_f = (t / 11) % 9;
        let n = pick_n(&mut rng, t, mode_n);
        let fillers = make_fillers(&mut rng, n, mode_f);
        let grades = generate_candidate(n, &fillers);
        print_json(&grades);
    }
}
