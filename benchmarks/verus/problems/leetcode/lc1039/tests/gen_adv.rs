use vstd::prelude::*;

verus! {

pub fn generate_test_case(a: i32, b: i32, c: i32) -> (values: Vec<i32>)
    requires
        1 <= a <= 100,
        1 <= b <= 100,
        1 <= c <= 100,
    ensures
        3 <= values.len() <= 50,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100,
{
    let mut values: Vec<i32> = Vec::new();
    values.push(a);
    values.push(b);
    values.push(c);

    assert(values.len() == 3);
    assert(3 <= values.len() <= 50);
    assert(values[0] == a);
    assert(values[1] == b);
    assert(values[2] == c);

    assert forall|i: int| 0 <= i < values.len() implies 1 <= #[trigger] values[i] <= 100 by {
        assert(0 <= i < values.len());
        assert(values.len() == 3);
        if i == 0 {
            assert(values[i] == a);
            assert(1 <= values[i] <= 100);
        } else if i == 1 {
            assert(values[i] == b);
            assert(1 <= values[i] <= 100);
        } else {
            assert(2 <= i);
            assert(i < 3);
            assert(i == 2);
            assert(values[i] == c);
            assert(1 <= values[i] <= 100);
        }
    };

    values
}

} // verus!

fn triple_product(a: i32, b: i32, c: i32) -> i32 {
    a * b * c
}

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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }

    fn gen_bool(&mut self) -> bool {
        (self.next_u64() & 1) == 0
    }
}

fn adversarial_case(mode: usize, rng: &mut Rng) -> (i32, i32, i32) {
    match mode {
        0 => (1, 1, 1),
        1 => (100, 100, 100),
        2 => (1, 100, 1),
        3 => (100, 1, 100),
        4 => (1, 2, 100),
        5 => (100, 2, 1),
        6 => {
            let x = rng.gen_range_i32(1, 100);
            (x, x, x)
        }
        7 => {
            let a = rng.gen_range_i32(1, 3);
            let b = rng.gen_range_i32(98, 100);
            let c = rng.gen_range_i32(1, 3);
            (a, b, c)
        }
        8 => {
            let a = if rng.gen_bool() { 1 } else { 100 };
            let b = rng.gen_range_i32(1, 100);
            let c = if rng.gen_bool() { 1 } else { 100 };
            (a, b, c)
        }
        9 => {
            let a = rng.gen_range_i32(1, 100);
            let b = rng.gen_range_i32(1, 100);
            let c = rng.gen_range_i32(1, 100);
            let mut arr = [a, b, c];
            if arr[0] > arr[1] {
                arr.swap(0, 1);
            }
            if arr[1] > arr[2] {
                arr.swap(1, 2);
            }
            if arr[0] > arr[1] {
                arr.swap(0, 1);
            }
            (arr[2], arr[1], arr[0])
        }
        _ => (
            rng.gen_range_i32(1, 100),
            rng.gen_range_i32(1, 100),
            rng.gen_range_i32(1, 100),
        ),
    }
}

fn main() {
    use std::env;
    use std::io::{self, Write};

    let seed = env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);
    let stdout = io::stdout();
    let mut out = io::BufWriter::new(stdout.lock());

    let total_cases = 200usize;
    let mut i = 0usize;
    while i < total_cases {
        let mode = i % 10;
        let (a, b, c) = if i < 120 {
            adversarial_case(mode, &mut rng)
        } else {
            adversarial_case(100, &mut rng)
        };

        let values = generate_test_case(a, b, c);

        write!(out, "{{\"values\": [").unwrap();
        for j in 0..values.len() {
            if j > 0 { write!(out, ",").unwrap(); }
            write!(out, "{}", values[j]).unwrap();
        }
        writeln!(out, "]}}").unwrap();
        i += 1;
    }
}