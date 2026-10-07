use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    m: i32,
    n: i32,
    introverts_count: i32,
    extroverts_count: i32,
) -> (result: (i32, i32, i32, i32))
    requires
        1 <= m <= 5,
        1 <= n <= 5,
        0 <= introverts_count <= 6,
        0 <= extroverts_count <= 6,
        introverts_count <= m * n,
        extroverts_count <= m * n,
    ensures
        ({
            let (a, b, c, d) = result;
            &&& 1 <= a <= 5
            &&& 1 <= b <= 5
            &&& 0 <= c <= 6
            &&& 0 <= d <= 6
            &&& c <= a * b
            &&& d <= a * b
        }),
{
    (m, n, introverts_count, extroverts_count)
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

    fn gen_range(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn clamp(v: i32, lo: i32, hi: i32) -> i32 {
    if v < lo { lo } else if v > hi { hi } else { v }
}

fn build(m: i32, n: i32, ic: i32, ec: i32) -> (i32, i32, i32, i32) {
    let m = clamp(m, 1, 5);
    let n = clamp(n, 1, 5);
    let cap = m * n;
    let ic = clamp(ic, 0, 6);
    let ec = clamp(ec, 0, 6);
    let ic = if ic > cap { cap } else { ic };
    let ec = if ec > cap { cap } else { ec };
    generate_test_case(m, n, ic, ec)
}

fn print_case(m: i32, n: i32, ic: i32, ec: i32) {
    println!(
        "{{\"m\": {}, \"n\": {}, \"introverts_count\": {}, \"extroverts_count\": {}}}",
        m, n, ic, ec
    );
}

fn adversarial(idx: usize, rng: &mut Rng) -> (i32, i32, i32, i32) {
    match idx % 10 {
        0 => build(1, 1, 0, 0),
        1 => build(1, 1, 1, 0),
        2 => build(1, 1, 0, 1),
        3 => build(5, 5, 6, 6),
        4 => build(5, 5, 0, 0),
        5 => build(1, 5, 6, 0),
        6 => build(5, 1, 0, 6),
        7 => build(2, 2, 4, 0),
        8 => build(2, 3, 1, 2),
        9 => {
            let m = rng.gen_range(1, 5);
            let n = rng.gen_range(1, 5);
            let cap = m * n;
            let ic = rng.gen_range(0, 6);
            let remaining = if ic <= cap { cap - ic } else { 0 };
            let hi_ec = if remaining < 6 { remaining } else { 6 };
            let ec = if hi_ec < 0 { 0 } else { rng.gen_range(0, hi_ec) };
            build(m, n, ic, ec)
        }
        _ => build(3, 3, 3, 3),
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

    for t in 0..total {
        let (m, n, ic, ec) = if t < 50 {
            adversarial(t, &mut rng)
        } else {
            let m = rng.gen_range(1, 5);
            let n = rng.gen_range(1, 5);
            let ic = rng.gen_range(0, 6);
            let ec = rng.gen_range(0, 6);
            build(m, n, ic, ec)
        };
        print_case(m, n, ic, ec);
    }
}