use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    bits_a: &Vec<u8>,
    bits_b: &Vec<u8>,
) -> (result: (Vec<i64>, Vec<i64>))
    requires
        bits_a.len() == bits_b.len(),
        bits_a.len() >= 1,
        bits_a.len() <= 200_000,
        forall|i: int| 0 <= i < bits_a.len() ==> (#[trigger] bits_a[i]) <= 1,
        forall|i: int| 0 <= i < bits_b.len() ==> (#[trigger] bits_b[i]) <= 1,
    ensures
        result.0.len() == result.1.len(),
        result.0.len() >= 1,
        result.0.len() == bits_a.len(),
        forall|i: int| 0 <= i < result.0.len() ==> (#[trigger] result.0@[i] == 0 || result.0@[i] == 1),
        forall|i: int| 0 <= i < result.1.len() ==> (#[trigger] result.1@[i] == 0 || result.1@[i] == 1),
{
    let n = bits_a.len();
    let mut a: Vec<i64> = Vec::new();
    let mut b: Vec<i64> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            n == bits_a.len(),
            n == bits_b.len(),
            a.len() == i,
            b.len() == i,
            0 <= i <= n,
            forall|k: int| 0 <= k < bits_a.len() ==> (#[trigger] bits_a[k]) <= 1,
            forall|k: int| 0 <= k < bits_b.len() ==> (#[trigger] bits_b[k]) <= 1,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] a@[k] == 0 || a@[k] == 1),
            forall|k: int| 0 <= k < i as int ==> (#[trigger] b@[k] == 0 || b@[k] == 1),
        decreases n - i,
    {
        let va: i64 = if bits_a[i] == 0 { 0 } else { 1 };
        let vb: i64 = if bits_b[i] == 0 { 0 } else { 1 };
        a.push(va);
        b.push(vb);
        i = i + 1;
    }

    (a, b)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(1) }
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
    fn gen_bit(&mut self) -> u8 {
        (self.next_u64() & 1) as u8
    }
}

fn make_case(rng: &mut Rng, mode: usize, n: usize) -> (Vec<u8>, Vec<u8>) {
    let mut a = vec![0u8; n];
    let mut b = vec![0u8; n];
    match mode {
        0 => {
            // all zeros
        }
        1 => {
            for i in 0..n { a[i] = 1; b[i] = 1; }
        }
        2 => {
            // all zeros a, all ones b
            for i in 0..n { b[i] = 1; }
        }
        3 => {
            // equal
            for i in 0..n {
                let v = rng.gen_bit();
                a[i] = v; b[i] = v;
            }
        }
        4 => {
            // complementary: a[i] xor b[i] = 1 for all i
            for i in 0..n {
                let v = rng.gen_bit();
                a[i] = v; b[i] = 1 - v;
            }
        }
        5 => {
            // random
            for i in 0..n {
                a[i] = rng.gen_bit();
                b[i] = rng.gen_bit();
            }
        }
        6 => {
            // one index differs in xor pattern
            let v = rng.gen_bit();
            for i in 0..n { a[i] = v; b[i] = v; }
            let k = rng.gen_range_usize(0, n - 1);
            b[k] = 1 - b[k];
        }
        7 => {
            // alternating
            for i in 0..n {
                a[i] = (i & 1) as u8;
                b[i] = ((i + 1) & 1) as u8;
            }
        }
        8 => {
            // half zero half one
            for i in 0..n {
                if i < n / 2 { a[i] = 0; b[i] = 0; } else { a[i] = 1; b[i] = 1; }
            }
        }
        9 => {
            // first bit differs, rest same
            a[0] = 1;
            for i in 1..n {
                let v = rng.gen_bit();
                a[i] = v; b[i] = v;
            }
        }
        _ => {
            for i in 0..n {
                a[i] = rng.gen_bit();
                b[i] = rng.gen_bit();
            }
        }
    }
    (a, b)
}

fn print_json(a: &[i64], b: &[i64]) {
    print!("{{\"a\":[");
    for i in 0..a.len() {
        if i > 0 { print!(","); }
        print!("{}", a[i]);
    }
    print!("],\"b\":[");
    for i in 0..b.len() {
        if i > 0 { print!(","); }
        print!("{}", b[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 5),
            1 => 2 + (t % 8),
            2 => 10,
            3 => rng.gen_range_usize(1, 50),
            4 => rng.gen_range_usize(1, 50),
            5 => rng.gen_range_usize(1, 200),
            6 => rng.gen_range_usize(2, 100),
            7 => 2 + (t % 20),
            8 => 2 + (t % 30),
            9 => rng.gen_range_usize(2, 100),
            _ => rng.gen_range_usize(1, 100),
        };
        let n = if n < 1 { 1 } else { n };
        let (ba, bb) = make_case(&mut rng, mode, n);
        let ba_v: Vec<u8> = ba;
        let bb_v: Vec<u8> = bb;
        let (a, b) = generate_test_case(&ba_v, &bb_v);
        print_json(&a, &b);
    }
}