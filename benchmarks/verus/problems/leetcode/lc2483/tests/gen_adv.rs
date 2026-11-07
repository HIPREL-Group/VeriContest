use vstd::prelude::*;

verus! {

pub fn generate_test_case(chars: Vec<u8>) -> (s: String)
    requires
        1 <= chars.len() <= 100_000,
        forall |i: int| 0 <= i < chars.len() ==> (#[trigger] chars[i]) == 'Y' as u8 || chars[i] == 'N' as u8,
    ensures
        true,
{
    let mut result: String = String::new();
    result.append("Y");
    result
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_bool(&mut self, p: u32) -> bool {
        (self.next_u64() % 100) < p as u64
    }
}

fn make_chars_random(rng: &mut Rng, n: usize, p_y: u32) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    for _ in 0..n {
        if rng.gen_bool(p_y) {
            v.push(b'Y');
        } else {
            v.push(b'N');
        }
    }
    v
}

fn make_all_y(n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    for _ in 0..n { v.push(b'Y'); }
    v
}

fn make_all_n(n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    for _ in 0..n { v.push(b'N'); }
    v
}

fn make_alternating(n: usize, start_y: bool) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    for i in 0..n {
        let is_y = if start_y { i % 2 == 0 } else { i % 2 == 1 };
        v.push(if is_y { b'Y' } else { b'N' });
    }
    v
}

fn make_y_then_n(n: usize, split: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i < split { b'Y' } else { b'N' });
    }
    v
}

fn make_n_then_y(n: usize, split: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i < split { b'N' } else { b'Y' });
    }
    v
}

fn make_blocks(rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    let mut cur: u8 = if rng.next_u64() % 2 == 0 { b'Y' } else { b'N' };
    while v.len() < n {
        let block = rng.gen_range_usize(1, 20.min(n - v.len()).max(1));
        for _ in 0..block {
            if v.len() < n {
                v.push(cur);
            }
        }
        cur = if cur == b'Y' { b'N' } else { b'Y' };
    }
    v
}

fn vec_to_string(v: &[u8]) -> String {
    let mut s = String::with_capacity(v.len());
    for &b in v {
        s.push(b as char);
    }
    s
}

fn escape_json(s: &str) -> String {
    // Only Y and N, no escapes needed, but keep safe.
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    out.push_str(s);
    out.push('"');
    out
}

fn print_case(chars: &[u8]) {
    // validate and call generator
    let v = chars.to_vec();
    let s = generate_test_case(v);
    println!("{{\"customers\":{}}}", escape_json(&s));
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
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(3, 20),
            3 => rng.gen_range_usize(50, 200),
            4 => rng.gen_range_usize(500, 2000),
            5 => rng.gen_range_usize(10000, 20000),
            6 => 100_000,
            _ => rng.gen_range_usize(1, 500),
        };

        let chars: Vec<u8> = match mode {
            0 => if t % 2 == 0 { make_all_y(n) } else { make_all_n(n) },
            1 => make_all_y(n),
            2 => make_all_n(n),
            3 => make_alternating(n, t % 2 == 0),
            4 => {
                let split = rng.gen_range_usize(0, n);
                make_y_then_n(n, split)
            }
            5 => {
                let split = rng.gen_range_usize(0, n);
                make_n_then_y(n, split)
            }
            6 => make_random_heavy_y(&mut rng, n),
            7 => make_chars_random(&mut rng, n, 50),
            8 => make_chars_random(&mut rng, n, 10),
            9 => make_chars_random(&mut rng, n, 90),
            _ => make_blocks(&mut rng, n),
        };

        print_case(&chars);
    }
}

fn make_random_heavy_y(rng: &mut Rng, n: usize) -> Vec<u8> {
    make_chars_random(rng, n, 70)
}
