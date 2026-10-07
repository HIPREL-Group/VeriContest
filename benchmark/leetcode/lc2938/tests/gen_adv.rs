use vstd::prelude::*;

verus! {

pub fn generate_test_case(bits: &Vec<u8>) -> (result: String)
    requires
        1 <= bits.len() <= 100000,
        forall |i: int| 0 <= i < bits.len() ==> (#[trigger] bits[i]) == 0u8 || bits[i] == 1u8,
    ensures
        true,
{
    let mut result: String = String::new();
    result.append("0");
    result
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
}

fn print_json(s: &str) {
    let mut out = String::new();
    out.push_str("{\"s\":\"");
    out.push_str(s);
    out.push_str("\"}");
    println!("{}", out);
}

fn bits_from_string(s: &str) -> Vec<u8> {
    s.chars().map(|c| if c == '1' { 1u8 } else { 0u8 }).collect()
}

fn make_random(rng: &mut Rng, n: usize) -> Vec<u8> {
    (0..n).map(|_| (rng.next_u64() & 1) as u8).collect()
}

fn make_all_zero(n: usize) -> Vec<u8> { vec![0u8; n] }
fn make_all_one(n: usize) -> Vec<u8> { vec![1u8; n] }

fn make_ones_then_zeros(n: usize, ones: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..ones { v.push(1u8); }
    for _ in ones..n { v.push(0u8); }
    v
}

fn make_zeros_then_ones(n: usize, zeros: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..zeros { v.push(0u8); }
    for _ in zeros..n { v.push(1u8); }
    v
}

fn make_alternating(n: usize, start: u8) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { start } else { 1 - start });
    }
    v
}

fn make_single_one(n: usize, pos: usize) -> Vec<u8> {
    let mut v = vec![0u8; n];
    if pos < n { v[pos] = 1; }
    v
}

fn make_single_zero(n: usize, pos: usize) -> Vec<u8> {
    let mut v = vec![1u8; n];
    if pos < n { v[pos] = 0; }
    v
}

fn make_blocks(rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    let mut cur: u8 = (rng.next_u64() & 1) as u8;
    let mut i = 0;
    while i < n {
        let blen = rng.gen_range_usize(1, 20.min(n - i).max(1));
        for _ in 0..blen {
            if v.len() < n { v.push(cur); }
        }
        cur = 1 - cur;
        i += blen;
    }
    while v.len() > n { v.pop(); }
    while v.len() < n { v.push(0); }
    v
}

fn bits_to_string(bits: &[u8]) -> String {
    bits.iter().map(|&b| if b == 1 { '1' } else { '0' }).collect()
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 { args[1].parse::<u64>().unwrap_or(1) } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;

    for t in 0..total {
        let mode = t % 12;
        let n: usize = match mode {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(3, 20),
            3 => rng.gen_range_usize(100, 500),
            4 => 100000,
            5 => rng.gen_range_usize(2, 50),
            6 => rng.gen_range_usize(50, 200),
            7 => rng.gen_range_usize(10, 100),
            8 => 1000,
            9 => 99999,
            10 => 50000,
            _ => rng.gen_range_usize(1, 1000),
        };

        let bits: Vec<u8> = match mode {
            0 => if rng.next_u64() & 1 == 0 { vec![0] } else { vec![1] },
            1 => {
                let a = (rng.next_u64() & 1) as u8;
                let b = (rng.next_u64() & 1) as u8;
                vec![a, b]
            }
            2 => make_random(&mut rng, n),
            3 => make_random(&mut rng, n),
            4 => make_random(&mut rng, n),
            5 => make_all_zero(n),
            6 => make_all_one(n),
            7 => {
                let ones = rng.gen_range_usize(0, n);
                make_ones_then_zeros(n, ones)
            }
            8 => {
                let zeros = rng.gen_range_usize(0, n);
                make_zeros_then_ones(n, zeros)
            }
            9 => make_alternating(n, (rng.next_u64() & 1) as u8),
            10 => {
                if rng.next_u64() & 1 == 0 {
                    let pos = rng.gen_range_usize(0, n - 1);
                    make_single_one(n, pos)
                } else {
                    let pos = rng.gen_range_usize(0, n - 1);
                    make_single_zero(n, pos)
                }
            }
            _ => make_blocks(&mut rng, n),
        };

        let s = generate_test_case(&bits);
        // sanity
        let _ = bits_from_string(&s);
        let _ = bits_to_string(&bits);
        print_json(&s);
    }
}
