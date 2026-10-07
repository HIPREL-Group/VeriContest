use vstd::prelude::*;

verus! {

pub fn generate_test_case(n: usize, s_bits: &Vec<u8>, t_bits: &Vec<u8>) -> (res: (Vec<char>, Vec<char>))
    requires
        2 <= n <= 100000,
        s_bits.len() == n,
        t_bits.len() == n,
        forall|i: int| 0 <= i < n as int ==> (#[trigger] s_bits[i]) == 0u8 || s_bits[i] == 1u8,
        forall|i: int| 0 <= i < n as int ==> (#[trigger] t_bits[i]) == 0u8 || t_bits[i] == 1u8,
    ensures
        res.0.len() == n,
        res.1.len() == n,
        2 <= res.0.len() <= 100000,
        2 <= res.1.len() <= 100000,
        forall|i: int| 0 <= i < res.0.len() ==> (#[trigger] res.0[i]) == '0' || res.0[i] == '1',
        forall|i: int| 0 <= i < res.1.len() ==> (#[trigger] res.1[i]) == '0' || res.1[i] == '1',
{
    let mut s: Vec<char> = Vec::new();
    let mut t: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == s_bits.len(),
            n == t_bits.len(),
            2 <= n <= 100000,
            i <= n,
            s.len() == i,
            t.len() == i,
            forall|k: int| 0 <= k < n as int ==> (#[trigger] s_bits[k]) == 0u8 || s_bits[k] == 1u8,
            forall|k: int| 0 <= k < n as int ==> (#[trigger] t_bits[k]) == 0u8 || t_bits[k] == 1u8,
            forall|k: int| 0 <= k < i as int ==> (#[trigger] s[k]) == '0' || s[k] == '1',
            forall|k: int| 0 <= k < i as int ==> (#[trigger] t[k]) == '0' || t[k] == '1',
        decreases n - i,
    {
        let sb = s_bits[i];
        let tb = t_bits[i];
        let sc: char = if sb == 0u8 { '0' } else { '1' };
        let tc: char = if tb == 0u8 { '0' } else { '1' };
        s.push(sc);
        t.push(tc);
        i = i + 1;
    }
    (s, t)
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
    fn gen_range(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn make_case(rng: &mut Rng, mode: usize, n_in: usize) -> (Vec<u8>, Vec<u8>, usize) {
    let mut n = n_in;
    if n < 2 { n = 2; }
    if n > 100000 { n = 100000; }
    let mut s = vec![0u8; n];
    let mut t = vec![0u8; n];

    match mode {
        0 => {
            // all zeros both -> true
        }
        1 => {
            // s all zeros, t has ones -> false (has_one differs)
            for i in 0..n { t[i] = 1; }
        }
        2 => {
            // s has ones, t all zeros -> false
            for i in 0..n { s[i] = 1; }
        }
        3 => {
            // both all ones -> true
            for i in 0..n { s[i] = 1; t[i] = 1; }
        }
        4 => {
            // single one in s, single one in t at different positions -> true
            s[0] = 1;
            t[n - 1] = 1;
        }
        5 => {
            // random with at least one '1' in each
            for i in 0..n {
                s[i] = (rng.next_u64() % 2) as u8;
                t[i] = (rng.next_u64() % 2) as u8;
            }
            s[rng.gen_range(0, n - 1)] = 1;
            t[rng.gen_range(0, n - 1)] = 1;
        }
        6 => {
            // fully random
            for i in 0..n {
                s[i] = (rng.next_u64() % 2) as u8;
                t[i] = (rng.next_u64() % 2) as u8;
            }
        }
        7 => {
            // sparse: one '1' each
            s[rng.gen_range(0, n - 1)] = 1;
            t[rng.gen_range(0, n - 1)] = 1;
        }
        8 => {
            // s sparse, t zero -> false
            s[rng.gen_range(0, n - 1)] = 1;
        }
        9 => {
            // alternating
            for i in 0..n {
                s[i] = (i % 2) as u8;
                t[i] = ((i + 1) % 2) as u8;
            }
        }
        _ => {
            // mostly ones
            for i in 0..n {
                s[i] = if rng.next_u64() % 4 == 0 { 0 } else { 1 };
                t[i] = if rng.next_u64() % 4 == 0 { 0 } else { 1 };
            }
        }
    }
    (s, t, n)
}

fn print_json(s: &[char], t: &[char]) {
    print!("{{\"s\":\"");
    for &c in s { print!("{}", c); }
    print!("\",\"target\":\"");
    for &c in t { print!("{}", c); }
    println!("\"}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for tc in 0..total {
        let mode = tc % modes;
        let n = match mode {
            0 => 2 + (tc % 5),
            1 => 100000,
            2 => 3 + (tc % 10),
            3 => 2,
            4 => 5 + (tc % 20),
            5 => 100 + (tc % 50),
            6 => 50 + (tc % 100),
            7 => 1000,
            8 => 200 + (tc % 300),
            9 => 2 + (tc % 50),
            _ => 500 + (tc % 500),
        };
        let (sb, tb, nn) = make_case(&mut rng, mode, n);
        let sb_vec: Vec<u8> = sb;
        let tb_vec: Vec<u8> = tb;
        let (sc, tc_chars) = generate_test_case(nn, &sb_vec, &tb_vec);
        print_json(&sc, &tc_chars);
    }
}