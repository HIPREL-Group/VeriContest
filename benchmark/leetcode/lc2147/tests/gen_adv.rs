use vstd::prelude::*;

verus! {

pub open spec fn vec_to_seq_chars(v: Seq<u8>) -> Seq<char> {
    v.map(|_i: int, b: u8| b as char)
}

pub fn generate_test_case(chars: &Vec<u8>) -> (result: Vec<u8>)
    requires
        1 <= chars.len() <= 100_000,
        forall |i: int| 0 <= i < chars.len() ==> (#[trigger] chars[i]) == 'S' as u8 || chars[i] == 'P' as u8,
    ensures
        1 <= result.len() <= 100_000,
        result.len() == chars.len(),
        forall |i: int| 0 <= i < result.len() ==> (#[trigger] result[i]) == 'S' as u8 || result[i] == 'P' as u8,
        forall |i: int| 0 <= i < result.len() ==> result[i] == chars[i],
{
    let mut out: Vec<u8> = Vec::new();
    let n = chars.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == chars.len(),
            0 <= i <= n,
            out.len() == i,
            forall |k: int| 0 <= k < i as int ==> (#[trigger] out[k]) == chars[k],
            forall |k: int| 0 <= k < chars.len() ==> (#[trigger] chars[k]) == 'S' as u8 || chars[k] == 'P' as u8,
        decreases n - i,
    {
        out.push(chars[i]);
        i += 1;
    }
    out
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

    fn gen_bool(&mut self, p_num: u64, p_den: u64) -> bool {
        (self.next_u64() % p_den) < p_num
    }
}

fn make_random(rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        if rng.gen_bool(1, 2) {
            v.push(b'S');
        } else {
            v.push(b'P');
        }
    }
    v
}

fn make_pattern(mode: usize, rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    match mode {
        0 => {
            // single char
            v.push(b'S');
        }
        1 => {
            v.push(b'P');
        }
        2 => {
            // all S
            for _ in 0..n { v.push(b'S'); }
        }
        3 => {
            // all P
            for _ in 0..n { v.push(b'P'); }
        }
        4 => {
            // SP SP SP ...
            for i in 0..n {
                v.push(if i % 2 == 0 { b'S' } else { b'P' });
            }
        }
        5 => {
            // SS PP SS PP ...
            for i in 0..n {
                v.push(if (i / 2) % 2 == 0 { b'S' } else { b'P' });
            }
        }
        6 => {
            // many plants, few seats: SPPPPPPPPSPPPPPPP...
            for i in 0..n {
                v.push(if i % 8 == 0 { b'S' } else { b'P' });
            }
        }
        7 => {
            // exactly 2 seats with lots of plants between
            for i in 0..n {
                if i == n / 3 || i == 2 * n / 3 {
                    v.push(b'S');
                } else {
                    v.push(b'P');
                }
            }
        }
        8 => {
            // pairs of seats: SSSSSS with plants
            for i in 0..n {
                if i % 3 == 2 { v.push(b'P'); } else { v.push(b'S'); }
            }
        }
        9 => {
            // odd count of S (force 0 answer): SSSPPP...
            for i in 0..n {
                if i < 3 { v.push(b'S'); } else { v.push(b'P'); }
            }
        }
        _ => {
            return make_random(rng, n);
        }
    }
    // If resulting length < n (e.g., mode 0/1), pad with random
    while v.len() < n {
        if rng.gen_bool(1, 2) { v.push(b'S'); } else { v.push(b'P'); }
    }
    v.truncate(n);
    // Ensure at least one element
    if v.is_empty() {
        v.push(b'S');
    }
    v
}

fn print_json(chars: &[u8]) {
    print!("{{\"corridor\":\"");
    for &c in chars {
        print!("{}", c as char);
    }
    println!("\"}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 220usize;

    for t in 0..total {
        let mode = t % 11;
        let n = match mode {
            0 | 1 => 1,
            2 => {
                let choices = [2usize, 4, 6, 10, 50, 100];
                choices[t % choices.len()]
            }
            3 => {
                let choices = [1usize, 5, 100, 1000];
                choices[t % choices.len()]
            }
            4 => {
                let choices = [2usize, 4, 8, 20, 100, 10000];
                choices[t % choices.len()]
            }
            5 => {
                let choices = [4usize, 8, 16, 100, 1000];
                choices[t % choices.len()]
            }
            6 => {
                let choices = [16usize, 64, 256, 1024, 10000];
                choices[t % choices.len()]
            }
            7 => {
                let choices = [3usize, 7, 100, 1000, 50000];
                choices[t % choices.len()]
            }
            8 => {
                let choices = [3usize, 9, 30, 300, 3000];
                choices[t % choices.len()]
            }
            9 => {
                let choices = [3usize, 10, 100];
                choices[t % choices.len()]
            }
            _ => {
                let choices = [1usize, 2, 10, 100, 1000, 10000, 100000];
                choices[t % choices.len()]
            }
        };

        let chars = make_pattern(mode, &mut rng, n);
        // Sanity: ensure all are S or P and length in range
        let mut ok = chars.len() >= 1 && chars.len() <= 100_000;
        for &c in &chars {
            if c != b'S' && c != b'P' { ok = false; }
        }
        if !ok { continue; }

        let result = generate_test_case(&chars);
        print_json(&result);
    }
}