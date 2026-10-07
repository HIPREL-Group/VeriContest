use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    pattern: u8,
    letters: &Vec<u8>,
) -> (word: Vec<u8>)
    requires
        1 <= letters.len() <= 100,
        forall |i: int| 0 <= i < letters.len() ==>
            (('A' as u8 <= #[trigger] letters[i] && letters[i] <= 'Z' as u8) ||
             ('a' as u8 <= letters[i] && letters[i] <= 'z' as u8)),
    ensures
        1 <= word@.len() <= 100,
        word@.len() == letters.len(),
        forall |i: int| 0 <= i < word@.len() ==>
            (('A' <= word@[i] && word@[i] <= 'Z') || ('a' <= word@[i] && word@[i] <= 'z')),
{
    let _ = pattern;
    let n = letters.len();
    let mut word: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == letters.len(),
            0 <= i <= n,
            word.len() == i,
            forall |k: int| 0 <= k < letters.len() ==>
                (('A' as u8 <= #[trigger] letters[k] && letters[k] <= 'Z' as u8) ||
                 ('a' as u8 <= letters[k] && letters[k] <= 'z' as u8)),
            forall |k: int| 0 <= k < i as int ==> #[trigger] word[k] == letters[k],
        decreases n - i,
    {
        word.push(letters[i]);
        i = i + 1;
    }

    proof {
        assert forall |k: int| 0 <= k < word@.len() implies
            (('A' <= word@[k] && word@[k] <= 'Z') || ('a' <= word@[k] && word@[k] <= 'z'))
        by {
            assert(word[k] == letters[k]);
            let b = letters[k];
            assert(('A' as u8 <= b && b <= 'Z' as u8) || ('a' as u8 <= b && b <= 'z' as u8));
            assert('A' as u8 == 65);
            assert('Z' as u8 == 90);
            assert('a' as u8 == 97);
            assert('z' as u8 == 122);
        }
    }

    word
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
    fn next_bool(&mut self) -> bool {
        self.next_u64() & 1 == 1
    }
}

fn rand_upper(rng: &mut Rng) -> u8 {
    b'A' + (rng.gen_range_usize(0, 25) as u8)
}
fn rand_lower(rng: &mut Rng) -> u8 {
    b'a' + (rng.gen_range_usize(0, 25) as u8)
}
fn rand_letter(rng: &mut Rng) -> u8 {
    if rng.next_bool() { rand_upper(rng) } else { rand_lower(rng) }
}

fn generate_letters(rng: &mut Rng, mode: usize, n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all uppercase
            for _ in 0..n { v.push(rand_upper(rng)); }
        }
        1 => {
            // all lowercase
            for _ in 0..n { v.push(rand_lower(rng)); }
        }
        2 => {
            // first upper, rest lower (valid Google-style)
            v.push(rand_upper(rng));
            for _ in 1..n { v.push(rand_lower(rng)); }
        }
        3 => {
            // first lower, rest upper (invalid)
            if n >= 1 { v.push(rand_lower(rng)); }
            for _ in 1..n { v.push(rand_upper(rng)); }
        }
        4 => {
            // mixed random
            for _ in 0..n { v.push(rand_letter(rng)); }
        }
        5 => {
            // first upper, rest upper except one lower
            for _ in 0..n { v.push(rand_upper(rng)); }
            if n >= 2 {
                let idx = rng.gen_range_usize(1, n - 1);
                v[idx] = rand_lower(rng);
            }
        }
        6 => {
            // all lower except last
            for _ in 0..n { v.push(rand_lower(rng)); }
            if n >= 1 {
                v[n - 1] = rand_upper(rng);
            }
        }
        7 => {
            // alternating
            for i in 0..n {
                if i % 2 == 0 { v.push(rand_upper(rng)); } else { v.push(rand_lower(rng)); }
            }
        }
        8 => {
            // single char
            v.push(rand_letter(rng));
        }
        9 => {
            // two chars edge cases
            v.push(rand_letter(rng));
            if n >= 2 { v.push(rand_letter(rng)); }
            for _ in 2..n { v.push(rand_letter(rng)); }
        }
        _ => {
            for _ in 0..n { v.push(rand_letter(rng)); }
        }
    }
    while v.len() < n {
        v.push(rand_letter(rng));
    }
    v.truncate(n);
    v
}

fn print_json(word: &[u8]) {
    print!("{{\"word\":\"");
    for &b in word {
        print!("{}", b as char);
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
    let total = 200usize;
    let modes = 10usize;

    for t in 0..total {
        let mode = t % modes;
        let n: usize = match mode {
            8 => 1,
            9 => if t % 2 == 0 { 2 } else { 100 },
            _ => {
                let choice = t % 5;
                match choice {
                    0 => 1,
                    1 => 2,
                    2 => 100,
                    3 => rng.gen_range_usize(1, 20),
                    _ => rng.gen_range_usize(1, 100),
                }
            }
        };
        let letters = generate_letters(&mut rng, mode, n);
        let word = generate_test_case(mode as u8, &letters);
        print_json(&word);
    }
}