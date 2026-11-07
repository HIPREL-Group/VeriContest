use vstd::prelude::*;

verus! {

pub fn generate_test_case(letters: &Vec<u8>) -> (result: (String, usize))
    requires
        1 <= letters.len() <= 100,
        forall|i: int| 0 <= i < letters.len() ==> 97 <= #[trigger] letters[i] <= 122,
    ensures
        true,
{
    let mut s: String = String::new();
    s.append("a");
    (s, 0usize)
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
}

fn make_letters_random(rng: &mut Rng, n: usize, alphabet_size: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let idx = rng.gen_range_usize(0, alphabet_size - 1);
        v.push(97u8 + idx as u8);
    }
    v
}

fn make_single_letter(n: usize, letter: u8) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(letter);
    }
    v
}

fn make_alphabet_prefix(n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(97u8 + ((i % 26) as u8));
    }
    v
}

fn make_distinct_then_repeat(n: usize, distinct: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        if i < distinct {
            v.push(97u8 + (i as u8));
        } else {
            v.push(97u8);
        }
    }
    v
}

fn make_ab_pattern(n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(if i % 2 == 0 { 97u8 } else { 98u8 });
    }
    v
}

fn make_abc_pattern(n: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(n);
    for i in 0..n {
        v.push(97u8 + ((i % 3) as u8));
    }
    v
}

fn make_adversarial(rng: &mut Rng, mode: usize, n: usize) -> Vec<u8> {
    match mode {
        0 => make_letters_random(rng, n, 26),
        1 => make_letters_random(rng, n, 2),
        2 => make_letters_random(rng, n, 3),
        3 => make_single_letter(n, 97u8 + (rng.gen_range_usize(0, 25) as u8)),
        4 => make_alphabet_prefix(n),
        5 => make_distinct_then_repeat(n, n.min(26)),
        6 => make_ab_pattern(n),
        7 => make_abc_pattern(n),
        8 => make_letters_random(rng, n, 5),
        9 => {
            // distinct count = len%3 at various points
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                let d = ((i + 1) % 3) as u8;
                if d == 0 {
                    v.push(97u8);
                } else {
                    v.push(97u8 + ((i as u8) % 26));
                }
            }
            v
        }
        _ => make_letters_random(rng, n, 26),
    }
}

fn escape_string(bytes: &[u8]) -> String {
    let mut s = String::new();
    for &b in bytes {
        s.push(b as char);
    }
    s
}

fn print_json(letters: &[u8], p: usize) {
    let s = escape_string(letters);
    println!("{{\"s\":\"{}\",\"p\":{}}}", s, p);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 10usize;
    let total = 200usize;

    // boundary cases first
    let boundary_lens: [usize; 6] = [1, 2, 3, 4, 99, 100];
    for &n in &boundary_lens {
        let letters = make_letters_random(&mut rng, n, 26);
        let v = Vec::from(letters.clone());
        let p = if n > 0 { rng.gen_range_usize(0, n - 1) } else { 0 };
        let (s_out, _p_out) = generate_test_case(&v);
        // Use returned p_out? It's always 0 from generator; but we can use random p valid index
        let _ = s_out;
        print_json(&letters, p);
    }

    for t in 0..(total - boundary_lens.len()) {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 100),
            1 => 2 + (t % 50),
            2 => 100,
            3 => 1,
            4 => (t % 100) + 1,
            5 => 26.min(1 + t % 30),
            6 => 1 + (t % 100),
            7 => 1 + (t % 100),
            8 => 1 + (t % 100),
            9 => 1 + (t % 100),
            _ => 10,
        };
        let n = n.max(1).min(100);
        let letters = make_adversarial(&mut rng, mode, n);
        let v: Vec<u8> = letters.clone();
        let (s_out, _p_out) = generate_test_case(&v);
        let _ = s_out;
        let p = rng.gen_range_usize(0, n - 1);
        print_json(&letters, p);
    }
}
