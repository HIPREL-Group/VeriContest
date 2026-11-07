use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    chars: Vec<char>,
    start: usize,
    end: usize,
) -> (res: (Vec<char>, usize, usize))
    requires
        1 <= chars.len() <= 100000,
        start <= chars.len(),
        end < chars.len(),
        start <= end + 1,
    ensures
        res.0.len() == chars.len(),
        1 <= res.0.len() <= 100000,
        res.1 == start,
        res.2 == end,
        res.1 <= res.0.len(),
        res.2 < res.0.len(),
        res.1 <= res.2 + 1,
{
    (chars, start, end)
}

pub fn generate_full_test_case(
    chars: Vec<char>,
) -> (res: Vec<char>)
    requires
        1 <= chars.len() <= 100000,
    ensures
        1 <= res.len() <= 100000,
{
    chars
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn random_char(&mut self) -> char {
        let c = (b'a' + (self.next_u64() % 26) as u8) as char;
        c
    }
}

fn make_palindrome(rng: &mut Rng, n: usize) -> Vec<char> {
    let mut v: Vec<char> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push('a');
    }
    for i in 0..n / 2 {
        let c = rng.random_char();
        v[i] = c;
        v[n - 1 - i] = c;
    }
    if n % 2 == 1 {
        v[n / 2] = rng.random_char();
    }
    v
}

fn make_palindrome_with_one_bad(rng: &mut Rng, n: usize) -> Vec<char> {
    let mut v = make_palindrome(rng, n);
    if n >= 2 {
        let pos = rng.gen_range_usize(0, n - 1);
        // insert a char at pos by replacing; but we want to "insert" so add and remove opposite
        // simplest: change one char so that removing it creates palindrome
        // Actually: take palindrome of length n-1, insert random at pos
        let base = make_palindrome(rng, n - 1);
        let ch = rng.random_char();
        let mut r: Vec<char> = Vec::with_capacity(n);
        for i in 0..n {
            if i < pos {
                r.push(base[i]);
            } else if i == pos {
                r.push(ch);
            } else {
                r.push(base[i - 1]);
            }
        }
        return r;
    }
    v
}

fn make_random(rng: &mut Rng, n: usize) -> Vec<char> {
    let mut v: Vec<char> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push(rng.random_char());
    }
    v
}

fn make_all_same(n: usize) -> Vec<char> {
    let mut v: Vec<char> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push('a');
    }
    v
}

fn make_two_chars(rng: &mut Rng, n: usize) -> Vec<char> {
    let mut v: Vec<char> = Vec::with_capacity(n);
    for _ in 0..n {
        let c = if rng.next_u64() % 2 == 0 { 'a' } else { 'b' };
        v.push(c);
    }
    v
}

fn print_json_full(chars: &[char]) {
    print!("{{\"s\":\"");
    for &c in chars {
        print!("{}", c);
    }
    println!("\"}}");
}

fn print_json_partial(chars: &[char], start: usize, end: usize) {
    print!("{{\"s\":\"");
    for &c in chars {
        print!("{}", c);
    }
    println!("\",\"start\":{},\"end\":{}}}", start, end);
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
        let mode = t % 10;
        let n = match mode {
            0 => 1,
            1 => 2,
            2 => 3,
            3 => rng.gen_range_usize(1, 20),
            4 => rng.gen_range_usize(50, 200),
            5 => rng.gen_range_usize(1000, 5000),
            6 => 100000,
            7 => rng.gen_range_usize(4, 50),
            8 => rng.gen_range_usize(10, 100),
            _ => rng.gen_range_usize(1, 1000),
        };

        let chars = match mode {
            0 | 3 => make_random(&mut rng, n),
            1 => make_all_same(n),
            2 => make_palindrome(&mut rng, n),
            4 => make_palindrome_with_one_bad(&mut rng, n),
            5 => make_two_chars(&mut rng, n),
            6 => make_palindrome(&mut rng, n),
            7 => make_palindrome_with_one_bad(&mut rng, n),
            8 => make_random(&mut rng, n),
            _ => make_random(&mut rng, n),
        };

        let verified = generate_full_test_case(chars);
        print_json_full(&verified);
    }
}