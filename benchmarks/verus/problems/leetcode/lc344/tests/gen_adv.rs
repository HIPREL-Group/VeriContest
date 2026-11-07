use vstd::prelude::*;

verus! {

pub fn generate_test_case(chars: Vec<char>) -> (s: Vec<char>)
    requires
        1 <= chars.len() <= 100000,
        forall|i: int| 0 <= i < chars.len() ==> ' ' <= #[trigger] chars[i] <= '~',
    ensures
        1 <= s.len() <= 100000,
        forall|i: int| 0 <= i < s.len() ==> ' ' <= #[trigger] s[i] <= '~',
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn random_printable(&mut self) -> char {
        let v = self.gen_range_usize(0x20, 0x7E);
        v as u8 as char
    }
}

fn make_chars(rng: &mut Rng, mode: usize, n: usize) -> Vec<char> {
    let mut v: Vec<char> = Vec::with_capacity(n);
    match mode {
        0 => {
            for _ in 0..n {
                v.push(rng.random_printable());
            }
        }
        1 => {
            for _ in 0..n {
                v.push(' ');
            }
        }
        2 => {
            for _ in 0..n {
                v.push('~');
            }
        }
        3 => {
            for i in 0..n {
                let c = if i % 2 == 0 { 'a' } else { 'b' };
                v.push(c);
            }
        }
        4 => {
            let s = "hello";
            let bytes = s.as_bytes();
            for i in 0..n {
                v.push(bytes[i % bytes.len()] as char);
            }
        }
        5 => {
            let s = "Hannah";
            let bytes = s.as_bytes();
            for i in 0..n {
                v.push(bytes[i % bytes.len()] as char);
            }
        }
        6 => {
            for i in 0..n {
                let c = (0x20 + (i % 95)) as u8 as char;
                v.push(c);
            }
        }
        7 => {
            // palindrome
            let half = n / 2;
            let mut left: Vec<char> = Vec::new();
            for _ in 0..half {
                left.push(rng.random_printable());
            }
            for c in &left {
                v.push(*c);
            }
            if n % 2 == 1 {
                v.push(rng.random_printable());
            }
            for i in 0..half {
                v.push(left[half - 1 - i]);
            }
        }
        8 => {
            for _ in 0..n {
                v.push('A');
            }
        }
        9 => {
            // digits
            for i in 0..n {
                v.push(((b'0' + (i % 10) as u8)) as char);
            }
        }
        _ => {
            for _ in 0..n {
                let r = rng.gen_range_usize(0, 2);
                let c = match r {
                    0 => rng.random_printable(),
                    1 => ' ',
                    _ => '~',
                };
                v.push(c);
            }
        }
    }
    v
}

fn escape_char(c: char) -> String {
    match c {
        '"' => "\\\"".to_string(),
        '\\' => "\\\\".to_string(),
        _ => c.to_string(),
    }
}

fn print_json(s: &[char]) {
    print!("{{\"s\":[");
    for i in 0..s.len() {
        if i > 0 {
            print!(",");
        }
        print!("\"{}\"", escape_char(s[i]));
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let n = match mode {
            0 => 1 + (t % 20),
            1 => 1,
            2 => 2,
            3 => 3 + (t % 10),
            4 => 5,
            5 => 6,
            6 => 50 + (t % 50),
            7 => 7 + (t % 15),
            8 => 100000,
            9 => 10 + (t % 30),
            _ => {
                let r = rng.gen_range_usize(1, 1000);
                r
            }
        };
        let n = if n < 1 { 1 } else if n > 100000 { 100000 } else { n };

        let chars = make_chars(&mut rng, mode, n);
        let s = generate_test_case(chars);
        print_json(&s);
    }
}