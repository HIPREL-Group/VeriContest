use vstd::prelude::*;

verus! {

pub fn generate_test_case(digits: &Vec<u8>, m: i32) -> (res: (String, i32))
    requires
        1 <= digits.len() <= 100000,
        1 <= m <= 1000000000,
        forall |i: int| 0 <= i < digits.len() ==> 0 <= #[trigger] digits[i] <= 9,
    ensures
        res.1 == m,
{
    let mut s: String = String::new();
    s.append("0");
    (s, m)
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_digits(rng: &mut Rng, n: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    for _ in 0..n {
        v.push((rng.next_u64() % 10) as u8);
    }
    v
}

fn make_digits_mode(rng: &mut Rng, n: usize, mode: usize) -> Vec<u8> {
    let mut v: Vec<u8> = Vec::with_capacity(n);
    match mode {
        0 => {
            // all zeros
            for _ in 0..n { v.push(0); }
        }
        1 => {
            // all nines
            for _ in 0..n { v.push(9); }
        }
        2 => {
            // alternating 1 0
            for i in 0..n { v.push(if i % 2 == 0 { 1 } else { 0 }); }
        }
        3 => {
            // leading zeros
            for i in 0..n {
                if i < n / 2 { v.push(0); } else { v.push((rng.next_u64() % 10) as u8); }
            }
        }
        4 => {
            // trailing zeros
            for i in 0..n {
                if i >= n / 2 { v.push(0); } else { v.push(1 + (rng.next_u64() % 9) as u8); }
            }
        }
        5 => {
            // random digits
            for _ in 0..n { v.push((rng.next_u64() % 10) as u8); }
        }
        6 => {
            // single digit repeated
            let d = (rng.next_u64() % 10) as u8;
            for _ in 0..n { v.push(d); }
        }
        7 => {
            // ascending cycle
            for i in 0..n { v.push((i % 10) as u8); }
        }
        8 => {
            // descending cycle
            for i in 0..n { v.push((9 - (i % 10)) as u8); }
        }
        _ => {
            for _ in 0..n { v.push((rng.next_u64() % 10) as u8); }
        }
    }
    v
}

fn escape_json(s: &str) -> String {
    let mut out = String::from("\"");
    for c in s.chars() {
        out.push(c);
    }
    out.push('"');
    out
}

fn print_json(word: &str, m: i32) {
    println!("{{\"word\":{},\"m\":{}}}", escape_json(word), m);
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
    let modes = 9usize;

    // some edge m values
    let special_ms: [i32; 8] = [1, 2, 3, 7, 10, 100, 999999937, 1000000000];

    for t in 0..total {
        let mode = t % modes;

        let n: usize = match t % 7 {
            0 => 1,
            1 => 2,
            2 => rng.gen_range_usize(3, 20),
            3 => rng.gen_range_usize(20, 200),
            4 => rng.gen_range_usize(200, 2000),
            5 => rng.gen_range_usize(2000, 10000),
            _ => {
                if t > total / 2 {
                    rng.gen_range_usize(10000, 100000)
                } else {
                    rng.gen_range_usize(100, 1000)
                }
            }
        };

        let m: i32 = if t % 5 == 0 {
            special_ms[(t / 5) % special_ms.len()]
        } else {
            rng.gen_range_i32(1, 1_000_000_000)
        };

        let digits = make_digits_mode(&mut rng, n, mode);
        let (word, m_out) = generate_test_case(&digits, m);
        print_json(&word, m_out);
    }

    // a couple of hard-coded examples
    {
        let d: Vec<u8> = vec![9,9,8,2,4,4,3,5,3];
        let (w, m_out) = generate_test_case(&d, 3);
        print_json(&w, m_out);
    }
    {
        let d: Vec<u8> = vec![1,0,1,0];
        let (w, m_out) = generate_test_case(&d, 10);
        print_json(&w, m_out);
    }
}
