use vstd::prelude::*;

verus! {

pub fn generate_test_case(chars: &Vec<char>) -> (s: String)
    requires
        1 <= chars.len() <= 1_000,
        forall |i: int| 0 <= i < chars.len() ==> 
            (#[trigger] chars[i]) == 'A' || chars[i] == 'L' || chars[i] == 'P',
    ensures
        true,
{
    let mut s: String = String::new();
    s.append("P");
    s
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

fn random_chars(rng: &mut Rng, n: usize) -> Vec<char> {
    let mut v: Vec<char> = Vec::with_capacity(n);
    for _ in 0..n {
        let r = rng.gen_range_usize(0, 2);
        let c = match r {
            0 => 'A',
            1 => 'L',
            _ => 'P',
        };
        v.push(c);
    }
    v
}

fn biased_chars(rng: &mut Rng, n: usize, p_a: u32, p_l: u32) -> Vec<char> {
    let mut v: Vec<char> = Vec::with_capacity(n);
    for _ in 0..n {
        let r = (rng.next_u64() % 100) as u32;
        let c = if r < p_a {
            'A'
        } else if r < p_a + p_l {
            'L'
        } else {
            'P'
        };
        v.push(c);
    }
    v
}

fn adversarial_case(rng: &mut Rng, mode: usize) -> Vec<char> {
    match mode {
        0 => {
            // Single 'P'
            vec!['P']
        }
        1 => {
            // Single 'A'
            vec!['A']
        }
        2 => {
            // Single 'L'
            vec!['L']
        }
        3 => {
            // All 'L's -- definitely 3 consecutive
            let n = rng.gen_range_usize(3, 1000);
            (0..n).map(|_| 'L').collect()
        }
        4 => {
            // All 'A' -- many absences
            let n = rng.gen_range_usize(2, 1000);
            (0..n).map(|_| 'A').collect()
        }
        5 => {
            // Exactly 2 consecutive L's, never 3
            let n = rng.gen_range_usize(3, 1000);
            let mut v = Vec::with_capacity(n);
            for i in 0..n {
                if i % 3 == 2 { v.push('P'); } else { v.push('L'); }
            }
            v
        }
        6 => {
            // Exactly one A, no triple L
            let n = rng.gen_range_usize(1, 1000);
            let mut v: Vec<char> = (0..n).map(|_| 'P').collect();
            if n > 0 {
                let idx = rng.gen_range_usize(0, n - 1);
                v[idx] = 'A';
            }
            v
        }
        7 => {
            // Exactly 2 A's
            let n = rng.gen_range_usize(2, 1000);
            let mut v: Vec<char> = (0..n).map(|_| 'P').collect();
            let i = rng.gen_range_usize(0, n - 1);
            let mut j = rng.gen_range_usize(0, n - 1);
            if j == i { j = (j + 1) % n; }
            v[i] = 'A';
            v[j] = 'A';
            v
        }
        8 => {
            // "LLL" somewhere in middle
            let n = rng.gen_range_usize(3, 1000);
            let mut v: Vec<char> = (0..n).map(|_| 'P').collect();
            if n >= 3 {
                let start = rng.gen_range_usize(0, n - 3);
                v[start] = 'L';
                v[start + 1] = 'L';
                v[start + 2] = 'L';
            }
            v
        }
        9 => {
            // Biased heavy L's
            let n = rng.gen_range_usize(1, 1000);
            biased_chars(rng, n, 5, 80)
        }
        10 => {
            // Max length random
            random_chars(rng, 1000)
        }
        _ => {
            let n = rng.gen_range_usize(1, 1000);
            random_chars(rng, n)
        }
    }
}

fn escape_json(s: &str) -> String {
    let mut out = String::new();
    for c in s.chars() {
        match c {
            '"' => out.push_str("\\\""),
            '\\' => out.push_str("\\\\"),
            _ => out.push(c),
        }
    }
    out
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
        let chars = if t < modes * 5 {
            adversarial_case(&mut rng, t % modes)
        } else {
            let n = rng.gen_range_usize(1, 1000);
            random_chars(&mut rng, n)
        };
        let s = generate_test_case(&chars);
        println!("{{\"s\":\"{}\"}}", escape_json(&s));
    }
}
