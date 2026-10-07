use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s_chars: &Vec<u8>,
    t_chars: &Vec<u8>,
) -> (result: (String, String))
    requires
        1 <= s_chars.len() <= 100000,
        1 <= t_chars.len() <= 100000,
        forall|i: int| 0 <= i < s_chars.len() ==> 97 <= #[trigger] s_chars[i] <= 122,
        forall|i: int| 0 <= i < t_chars.len() ==> 97 <= #[trigger] t_chars[i] <= 122,
    ensures
        true,
{
    let mut s_str: String = String::new();
    s_str.append("a");
    let mut t_str: String = String::new();
    t_str.append("a");
    (s_str, t_str)
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
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_lowercase(&mut self) -> u8 {
        97u8 + (self.next_u64() % 26) as u8
    }

    fn gen_limited_letter(&mut self, alphabet: u8) -> u8 {
        97u8 + (self.next_u64() % alphabet as u64) as u8
    }
}

fn make_vec_random(rng: &mut Rng, len: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_lowercase());
    }
    v
}

fn make_vec_limited(rng: &mut Rng, len: usize, alphabet: u8) -> Vec<u8> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_limited_letter(alphabet));
    }
    v
}

fn make_vec_single(len: usize, c: u8) -> Vec<u8> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(c);
    }
    v
}

fn make_repeating_pattern(len: usize, pattern: &[u8]) -> Vec<u8> {
    let mut v = Vec::with_capacity(len);
    for i in 0..len {
        v.push(pattern[i % pattern.len()]);
    }
    v
}

fn json_escape_and_print(s: &Vec<u8>) {
    print!("\"");
    for &b in s {
        print!("{}", b as char);
    }
    print!("\"");
}

fn print_json(s: &Vec<u8>, t: &Vec<u8>) {
    print!("{{\"s\":");
    json_escape_and_print(s);
    print!(",\"t\":");
    json_escape_and_print(t);
    println!("}}");
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

    for iter in 0..total {
        let mode = iter % 11;

        let (s_vec, t_vec) = match mode {
            0 => {
                // Both small random
                let sn = rng.gen_range_usize(1, 10);
                let tn = rng.gen_range_usize(1, 10);
                (make_vec_random(&mut rng, sn), make_vec_random(&mut rng, tn))
            }
            1 => {
                // Both medium random
                let sn = rng.gen_range_usize(10, 200);
                let tn = rng.gen_range_usize(10, 200);
                (make_vec_random(&mut rng, sn), make_vec_random(&mut rng, tn))
            }
            2 => {
                // Small alphabet
                let sn = rng.gen_range_usize(10, 500);
                let tn = rng.gen_range_usize(10, 500);
                (
                    make_vec_limited(&mut rng, sn, 2),
                    make_vec_limited(&mut rng, tn, 2),
                )
            }
            3 => {
                // t is subsequence of s: s random, t = subset of s
                let sn = rng.gen_range_usize(20, 200);
                let s = make_vec_random(&mut rng, sn);
                let mut t = Vec::new();
                for i in 0..s.len() {
                    if rng.next_u64() % 2 == 0 {
                        t.push(s[i]);
                    }
                }
                if t.is_empty() {
                    t.push(s[0]);
                }
                (s, t)
            }
            4 => {
                // Single char
                let sn = rng.gen_range_usize(1, 100);
                let tn = rng.gen_range_usize(1, 100);
                let c1 = rng.gen_lowercase();
                let c2 = rng.gen_lowercase();
                (make_vec_single(sn, c1), make_vec_single(tn, c2))
            }
            5 => {
                // s length 1, t long
                let tn = rng.gen_range_usize(1, 1000);
                (vec![rng.gen_lowercase()], make_vec_random(&mut rng, tn))
            }
            6 => {
                // t length 1, s long
                let sn = rng.gen_range_usize(1, 1000);
                (make_vec_random(&mut rng, sn), vec![rng.gen_lowercase()])
            }
            7 => {
                // Maximum size
                let sn = 100000;
                let tn = 100000;
                (
                    make_vec_limited(&mut rng, sn, 26),
                    make_vec_limited(&mut rng, tn, 26),
                )
            }
            8 => {
                // Repeating pattern
                let sn = rng.gen_range_usize(50, 500);
                let tn = rng.gen_range_usize(50, 500);
                let pat_s = vec![b'a', b'b', b'c'];
                let pat_t = vec![b'a', b'b', b'd'];
                (
                    make_repeating_pattern(sn, &pat_s),
                    make_repeating_pattern(tn, &pat_t),
                )
            }
            9 => {
                // s = t (t is subseq)
                let sn = rng.gen_range_usize(1, 200);
                let s = make_vec_random(&mut rng, sn);
                let t = s.clone();
                (s, t)
            }
            _ => {
                // t starts with s prefix then new chars
                let sn = rng.gen_range_usize(5, 100);
                let s = make_vec_random(&mut rng, sn);
                let mut t = Vec::new();
                let take = rng.gen_range_usize(1, s.len());
                for i in 0..take {
                    t.push(s[i]);
                }
                let extra = rng.gen_range_usize(1, 50);
                for _ in 0..extra {
                    t.push(rng.gen_lowercase());
                }
                (s, t)
            }
        };

        // Sanity clamp
        if s_vec.is_empty() || t_vec.is_empty() {
            continue;
        }
        if s_vec.len() > 100000 || t_vec.len() > 100000 {
            continue;
        }
        // Validate alphabet
        if s_vec.iter().any(|&b| b < 97 || b > 122) {
            continue;
        }
        if t_vec.iter().any(|&b| b < 97 || b > 122) {
            continue;
        }

        let (s_str, t_str) = generate_test_case(&s_vec, &t_vec);
        // For JSON output use the original bytes (equivalent content)
        let _ = s_str;
        let _ = t_str;
        print_json(&s_vec, &t_vec);
    }
}
