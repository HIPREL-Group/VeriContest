use vstd::prelude::*;

verus! {

pub open spec fn all_lowercase(v: Seq<char>) -> bool {
    forall |i: int| 0 <= i < v.len() ==> 97 <= (#[trigger] v[i] as u32) && (v[i] as u32) <= 122
}

pub fn generate_test_case(
    s_chars: &Vec<u8>,
    t_chars: &Vec<u8>,
) -> (res: (Vec<char>, Vec<char>))
    requires
        1 <= s_chars.len() <= 50_000,
        1 <= t_chars.len() <= 50_000,
        forall |i: int| 0 <= i < s_chars.len() ==> 97 <= #[trigger] s_chars[i] <= 122,
        forall |i: int| 0 <= i < t_chars.len() ==> 97 <= #[trigger] t_chars[i] <= 122,
    ensures
        1 <= res.0.len() <= 50_000,
        1 <= res.1.len() <= 50_000,
        res.0.len() == s_chars.len(),
        res.1.len() == t_chars.len(),
        forall |i: int| 0 <= i < res.0.len() ==> 97 <= (#[trigger] res.0[i] as u32) && (res.0[i] as u32) <= 122,
        forall |i: int| 0 <= i < res.1.len() ==> 97 <= (#[trigger] res.1[i] as u32) && (res.1[i] as u32) <= 122,
{
    let mut s_vec: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s_chars.len()
        invariant
            0 <= i <= s_chars.len(),
            s_vec.len() == i,
            forall |k: int| 0 <= k < s_chars.len() ==> 97 <= #[trigger] s_chars[k] <= 122,
            forall |k: int| 0 <= k < i as int ==> 97 <= (#[trigger] s_vec[k] as u32) && (s_vec[k] as u32) <= 122,
        decreases s_chars.len() - i,
    {
        let b = s_chars[i];
        let c: char = b as char;
        assert((c as u32) == (b as u32));
        s_vec.push(c);
        i = i + 1;
    }

    let mut t_vec: Vec<char> = Vec::new();
    let mut j: usize = 0;
    while j < t_chars.len()
        invariant
            0 <= j <= t_chars.len(),
            t_vec.len() == j,
            forall |k: int| 0 <= k < t_chars.len() ==> 97 <= #[trigger] t_chars[k] <= 122,
            forall |k: int| 0 <= k < j as int ==> 97 <= (#[trigger] t_vec[k] as u32) && (t_vec[k] as u32) <= 122,
        decreases t_chars.len() - j,
    {
        let b = t_chars[j];
        let c: char = b as char;
        assert((c as u32) == (b as u32));
        t_vec.push(c);
        j = j + 1;
    }

    (s_vec, t_vec)
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_letter(&mut self) -> u8 {
        97 + (self.next_u64() as u8 % 26)
    }
}

fn random_word(rng: &mut Rng, len: usize) -> Vec<u8> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        v.push(rng.gen_letter());
    }
    v
}

fn shuffle(rng: &mut Rng, v: &mut Vec<u8>) {
    let n = v.len();
    if n <= 1 {
        return;
    }
    for i in (1..n).rev() {
        let j = (rng.next_u64() as usize) % (i + 1);
        v.swap(i, j);
    }
}

fn print_json(s: &[char], t: &[char]) {
    print!("{{\"s\":\"");
    for c in s {
        print!("{}", c);
    }
    print!("\",\"t\":\"");
    for c in t {
        print!("{}", c);
    }
    println!("\"}}");
}

fn make_test(rng: &mut Rng, mode: usize, idx: usize) -> (Vec<u8>, Vec<u8>) {
    match mode {
        0 => {
            // Both length 1 equal
            let c = rng.gen_letter();
            (vec![c], vec![c])
        }
        1 => {
            // Both length 1 different
            let c1 = rng.gen_letter();
            let mut c2 = rng.gen_letter();
            if c2 == c1 {
                c2 = 97 + ((c1 - 97 + 1) % 26);
            }
            (vec![c1], vec![c2])
        }
        2 => {
            // Anagram: same characters shuffled
            let n = rng.gen_range_usize(2, 50);
            let s = random_word(rng, n);
            let mut t = s.clone();
            shuffle(rng, &mut t);
            (s, t)
        }
        3 => {
            // Same string
            let n = rng.gen_range_usize(1, 100);
            let s = random_word(rng, n);
            let t = s.clone();
            (s, t)
        }
        4 => {
            // Different lengths
            let n1 = rng.gen_range_usize(1, 50);
            let n2 = rng.gen_range_usize(1, 50);
            let n2 = if n2 == n1 { n2 + 1 } else { n2 };
            (random_word(rng, n1), random_word(rng, n2.min(50_000)))
        }
        5 => {
            // Same length, different counts (one char changed)
            let n = rng.gen_range_usize(2, 100);
            let s = random_word(rng, n);
            let mut t = s.clone();
            let pos = rng.gen_range_usize(0, n - 1);
            t[pos] = 97 + ((t[pos] - 97 + 1) % 26);
            (s, t)
        }
        6 => {
            // All same character
            let c = rng.gen_letter();
            let n = rng.gen_range_usize(1, 100);
            (vec![c; n], vec![c; n])
        }
        7 => {
            // Max length anagrams
            let n = 50_000;
            let s = random_word(rng, n);
            let mut t = s.clone();
            shuffle(rng, &mut t);
            (s, t)
        }
        8 => {
            // Max length, one differing char
            let n = 50_000;
            let s = random_word(rng, n);
            let mut t = s.clone();
            let pos = rng.gen_range_usize(0, n - 1);
            t[pos] = 97 + ((t[pos] - 97 + 1) % 26);
            (s, t)
        }
        9 => {
            // All 26 letters each
            let mut s: Vec<u8> = (97..123).collect();
            let mut t = s.clone();
            shuffle(rng, &mut s);
            shuffle(rng, &mut t);
            (s, t)
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            let m = rng.gen_range_usize(1, 200);
            let _ = idx;
            (random_word(rng, n), random_word(rng, m))
        }
    }
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

    for i in 0..total {
        let mode = i % modes;
        let (s_bytes, t_bytes) = make_test(&mut rng, mode, i);

        // Clamp to valid ranges just to be safe
        if s_bytes.is_empty() || t_bytes.is_empty() || s_bytes.len() > 50_000 || t_bytes.len() > 50_000 {
            continue;
        }
        let mut ok = true;
        for &b in &s_bytes {
            if !(97..=122).contains(&b) { ok = false; break; }
        }
        if ok {
            for &b in &t_bytes {
                if !(97..=122).contains(&b) { ok = false; break; }
            }
        }
        if !ok {
            continue;
        }

        let (s_vec, t_vec) = generate_test_case(&s_bytes, &t_bytes);
        print_json(&s_vec, &t_vec);
    }
}