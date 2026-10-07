use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    s: &mut Vec<char>,
    mutation_kind: u8,
)
    requires
        1 <= old(s).len() <= 100000,
        forall|i: int| 0 <= i < old(s).len() ==> ' ' <= #[trigger] old(s)[i] <= '~',
    ensures
        1 <= old(s).len() <= 100000,
        forall|i: int| 0 <= i < old(s).len() ==> ' ' <= #[trigger] old(s)[i] <= '~',
        1 <= s.len() <= 100000,
        forall|i: int| 0 <= i < s.len() ==> ' ' <= #[trigger] s[i] <= '~',
{
    if mutation_kind == 0 {
        // identity — no change
    } else if mutation_kind == 1 && s.len() > 1 {
        // swap first and last characters
        let last = s.len() - 1;
        let c0 = s[0];
        let cl = s[last];
        s.set(0, cl);
        s.set(last, c0);
    } else if mutation_kind == 2 && s.len() < 100000 {
        // grow by one: push 'a'
        s.push('a');
    } else if mutation_kind == 3 && s.len() > 1 {
        // shrink by one: pop last element
        s.pop();
    } else if mutation_kind == 4 {
        // set first char to ' ' (min printable ASCII)
        s.set(0, ' ');
    } else if mutation_kind == 5 {
        // set first char to '~' (max printable ASCII)
        s.set(0, '~');
    } else if mutation_kind == 6 {
        // set all chars to 'x'
        let mut i: usize = 0;
        while i < s.len()
            invariant
                0 <= i <= s.len(),
                s.len() == old(s).len(),
                forall|j: int| 0 <= j < i ==> s[j] == 'x',
                forall|j: int| i <= j < s.len() as int ==> s[j] == old(s)[j],
            decreases s.len() - i,
        {
            s.set(i, 'x');
            i += 1;
        }
    } else if mutation_kind == 7 && s.len() > 1 {
        // swap adjacent pair at index 0 and 1
        let c0 = s[0];
        let c1 = s[1];
        s.set(0, c1);
        s.set(1, c0);
    } else {
        // fallback — no change
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

struct Solution;
include!("../code.rs");

fn random_chars(rng: &mut Rng, len: usize) -> Vec<char> {
    let mut v = Vec::with_capacity(len);
    for _ in 0..len {
        let c = rng.gen_range_i64(' ' as i64, '~' as i64) as u8 as char;
        v.push(c);
    }
    v
}

fn mutate(mut s: Vec<char>, mutation_kind: u8) -> Vec<char> {
    generate_test_case(&mut s, mutation_kind);
    s
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(344);
    let target: usize = args.get(2).and_then(|s| s.parse().ok()).unwrap_or(100);

    let mut rng = Rng::new(seed);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;

    let mut emit = |s: Vec<char>, seen: &mut HashSet<String>, out: &mut std::io::BufWriter<std::fs::File>, count: &mut usize| {
        if *count >= target {
            return;
        }
        let key = format!("{:?}", s);
        if !seen.insert(key) {
            return;
        }
        let input_s: Vec<String> = s.iter().map(|c| c.to_string()).collect();
        let mut s_mut = s;
        Solution::reverse_string(&mut s_mut);
        let output_s: Vec<String> = s_mut.iter().map(|c| c.to_string()).collect();
        writeln!(out, "{}", json!({"input": {"s": input_s}, "output": output_s})).unwrap();
        *count += 1;
    };

    // Example inputs from description.md
    let examples: Vec<Vec<char>> = vec![
        vec!['h', 'e', 'l', 'l', 'o'],
        vec!['H', 'a', 'n', 'n', 'a', 'h'],
    ];
    for ex in &examples {
        emit(ex.clone(), &mut seen, &mut out, &mut count);
    }

    // Seed pool: interesting base strings
    let seeds: Vec<Vec<char>> = vec![
        vec!['a'],                                 // single char
        vec![' '],                                 // min printable
        vec!['~'],                                 // max printable
        vec!['a', 'b'],                            // two chars
        vec!['a', 'a', 'a'],                       // all same
        vec!['a', 'b', 'c', 'd', 'e'],            // ascending
        vec!['z', 'y', 'x', 'w', 'v'],            // descending
        vec![' ', '~', ' ', '~'],                  // boundary alternation
        vec!['A', 'B', 'C', 'D', 'E', 'F', 'G', 'H', 'I', 'J'], // 10 chars
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7];

    // Apply every mutation to every seed
    for s in &seeds {
        for &mk in &mutation_kinds {
            let result = mutate(s.clone(), mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random inputs with diverse size classes
    while count < target {
        let n: usize = match count % 5 {
            0 => rng.gen_range_usize(1, 5),        // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // very large
        };
        let s = random_chars(&mut rng, n);
        let mk = rng.gen_range_usize(0, 7) as u8;
        let result = mutate(s, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
