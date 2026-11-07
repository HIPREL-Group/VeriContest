use vstd::prelude::*;

verus! {

pub fn generate_test_case(choices: Vec<u8>, mutation_kind: u8) -> (result: Vec<char>)
    requires
        1 <= choices.len() <= 100_000,
        forall|i: int| 0 <= i < choices.len() ==> choices[i] == 0u8 || choices[i] == 1u8,
    ensures
        1 <= result@.len() <= 100_000,
        forall|i: int| 0 <= i < result@.len() ==> result@[i] == 'Y' || result@[i] == 'N',
{
    // Build Vec<char> from choices (0 -> 'N', 1 -> 'Y')
    let mut result: Vec<char> = Vec::new();
    let mut idx: usize = 0;
    while idx < choices.len()
        invariant
            idx <= choices.len(),
            result.len() == idx,
            1 <= choices.len() <= 100_000,
            forall|j: int| 0 <= j < idx as int ==> result@[j] == 'Y' || result@[j] == 'N',
            forall|j: int| 0 <= j < choices.len() as int ==> choices[j] == 0u8 || choices[j] == 1u8,
        decreases choices.len() - idx,
    {
        if choices[idx] == 1u8 {
            result.push('Y');
        } else {
            result.push('N');
        }
        idx += 1;
    }

    if mutation_kind == 0 {
        // identity
        result
    } else if mutation_kind == 1 {
        // flip first character
        if result[0] == 'Y' {
            result.set(0, 'N');
        } else {
            result.set(0, 'Y');
        }
        result
    } else if mutation_kind == 2 {
        // flip last character
        let last = result.len() - 1;
        if result[last] == 'Y' {
            result.set(last, 'N');
        } else {
            result.set(last, 'Y');
        }
        result
    } else if mutation_kind == 3 {
        // set all to 'Y'
        let mut i: usize = 0;
        while i < result.len()
            invariant
                i <= result.len(),
                result.len() == choices.len(),
                1 <= result.len() <= 100_000,
                forall|j: int| 0 <= j < i as int ==> result@[j] == 'Y',
                forall|j: int| i as int <= j < result.len() as int
                    ==> result@[j] == 'Y' || result@[j] == 'N',
            decreases result.len() - i,
        {
            result.set(i, 'Y');
            i += 1;
        }
        result
    } else if mutation_kind == 4 {
        // set all to 'N'
        let mut i: usize = 0;
        while i < result.len()
            invariant
                i <= result.len(),
                result.len() == choices.len(),
                1 <= result.len() <= 100_000,
                forall|j: int| 0 <= j < i as int ==> result@[j] == 'N',
                forall|j: int| i as int <= j < result.len() as int
                    ==> result@[j] == 'Y' || result@[j] == 'N',
            decreases result.len() - i,
        {
            result.set(i, 'N');
            i += 1;
        }
        result
    } else if mutation_kind == 5 && result.len() < 100_000 {
        // grow by one (push 'Y')
        result.push('Y');
        result
    } else if mutation_kind == 6 && result.len() > 1 {
        // shrink by one (pop last)
        result.pop();
        result
    } else {
        // fallback: identity
        result
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

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn best_closing_time_impl(customers: &str) -> i32 {
    let mut score: i32 = 0;
    let mut best_score: i32 = 0;
    let mut best_hour: usize = 0;
    for (i, c) in customers.chars().enumerate() {
        if c == 'Y' {
            score += 1;
        } else {
            score -= 1;
        }
        if best_score < score {
            best_score = score;
            best_hour = i + 1;
        }
    }
    best_hour as i32
}

fn make_choices(s: &str) -> Vec<u8> {
    s.chars().map(|c| if c == 'Y' { 1u8 } else { 0u8 }).collect()
}

fn random_choices(rng: &mut Rng, len: usize) -> Vec<u8> {
    (0..len).map(|_| rng.gen_range_usize(0, 1) as u8).collect()
}

fn chars_to_string(chars: &[char]) -> String {
    chars.iter().collect()
}

extern crate serde_json;
use serde_json::json;

fn main() {
    use std::io::Write;
    use std::collections::HashSet;
    let mut rng = Rng::new(2483);
    let out_path = std::path::Path::new(file!()).parent().unwrap().join("testcases.jsonl");
    let file = std::fs::File::create(&out_path).unwrap();
    let mut out = std::io::BufWriter::new(file);
    let mut seen = HashSet::new();
    let mut count = 0usize;
    let target = 100;

    let mut emit = |chars: Vec<char>,
                    seen: &mut HashSet<String>,
                    out: &mut std::io::BufWriter<std::fs::File>,
                    count: &mut usize| {
        if *count >= target {
            return;
        }
        let s = chars_to_string(&chars);
        if !seen.insert(s.clone()) {
            return;
        }
        let output = best_closing_time_impl(&s);
        writeln!(out, "{}", json!({"input": {"customers": s}, "output": output})).unwrap();
        *count += 1;
    };

    // Example test cases from description.md
    let example_seeds: Vec<&str> = vec![
        "YYNY",   // -> 2
        "NNNNN",  // -> 0
        "YYYY",   // -> 4
    ];

    // Interesting pattern seeds
    let pattern_seeds: Vec<&str> = vec![
        "Y",
        "N",
        "YN",
        "NY",
        "YY",
        "NN",
        "YNYNYN",
        "NYNYNY",
        "YYYNNN",
        "NNNYYY",
        "YYYYYYYYYYN",
        "NYYYYYYYYY",
        "YNNNNNNNNN",
        "NNNNNNNNNY",
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6];

    // Emit example seeds with all mutations
    for seed_str in &example_seeds {
        for &mk in &mutation_kinds {
            let choices = make_choices(seed_str);
            let result = generate_test_case(choices, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Emit pattern seeds with all mutations
    for seed_str in &pattern_seeds {
        for &mk in &mutation_kinds {
            let choices = make_choices(seed_str);
            let result = generate_test_case(choices, mk);
            emit(result, &mut seen, &mut out, &mut count);
        }
    }

    // Random seeds with size classes and random mutations
    for i in 0..200 {
        if count >= target {
            break;
        }
        let len: usize = match i % 5 {
            0 => rng.gen_range_usize(1, 5),       // tiny
            1 => rng.gen_range_usize(1, 10),       // small
            2 => rng.gen_range_usize(11, 100),     // medium
            3 => rng.gen_range_usize(101, 1000),   // large
            _ => rng.gen_range_usize(1001, 10000), // xlarge
        };
        let choices = random_choices(&mut rng, len);
        let mk = rng.gen_range_usize(0, 6) as u8;
        let result = generate_test_case(choices, mk);
        emit(result, &mut seen, &mut out, &mut count);
    }

    // Fill remaining with random identity
    while count < target {
        let len = rng.gen_range_usize(1, 50000);
        let choices = random_choices(&mut rng, len);
        let result = generate_test_case(choices, 0);
        emit(result, &mut seen, &mut out, &mut count);
    }
}
