use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    scores: &Vec<i32>,
    ages: &Vec<i32>,
) -> (res: (Vec<i32>, Vec<i32>))
    requires
        1 <= scores.len() <= 1000,
        scores.len() == ages.len(),
        forall|i: int| 0 <= i < scores.len() ==> 1 <= #[trigger] scores[i] <= 1_000_000,
        forall|i: int| 0 <= i < ages.len() ==> 1 <= #[trigger] ages[i] <= 1000,
    ensures
        1 <= res.0.len() <= 1000,
        res.0.len() == res.1.len(),
        forall|i: int| 0 <= i < res.0.len() ==> 1 <= #[trigger] res.0[i] <= 1_000_000,
        forall|i: int| 0 <= i < res.1.len() ==> 1 <= #[trigger] res.1[i] <= 1000,
{
    let mut s_out: Vec<i32> = Vec::new();
    let mut a_out: Vec<i32> = Vec::new();
    let n = scores.len();
    let mut i: usize = 0;
    while i < n
        invariant
            n == scores.len(),
            scores.len() == ages.len(),
            0 <= i <= n,
            s_out.len() == i,
            a_out.len() == i,
            forall|k: int| 0 <= k < i as int ==> #[trigger] s_out[k] == scores[k],
            forall|k: int| 0 <= k < i as int ==> #[trigger] a_out[k] == ages[k],
            forall|k: int| 0 <= k < scores.len() ==> 1 <= #[trigger] scores[k] <= 1_000_000,
            forall|k: int| 0 <= k < ages.len() ==> 1 <= #[trigger] ages[k] <= 1000,
        decreases n - i,
    {
        s_out.push(scores[i]);
        a_out.push(ages[i]);
        i = i + 1;
    }
    (s_out, a_out)
}

} // verus!

struct Rng { state: u64 }

impl Rng {
    fn new(seed: u64) -> Self { Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) } }
    fn next_u64(&mut self) -> u64 {
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
    fn range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn gen_mode(rng: &mut Rng, mode: usize) -> (Vec<i32>, Vec<i32>) {
    let (scores, ages) = match mode {
        0 => {
            // single element
            (vec![rng.range_i32(1, 1_000_000)], vec![rng.range_i32(1, 1000)])
        }
        1 => {
            // all same age
            let n = rng.range_usize(1, 1000);
            let age = rng.range_i32(1, 1000);
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(rng.range_i32(1, 1_000_000));
                a.push(age);
            }
            (s, a)
        }
        2 => {
            // sorted ages ascending scores ascending (no conflicts)
            let n = rng.range_usize(1, 1000);
            let mut s = Vec::new();
            let mut a = Vec::new();
            let mut cur_age = 1i32;
            let mut cur_score = 1i32;
            for _ in 0..n {
                cur_age = (cur_age + rng.range_i32(0, 2)).min(1000);
                cur_score = (cur_score + rng.range_i32(0, 100)).min(1_000_000);
                s.push(cur_score.max(1));
                a.push(cur_age.max(1));
            }
            (s, a)
        }
        3 => {
            // adversarial: older with lower score, younger with higher
            let n = rng.range_usize(2, 1000);
            let mut s = Vec::new();
            let mut a = Vec::new();
            for i in 0..n {
                s.push(((n - i) as i32 * 100).max(1).min(1_000_000));
                a.push(((i + 1) as i32).min(1000));
            }
            (s, a)
        }
        4 => {
            // max values
            let n = 1000usize;
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(1_000_000);
                a.push(1000);
            }
            (s, a)
        }
        5 => {
            // min values
            let n = 1000usize;
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(1);
                a.push(1);
            }
            (s, a)
        }
        6 => {
            // random small
            let n = rng.range_usize(1, 20);
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(rng.range_i32(1, 100));
                a.push(rng.range_i32(1, 10));
            }
            (s, a)
        }
        7 => {
            // two age groups
            let n = rng.range_usize(2, 500);
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(rng.range_i32(1, 1_000_000));
                a.push(if rng.next_u64() % 2 == 0 { 1 } else { 1000 });
            }
            (s, a)
        }
        8 => {
            // n=1000 random
            let n = 1000usize;
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(rng.range_i32(1, 1_000_000));
                a.push(rng.range_i32(1, 1000));
            }
            (s, a)
        }
        9 => {
            // same score varying age
            let n = rng.range_usize(1, 500);
            let score = rng.range_i32(1, 1_000_000);
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(score);
                a.push(rng.range_i32(1, 1000));
            }
            (s, a)
        }
        _ => {
            let n = rng.range_usize(1, 1000);
            let mut s = Vec::new();
            let mut a = Vec::new();
            for _ in 0..n {
                s.push(rng.range_i32(1, 1_000_000));
                a.push(rng.range_i32(1, 1000));
            }
            (s, a)
        }
    };
    scores_ages_clamp(scores, ages)
}

fn scores_ages_clamp(mut s: Vec<i32>, mut a: Vec<i32>) -> (Vec<i32>, Vec<i32>) {
    if s.is_empty() {
        s.push(1);
        a.push(1);
    }
    if s.len() > 1000 { s.truncate(1000); }
    if a.len() > 1000 { a.truncate(1000); }
    while a.len() > s.len() { a.pop(); }
    while s.len() > a.len() { s.pop(); }
    for v in s.iter_mut() {
        if *v < 1 { *v = 1; }
        if *v > 1_000_000 { *v = 1_000_000; }
    }
    for v in a.iter_mut() {
        if *v < 1 { *v = 1; }
        if *v > 1000 { *v = 1000; }
    }
    (s, a)
}

fn print_json(scores: &[i32], ages: &[i32]) {
    print!("{{\"scores\":[");
    for i in 0..scores.len() {
        if i > 0 { print!(","); }
        print!("{}", scores[i]);
    }
    print!("],\"ages\":[");
    for i in 0..ages.len() {
        if i > 0 { print!(","); }
        print!("{}", ages[i]);
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
    let total = 220usize;
    for t in 0..total {
        let mode = t % modes;
        let (s, a) = gen_mode(&mut rng, mode);
        // verify all elements valid (they should be by construction)
        let (s2, a2) = generate_test_case(&s, &a);
        print_json(&s2, &a2);
    }
}