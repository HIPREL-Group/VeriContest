use vstd::prelude::*;

verus! {

pub fn generate_test_case(raw: Vec<i32>) -> (result: Vec<i32>)
    ensures
        3 <= result.len() <= 1000,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 100000,
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
{
    let end = if raw.len() > 1000 { 1000usize } else { raw.len() };
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0usize;
    while i < end
        invariant
            0 <= i <= end <= raw.len(), end <= 1000, result.len() <= i,
            forall|j: int| 0 <= j < result.len() ==> 1 <= #[trigger] result[j] <= 100000,
            forall|j: int, k: int| 0 <= j < k < result.len() ==> result[j] != result[k],
        decreases end - i,
    {
        let v = raw[i];
        let v = if v < 1 { 1 } else if v > 100000 { 100000 } else { v };
        let mut j = 0usize;
        let mut found = false;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                !found ==> forall|k: int| 0 <= k < j ==> #[trigger] result[k] != v,
            decreases result.len() - j,
        {
            if result[j] == v { found = true; }
            j += 1;
        }
        if !found { result.push(v); }
        i += 1;
    }
    if result.len() < 3 {
        let mut fallback: Vec<i32> = Vec::new();
        fallback.push(1);
        fallback.push(2);
        fallback.push(3);
        fallback
    } else {
        result
    }
}


pub fn generate_candidate(values: &Vec<i32>) -> (rating: Vec<i32>)
    requires
        3 <= values.len() <= 1000,
        forall|i: int| 0 <= i < values.len() ==> 1 <= #[trigger] values[i] <= 100000,
    ensures
        3 <= rating.len() <= 1000,
        forall|x: int| 0 <= x < rating.len() ==> 1 <= #[trigger] rating[x] <= 100000,
{
    let mut rating: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < values.len()
        invariant
            0 <= i <= values.len(),
            rating.len() == i,
            forall|k: int| 0 <= k < i as int ==> 1 <= #[trigger] rating[k] <= 100000,
            forall|k: int| 0 <= k < values.len() ==> 1 <= #[trigger] values[k] <= 100000,
            forall|k: int| 0 <= k < i as int ==> rating[k] == values[k],
        decreases values.len() - i,
    {
        rating.push(values[i]);
        i += 1;
    }
    rating
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
        self.state = self.state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        self.state
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = self.next_u64() % span;
        lo + v as i32
    }
}

fn unique_random(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    // generate n distinct values in [lo, hi]
    use std::collections::HashSet;
    let mut seen: HashSet<i32> = HashSet::new();
    let mut out: Vec<i32> = Vec::new();
    while out.len() < n {
        let v = rng.gen_range_i32(lo, hi);
        if !seen.contains(&v) {
            seen.insert(v);
            out.push(v);
        }
    }
    out
}

fn mode_sorted_asc(n: usize) -> Vec<i32> {
    (1..=n as i32).collect()
}

fn mode_sorted_desc(n: usize) -> Vec<i32> {
    (1..=n as i32).rev().collect()
}

fn mode_zigzag(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut lo = 1i32;
    let mut hi = n as i32;
    let mut toggle = true;
    while v.len() < n {
        if toggle {
            v.push(lo);
            lo += 1;
        } else {
            v.push(hi);
            hi -= 1;
        }
        toggle = !toggle;
    }
    v
}

fn mode_mountain(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mid = n / 2;
    for i in 0..=mid {
        v.push((i + 1) as i32);
    }
    let mut cur = mid as i32;
    while v.len() < n {
        v.push(cur);
        cur -= 1;
        if cur <= 0 { cur = 1; }
    }
    // ensure uniqueness by using a different scheme
    let mut out = Vec::with_capacity(n);
    // left: 1,2,...,mid+1; right: descending mid+2 range, but need unique
    out.clear();
    for i in 0..=mid {
        out.push((i + 1) as i32);
    }
    let mut next = (mid + 2) as i32;
    while out.len() < n {
        out.push(next);
        next += 1;
    }
    // This may not be a true mountain but all unique; reverse second half
    let half = (out.len() + 1) / 2;
    let right: Vec<i32> = out[half..].iter().rev().cloned().collect();
    let mut result: Vec<i32> = out[..half].to_vec();
    result.extend(right);
    result
}

fn mode_valley(n: usize) -> Vec<i32> {
    let mut m = mode_mountain(n);
    // flip: max - x + 1
    let mx = *m.iter().max().unwrap();
    for v in m.iter_mut() {
        *v = mx - *v + 1;
    }
    m
}

fn mode_random_small(rng: &mut Rng, n: usize) -> Vec<i32> {
    unique_random(rng, n, 1, (n as i32).max(10) * 2)
}

fn mode_random_large(rng: &mut Rng, n: usize) -> Vec<i32> {
    unique_random(rng, n, 1, 100000)
}

fn mode_min_size(rng: &mut Rng) -> Vec<i32> {
    unique_random(rng, 3, 1, 100000)
}

fn mode_max_size(rng: &mut Rng) -> Vec<i32> {
    unique_random(rng, 1000, 1, 100000)
}

fn mode_example1() -> Vec<i32> { vec![2,5,3,4,1] }
fn mode_example2() -> Vec<i32> { vec![2,1,3] }
fn mode_example3() -> Vec<i32> { vec![1,2,3,4] }

fn validate(v: &Vec<i32>) -> bool {
    if v.len() < 3 || v.len() > 1000 { return false; }
    for &x in v.iter() {
        if x < 1 || x > 100000 { return false; }
    }
    true
}

fn print_json(rating: &[i32]) {
        let rating = generate_test_case(rating.to_vec());
    print!("{{\"rating\":[");
    for i in 0..rating.len() {
        if i > 0 { print!(","); }
        print!("{}", rating[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };
    let mut rng = Rng::new(seed);

    let total = 200usize;
    for t in 0..total {
        let mode = t % 12;
        let n = match mode {
            0 => 3,
            1 => 1000,
            2 => rng.gen_range_usize(3, 20),
            3 => rng.gen_range_usize(50, 200),
            4 => rng.gen_range_usize(500, 1000),
            _ => rng.gen_range_usize(3, 100),
        };

        let values: Vec<i32> = match mode {
            0 => mode_example1(),
            1 => mode_sorted_asc(n),
            2 => mode_sorted_desc(n),
            3 => mode_zigzag(n),
            4 => mode_mountain(n),
            5 => mode_valley(n),
            6 => mode_random_small(&mut rng, n),
            7 => mode_random_large(&mut rng, n),
            8 => mode_min_size(&mut rng),
            9 => mode_max_size(&mut rng),
            10 => mode_example2(),
            11 => mode_example3(),
            _ => mode_random_large(&mut rng, n),
        };

        if !validate(&values) {
            continue;
        }
        let rating = generate_candidate(&values);
        print_json(&rating);
    }
}
