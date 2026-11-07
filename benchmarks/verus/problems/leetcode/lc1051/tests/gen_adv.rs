use vstd::prelude::*;

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn valid_heights(s: Seq<i32>) -> bool {
        1 <= s.len() <= 100
            && forall |i: int| 0 <= i < s.len() ==> 1 <= #[trigger] s[i] <= 100
    }
}

pub fn generate_test_case(prefix: &Vec<i32>, pivot: i32, suffix: &Vec<i32>) -> (heights: Vec<i32>)
    requires
        0 <= prefix.len() <= 99,
        0 <= suffix.len() <= 99,
        prefix.len() + suffix.len() + 1 <= 100,
        forall |i: int| 0 <= i < prefix.len() ==> 1 <= #[trigger] prefix[i] <= 100,
        1 <= pivot <= 100,
        forall |i: int| 0 <= i < suffix.len() ==> 1 <= #[trigger] suffix[i] <= 100,
    ensures
        1 <= heights.len() <= 100,
        forall |i: int| 0 <= i < heights.len() ==> 1 <= #[trigger] heights[i] <= 100,
{
    let total_len: usize = prefix.len() + suffix.len() + 1;
    let mut heights: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < prefix.len()
        invariant
            0 <= i <= prefix.len(),
            heights.len() == i,
            total_len == prefix.len() + suffix.len() + 1,
            total_len <= 100,
            forall |k: int| 0 <= k < i ==> #[trigger] heights[k] == prefix[k],
            forall |k: int| 0 <= k < heights.len() ==> 1 <= #[trigger] heights[k] <= 100,
            forall |k: int| 0 <= k < prefix.len() ==> 1 <= #[trigger] prefix[k] <= 100,
            1 <= pivot <= 100,
            forall |k: int| 0 <= k < suffix.len() ==> 1 <= #[trigger] suffix[k] <= 100,
        decreases prefix.len() - i,
    {
        heights.push(prefix[i]);
        i = i + 1;
    }

    heights.push(pivot);

    let mut j: usize = 0;
    while j < suffix.len()
        invariant
            0 <= j <= suffix.len(),
            heights.len() == prefix.len() + 1 + j,
            total_len == prefix.len() + suffix.len() + 1,
            total_len <= 100,
            forall |k: int| 0 <= k < prefix.len() ==> #[trigger] heights[k] == prefix[k],
            heights[prefix.len() as int] == pivot,
            forall |k: int| 0 <= k < j ==> #[trigger] heights[prefix.len() as int + 1 + k] == suffix[k],
            forall |k: int| 0 <= k < heights.len() ==> 1 <= #[trigger] heights[k] <= 100,
            forall |k: int| 0 <= k < prefix.len() ==> 1 <= #[trigger] prefix[k] <= 100,
            1 <= pivot <= 100,
            forall |k: int| 0 <= k < suffix.len() ==> 1 <= #[trigger] suffix[k] <= 100,
        decreases suffix.len() - j,
    {
        heights.push(suffix[j]);
        j = j + 1;
    }

    assert(heights.len() == total_len);
    assert(1 <= heights.len());
    assert(heights.len() <= 100);
    heights
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self {
        Self(seed)
    }

    fn next_u64(&mut self) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        assert!(lo <= hi);
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn sorted_non_decreasing(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut cur = 1i32;
    let mut i = 0usize;
    while i < n {
        v.push(cur);
        if (i + 1) % 3 == 0 && cur < 100 {
            cur += 1;
        }
        i += 1;
    }
    v
}

fn reversed_sorted(n: usize) -> Vec<i32> {
    let mut v = sorted_non_decreasing(n);
    v.reverse();
    v
}

fn alternating_extremes(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        if i % 2 == 0 {
            v.push(1);
        } else {
            v.push(100);
        }
        i += 1;
    }
    v
}

fn all_same(n: usize, x: i32) -> Vec<i32> {
    vec![x; n]
}

fn one_out_of_place(n: usize) -> Vec<i32> {
    let mut v = sorted_non_decreasing(n);
    if n >= 2 {
        v.swap(0, n - 1);
    }
    v
}

fn random_heights(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        v.push(rng.gen_range_i32(1, 100));
        i += 1;
    }
    v
}

fn almost_sorted(rng: &mut Rng, n: usize) -> Vec<i32> {
    let mut v = sorted_non_decreasing(n);
    if n >= 2 {
        let a = rng.gen_range_usize(0, n - 1);
        let b = rng.gen_range_usize(0, n - 1);
        v.swap(a, b);
    }
    v
}

fn sawtooth(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        v.push(((i % 10) as i32) + 1);
        i += 1;
    }
    v
}

fn plateau_blocks(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut i = 0usize;
    while i < n {
        let block = (i / 5) as i32;
        let val = 1 + (block % 20);
        v.push(val);
        i += 1;
    }
    v
}

fn zigzag_mid(n: usize) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    let mut low = 40i32;
    let mut high = 60i32;
    let mut i = 0usize;
    while i < n {
        if i % 2 == 0 {
            v.push(low);
            if low < 100 {
                low += 1;
            }
        } else {
            v.push(high);
            if high > 1 {
                high -= 1;
            }
        }
        i += 1;
    }
    v
}

fn build_mode_case(rng: &mut Rng, mode: usize, n: usize) -> Vec<i32> {
    match mode {
        0 => sorted_non_decreasing(n),
        1 => reversed_sorted(n),
        2 => alternating_extremes(n),
        3 => all_same(n, 1),
        4 => all_same(n, 100),
        5 => one_out_of_place(n),
        6 => almost_sorted(rng, n),
        7 => sawtooth(n),
        8 => plateau_blocks(n),
        9 => zigzag_mid(n),
        _ => random_heights(rng, n),
    }
}

fn print_json_line(v: &Vec<i32>) {
    use std::io::Write;
    let stdout = std::io::stdout();
    let mut out = std::io::BufWriter::new(stdout.lock());
    write!(out, "{{\"heights\":[").unwrap();
    let mut i = 0usize;
    while i < v.len() {
        if i > 0 {
            write!(out, ",").unwrap();
        }
        write!(out, "{}", v[i]).unwrap();
        i += 1;
    }
    writeln!(out, "]}}").unwrap();
}

fn emit_case(data: Vec<i32>) {
    let split = if data.is_empty() { 0 } else { data.len() / 2 };
    let prefix = data[..split].to_vec();
    let pivot = data[split];
    let suffix = data[split + 1..].to_vec();
    let heights = generate_test_case(&prefix, pivot, &suffix);
    print_json_line(&heights);
}

fn main() {
    let seed = std::env::args()
        .nth(1)
        .and_then(|s| s.parse::<u64>().ok())
        .unwrap_or(1);

    let mut rng = Rng::new(seed);

    let fixed_ns = [1usize, 2, 3, 4, 5, 10, 25, 50, 99, 100];
    let mut mode = 0usize;
    while mode < 10 {
        let mut idx = 0usize;
        while idx < fixed_ns.len() {
            emit_case(build_mode_case(&mut rng, mode, fixed_ns[idx]));
            idx += 1;
        }
        mode += 1;
    }

    let mut extra = 0usize;
    while extra < 100 {
        let n = rng.gen_range_usize(1, 100);
        let mode = rng.gen_range_usize(0, 10);
        emit_case(build_mode_case(&mut rng, mode, n));
        extra += 1;
    }
}