use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    distinct_vals: &Vec<i32>,
    k_val: i32,
) -> (result: (Vec<i32>, i32))
    requires
        2 <= distinct_vals.len() <= 100_000,
        forall |i: int| 0 <= i < distinct_vals.len() ==> 1 <= #[trigger] distinct_vals[i] <= 1_000_000,
        forall |i: int, j: int| 0 <= i < j < distinct_vals.len() ==> distinct_vals[i] != distinct_vals[j],
        1 <= k_val <= 1_000_000_000,
    ensures
        2 <= result.0.len() <= 100_000,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 1_000_000,
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        1 <= result.1 <= 1_000_000_000,
        result.1 == k_val,
{
    let mut arr: Vec<i32> = Vec::new();
    let n = distinct_vals.len();
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            n == distinct_vals.len(),
            arr.len() == i,
            forall |j: int| 0 <= j < i as int ==> #[trigger] arr[j] == distinct_vals[j],
        decreases n - i,
    {
        arr.push(distinct_vals[i]);
        i += 1;
    }

    proof {
        assert forall |a: int| 0 <= a < arr.len() implies 1 <= #[trigger] arr[a] <= 1_000_000 by {
            assert(arr[a] == distinct_vals[a]);
        }
        assert forall |a: int, b: int| 0 <= a < b < arr.len() implies arr[a] != arr[b] by {
            assert(arr[a] == distinct_vals[a]);
            assert(arr[b] == distinct_vals[b]);
        }
    }

    (arr, k_val)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed.wrapping_add(0x9E3779B97F4A7C15) }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn shuffle(rng: &mut Rng, v: &mut Vec<i32>) {
    let n = v.len();
    if n < 2 { return; }
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
}

fn gen_distinct(rng: &mut Rng, n: usize, max_val: i32) -> Vec<i32> {
    // n distinct values in [1, max_val]
    assert!(n as i64 <= max_val as i64);
    // Use a simple strategy: sample from 1..=max_val
    if (n as i64) * 2 > max_val as i64 {
        // dense: take 1..=max_val, shuffle, take first n
        let mut all: Vec<i32> = (1..=max_val).collect();
        shuffle(rng, &mut all);
        all.truncate(n);
        all
    } else {
        // sparse: rejection
        use std::collections::HashSet;
        let mut set: HashSet<i32> = HashSet::new();
        let mut res: Vec<i32> = Vec::with_capacity(n);
        while res.len() < n {
            let v = rng.gen_range_i32(1, max_val);
            if set.insert(v) {
                res.push(v);
            }
        }
        res
    }
}

fn print_json(arr: &[i32], k: i32) {
    print!("{{\"arr\":[");
    for i in 0..arr.len() {
        if i > 0 { print!(","); }
        print!("{}", arr[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn build_mode(rng: &mut Rng, mode: usize, t: usize) -> (Vec<i32>, i32) {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(2, 10);
            let arr = gen_distinct(rng, n, 1_000_000);
            let k = rng.gen_range_i32(1, 5);
            (arr, k)
        }
        1 => {
            // sorted ascending, k=1 -> winner is last; k large -> winner is max
            let n = rng.gen_range_usize(5, 200);
            let mut arr: Vec<i32> = (1..=(n as i32)).collect();
            // optionally offset
            let off = rng.gen_range_i32(0, 500);
            for x in arr.iter_mut() { *x += off; }
            let k = if t % 2 == 0 { 1 } else { 1_000_000_000 };
            (arr, k)
        }
        2 => {
            // sorted descending
            let n = rng.gen_range_usize(5, 200);
            let mut arr: Vec<i32> = (1..=(n as i32)).rev().collect();
            let k = rng.gen_range_i32(1, n as i32);
            (arr, k)
        }
        3 => {
            // max at the front - trivially wins
            let n = rng.gen_range_usize(2, 500);
            let mut arr = gen_distinct(rng, n, 1_000_000);
            // find max index, swap to front
            let mut mi = 0;
            for i in 1..n { if arr[i] > arr[mi] { mi = i; } }
            arr.swap(0, mi);
            let k = rng.gen_range_i32(1, 1_000_000_000);
            (arr, k)
        }
        4 => {
            // k = 1
            let n = rng.gen_range_usize(2, 1000);
            let arr = gen_distinct(rng, n, 1_000_000);
            (arr, 1)
        }
        5 => {
            // k very large
            let n = rng.gen_range_usize(2, 1000);
            let arr = gen_distinct(rng, n, 1_000_000);
            (arr, 1_000_000_000)
        }
        6 => {
            // minimum case: n=2
            let a = rng.gen_range_i32(1, 1_000_000);
            let mut b = rng.gen_range_i32(1, 1_000_000);
            while b == a { b = rng.gen_range_i32(1, 1_000_000); }
            let k = rng.gen_range_i32(1, 1_000_000_000);
            (vec![a, b], k)
        }
        7 => {
            // large n, random
            let n = 100_000;
            let arr = gen_distinct(rng, n, 1_000_000);
            let k = rng.gen_range_i32(1, 1_000_000_000);
            (arr, k)
        }
        8 => {
            // large n, sorted ascending
            let n = 100_000;
            let mut arr: Vec<i32> = (1..=(n as i32)).collect();
            shuffle(rng, &mut vec![]); // no-op
            // keep sorted
            let _ = arr.len();
            let k = if t % 2 == 0 { 2 } else { n as i32 - 1 };
            (arr, k)
        }
        9 => {
            // k = n-1, interesting boundary
            let n = rng.gen_range_usize(3, 100);
            let arr = gen_distinct(rng, n, 1_000_000);
            (arr, (n as i32) - 1)
        }
        _ => {
            let n = rng.gen_range_usize(2, 500);
            let arr = gen_distinct(rng, n, 1_000_000);
            let k = rng.gen_range_i32(1, 1_000_000_000);
            (arr, k)
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
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;
        let (arr, k) = build_mode(&mut rng, mode, t);
        // sanity-check constraints before calling
        if arr.len() < 2 || arr.len() > 100_000 { continue; }
        if k < 1 || k > 1_000_000_000 { continue; }
        let mut ok = true;
        for &v in &arr {
            if v < 1 || v > 1_000_000 { ok = false; break; }
        }
        if !ok { continue; }
        // distinctness check
        {
            let mut sorted = arr.clone();
            sorted.sort();
            for i in 1..sorted.len() {
                if sorted[i] == sorted[i-1] { ok = false; break; }
            }
        }
        if !ok { continue; }

        let (a, kk) = generate_test_case(&arr, k);
        print_json(&a, kk);
    }
}