use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len: usize,
    vals: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        2 <= len <= 100,
        vals.len() == len,
        forall |i: int| 0 <= i < vals.len() ==> 1 <= #[trigger] vals[i] <= 100,
        forall |i: int, j: int| 0 <= i < j < vals.len() ==> vals[i] != vals[j],
    ensures
        2 <= nums.len() <= 100,
        forall |i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 100,
        forall |i: int, j: int| 0 <= i < j < nums.len() ==> nums[i] != nums[j],
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            k <= len,
            len == vals.len(),
            nums.len() == k,
            forall |i: int| 0 <= i < nums.len() ==> nums[i] == vals[i],
        decreases len - k,
    {
        nums.push(vals[k]);
        k += 1;
    }
    assert(nums.len() == len);
    assert(forall |i: int| 0 <= i < nums.len() ==> nums[i] == vals[i]);
    nums
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
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn sample_unique(rng: &mut Rng, n: usize, lo: i32, hi: i32) -> Vec<i32> {
    // n must be <= (hi - lo + 1)
    let mut pool: Vec<i32> = (lo..=hi).collect();
    // Fisher-Yates partial shuffle
    let total = pool.len();
    let k = if n > total { total } else { n };
    for i in 0..k {
        let j = rng.gen_range_usize(i, total - 1);
        pool.swap(i, j);
    }
    pool.truncate(k);
    pool
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("]}}");
}

fn adversarial(rng: &mut Rng, mode: usize, t: usize) -> Vec<i32> {
    match mode {
        0 => {
            // minimum size, small range
            let n = 2;
            sample_unique(rng, n, 1, 100)
        }
        1 => {
            // maximum size: all 100 values used
            let n = 100;
            sample_unique(rng, n, 1, 100)
        }
        2 => {
            // size 2, containing 1 and 100
            vec![1, 100]
        }
        3 => {
            // size 2 with same small values like [5,1]
            let a = rng.gen_range_usize(1, 100) as i32;
            let mut b = rng.gen_range_usize(1, 100) as i32;
            while b == a {
                b = rng.gen_range_usize(1, 100) as i32;
            }
            vec![a, b]
        }
        4 => {
            // consecutive no missing
            let n = rng.gen_range_usize(2, 50);
            let start = rng.gen_range_usize(1, 100 - n + 1) as i32;
            let mut v: Vec<i32> = (start..start + n as i32).collect();
            // shuffle
            for i in 0..n {
                let j = rng.gen_range_usize(i, n - 1);
                v.swap(i, j);
            }
            v
        }
        5 => {
            // only endpoints kept
            let lo = rng.gen_range_usize(1, 50) as i32;
            let hi = rng.gen_range_usize((lo + 2) as usize, 100) as i32;
            vec![lo, hi]
        }
        6 => {
            // large range 1..100 pick many
            let n = rng.gen_range_usize(50, 100);
            sample_unique(rng, n, 1, 100)
        }
        7 => {
            // small contiguous slice
            let n = rng.gen_range_usize(2, 10);
            let start = rng.gen_range_usize(1, 100 - n + 1) as i32;
            let end = start + n as i32 - 1;
            let mut v = vec![start, end];
            // add some randoms in between
            let extras = rng.gen_range_usize(0, (end - start - 1).max(0) as usize);
            let mut used = vec![start, end];
            for _ in 0..extras {
                if end - start <= 1 { break; }
                let mut x = rng.gen_range_usize((start + 1) as usize, (end - 1) as usize) as i32;
                let mut attempts = 0;
                while used.contains(&x) && attempts < 20 {
                    x = rng.gen_range_usize((start + 1) as usize, (end - 1) as usize) as i32;
                    attempts += 1;
                }
                if !used.contains(&x) {
                    v.push(x);
                    used.push(x);
                }
            }
            v
        }
        8 => {
            // ordered ascending already
            let n = rng.gen_range_usize(2, 20);
            let mut v = sample_unique(rng, n, 1, 100);
            v.sort();
            v
        }
        9 => {
            // descending
            let n = rng.gen_range_usize(2, 20);
            let mut v = sample_unique(rng, n, 1, 100);
            v.sort();
            v.reverse();
            v
        }
        _ => {
            let n = rng.gen_range_usize(2, 100);
            sample_unique(rng, n, 1, 100)
        }
    }
    .into_iter()
    .take(100)
    .collect::<Vec<i32>>()
    .into_iter()
    .collect()
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
        let mut vals = adversarial(&mut rng, mode, t);

        // ensure 2 <= len <= 100 and all unique and all 1..=100
        if vals.len() < 2 {
            vals = vec![1, 2];
        }
        if vals.len() > 100 {
            vals.truncate(100);
        }
        // Dedup: build unique
        let mut seen = [false; 101];
        let mut cleaned: Vec<i32> = Vec::new();
        for &v in &vals {
            if v >= 1 && v <= 100 && !seen[v as usize] {
                seen[v as usize] = true;
                cleaned.push(v);
            }
        }
        while cleaned.len() < 2 {
            for cand in 1..=100i32 {
                if !seen[cand as usize] {
                    seen[cand as usize] = true;
                    cleaned.push(cand);
                    break;
                }
            }
        }

        let len = cleaned.len();
        let nums = generate_test_case(len, &cleaned);
        print_json(&nums);
    }
}