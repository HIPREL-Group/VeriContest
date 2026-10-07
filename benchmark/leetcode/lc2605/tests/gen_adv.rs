use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    len1: usize,
    len2: usize,
    perm1: &Vec<i32>,
    perm2: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= len1 <= 9,
        1 <= len2 <= 9,
        perm1.len() == len1,
        perm2.len() == len2,
        forall |i: int| 0 <= i < perm1.len() ==> 1 <= #[trigger] perm1[i] <= 9,
        forall |i: int| 0 <= i < perm2.len() ==> 1 <= #[trigger] perm2[i] <= 9,
        forall |i: int, j: int| 0 <= i < j < perm1.len() ==> perm1[i] != perm1[j],
        forall |i: int, j: int| 0 <= i < j < perm2.len() ==> perm2[i] != perm2[j],
    ensures
        1 <= result.0.len() <= 9,
        1 <= result.1.len() <= 9,
        forall |i: int| 0 <= i < result.0.len() ==> 1 <= #[trigger] result.0[i] <= 9,
        forall |i: int| 0 <= i < result.1.len() ==> 1 <= #[trigger] result.1[i] <= 9,
        forall |i: int, j: int| 0 <= i < j < result.0.len() ==> result.0[i] != result.0[j],
        forall |i: int, j: int| 0 <= i < j < result.1.len() ==> result.1[i] != result.1[j],
{
    let mut nums1: Vec<i32> = Vec::new();
    let mut nums2: Vec<i32> = Vec::new();

    let mut i: usize = 0;
    while i < len1
        invariant
            0 <= i <= len1,
            nums1.len() == i,
            perm1.len() == len1,
            forall |k: int| 0 <= k < i as int ==> nums1[k] == perm1[k],
            forall |k: int| 0 <= k < perm1.len() ==> 1 <= #[trigger] perm1[k] <= 9,
            forall |k1: int, k2: int| 0 <= k1 < k2 < perm1.len() ==> perm1[k1] != perm1[k2],
        decreases len1 - i,
    {
        nums1.push(perm1[i]);
        i = i + 1;
    }

    let mut j: usize = 0;
    while j < len2
        invariant
            0 <= j <= len2,
            nums2.len() == j,
            perm2.len() == len2,
            forall |k: int| 0 <= k < j as int ==> nums2[k] == perm2[k],
            forall |k: int| 0 <= k < perm2.len() ==> 1 <= #[trigger] perm2[k] <= 9,
            forall |k1: int, k2: int| 0 <= k1 < k2 < perm2.len() ==> perm2[k1] != perm2[k2],
        decreases len2 - j,
    {
        nums2.push(perm2[j]);
        j = j + 1;
    }

    (nums1, nums2)
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
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn make_unique_digits(rng: &mut Rng, len: usize) -> Vec<i32> {
    // digits 1..=9, shuffle, take `len`
    let mut pool: Vec<i32> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
    // Fisher-Yates
    for i in (1..pool.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        pool.swap(i, j);
    }
    pool.truncate(len);
    pool
}

fn make_from_set(digits: &[i32], rng: &mut Rng) -> Vec<i32> {
    let mut v: Vec<i32> = digits.to_vec();
    for i in (1..v.len()).rev() {
        let j = rng.gen_range_usize(0, i);
        v.swap(i, j);
    }
    v
}

fn gen_mode(mode: usize, t: usize, rng: &mut Rng) -> (Vec<i32>, Vec<i32>) {
    match mode {
        0 => {
            // fully random unique digits
            let l1 = rng.gen_range_usize(1, 9);
            let l2 = rng.gen_range_usize(1, 9);
            (make_unique_digits(rng, l1), make_unique_digits(rng, l2))
        }
        1 => {
            // no common digit: split 1..9 into two disjoint subsets
            let mut pool: Vec<i32> = vec![1, 2, 3, 4, 5, 6, 7, 8, 9];
            for i in (1..pool.len()).rev() {
                let j = rng.gen_range_usize(0, i);
                pool.swap(i, j);
            }
            let split = rng.gen_range_usize(1, 8);
            let a: Vec<i32> = pool[..split].to_vec();
            let b: Vec<i32> = pool[split..].to_vec();
            (a, b)
        }
        2 => {
            // exactly one common digit
            let common = rng.gen_range_usize(1, 9) as i32;
            let mut a: Vec<i32> = vec![common];
            let mut b: Vec<i32> = vec![common];
            let rest: Vec<i32> = (1..=9).filter(|&x| x != common).collect();
            let mut rshuf = rest.clone();
            for i in (1..rshuf.len()).rev() {
                let j = rng.gen_range_usize(0, i);
                rshuf.swap(i, j);
            }
            let take_a = rng.gen_range_usize(0, 4);
            let take_b = rng.gen_range_usize(0, 4);
            for k in 0..take_a {
                a.push(rshuf[k]);
            }
            for k in take_a..(take_a + take_b).min(rshuf.len()) {
                b.push(rshuf[k]);
            }
            (a, b)
        }
        3 => {
            // both singletons
            let x = rng.gen_range_usize(1, 9) as i32;
            let y = rng.gen_range_usize(1, 9) as i32;
            (vec![x], vec![y])
        }
        4 => {
            // smallest common = 1
            let mut a = vec![1i32];
            let mut b = vec![1i32];
            let rest: Vec<i32> = (2..=9).collect();
            let mut rs = rest.clone();
            for i in (1..rs.len()).rev() {
                let j = rng.gen_range_usize(0, i);
                rs.swap(i, j);
            }
            let ta = rng.gen_range_usize(0, 4);
            let tb = rng.gen_range_usize(0, 4);
            for k in 0..ta { a.push(rs[k]); }
            for k in ta..(ta+tb).min(rs.len()) { b.push(rs[k]); }
            (make_from_set(&a, rng), make_from_set(&b, rng))
        }
        5 => {
            // max length both
            (make_unique_digits(rng, 9), make_unique_digits(rng, 9))
        }
        6 => {
            // first has large digits, second has small digits (force two-digit answer)
            let a: Vec<i32> = vec![7, 8, 9];
            let b: Vec<i32> = vec![2, 3, 4];
            (make_from_set(&a, rng), make_from_set(&b, rng))
        }
        7 => {
            // disjoint with min digits at specific positions
            let a: Vec<i32> = vec![5, 1, 3];
            let b: Vec<i32> = vec![7, 2, 6];
            (make_from_set(&a, rng), make_from_set(&b, rng))
        }
        8 => {
            // same digit in both, at end of a
            let a: Vec<i32> = vec![9, 8, 5];
            let b: Vec<i32> = vec![5, 7];
            (make_from_set(&a, rng), make_from_set(&b, rng))
        }
        9 => {
            // adversarial: common exists but isn't smallest overall
            let a: Vec<i32> = vec![3, 5, 2, 6];
            let b: Vec<i32> = vec![3, 1, 7];
            (make_from_set(&a, rng), make_from_set(&b, rng))
        }
        _ => {
            let l1 = ((t % 9) + 1) as usize;
            let l2 = (((t * 7 + 3) % 9) + 1) as usize;
            (make_unique_digits(rng, l1), make_unique_digits(rng, l2))
        }
    }
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 { print!(","); }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 { print!(","); }
        print!("{}", nums2[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else { 1 };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 220usize;

    for t in 0..total {
        let mode = t % modes;
        let (v1, v2) = gen_mode(mode, t, &mut rng);
        let len1 = v1.len();
        let len2 = v2.len();
        if len1 < 1 || len1 > 9 || len2 < 1 || len2 > 9 {
            continue;
        }
        // sanity: uniqueness and range
        let mut ok = true;
        for &x in &v1 { if x < 1 || x > 9 { ok = false; } }
        for &x in &v2 { if x < 1 || x > 9 { ok = false; } }
        for i in 0..v1.len() {
            for j in (i+1)..v1.len() {
                if v1[i] == v1[j] { ok = false; }
            }
        }
        for i in 0..v2.len() {
            for j in (i+1)..v2.len() {
                if v2[i] == v2[j] { ok = false; }
            }
        }
        if !ok { continue; }

        let (nums1, nums2) = generate_test_case(len1, len2, &v1, &v2);
        print_json(&nums1, &nums2);
    }
}