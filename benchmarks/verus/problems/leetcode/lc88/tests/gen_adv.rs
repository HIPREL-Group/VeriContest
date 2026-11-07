use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    sorted1: &Vec<i32>,
    sorted2: &Vec<i32>,
    m: i32,
    n: i32,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        0 <= m,
        0 <= n,
        1 <= m + n <= 200,
        sorted1.len() == m as int,
        sorted2.len() == n as int,
        forall |i: int| 0 <= i < sorted1.len() ==>
            -1_000_000_000 <= #[trigger] sorted1[i] <= 1_000_000_000,
        forall |i: int| 0 <= i < sorted2.len() ==>
            -1_000_000_000 <= #[trigger] sorted2[i] <= 1_000_000_000,
        forall |i: int, j: int| 0 <= i <= j < sorted1.len() ==>
            sorted1[i] <= sorted1[j],
        forall |i: int, j: int| 0 <= i <= j < sorted2.len() ==>
            sorted2[i] <= sorted2[j],
    ensures
        ({
            let (nums1, nums2) = result;
            &&& nums1.len() == (m + n) as int
            &&& nums2.len() == n as int
            &&& (forall |i: int| 0 <= i < m as int ==>
                    -1_000_000_000 <= #[trigger] nums1[i] <= 1_000_000_000)
            &&& (forall |i: int| 0 <= i < n as int ==>
                    -1_000_000_000 <= #[trigger] nums2[i] <= 1_000_000_000)
            &&& (forall |i: int, j: int| 0 <= i <= j < m as int ==>
                    nums1[i] <= nums1[j])
            &&& (forall |i: int, j: int| 0 <= i <= j < n as int ==>
                    nums2[i] <= nums2[j])
        }),
{
    let mut nums1: Vec<i32> = Vec::new();
    let m_usize: usize = m as usize;
    let n_usize: usize = n as usize;

    let mut k: usize = 0;
    while k < m_usize
        invariant
            0 <= k <= m_usize,
            m_usize == m as int,
            sorted1.len() == m as int,
            nums1.len() == k as int,
            forall |i: int| 0 <= i < k as int ==> #[trigger] nums1[i] == sorted1[i],
        decreases m_usize - k,
    {
        nums1.push(sorted1[k]);
        k = k + 1;
    }

    let mut k2: usize = 0;
    while k2 < n_usize
        invariant
            0 <= k2 <= n_usize,
            m_usize == m as int,
            n_usize == n as int,
            sorted1.len() == m as int,
            nums1.len() == (m as int) + (k2 as int),
            forall |i: int| 0 <= i < m as int ==> #[trigger] nums1[i] == sorted1[i],
        decreases n_usize - k2,
    {
        nums1.push(0);
        k2 = k2 + 1;
    }

    let mut nums2: Vec<i32> = Vec::new();
    let mut k3: usize = 0;
    while k3 < n_usize
        invariant
            0 <= k3 <= n_usize,
            n_usize == n as int,
            sorted2.len() == n as int,
            nums2.len() == k3 as int,
            forall |i: int| 0 <= i < k3 as int ==> #[trigger] nums2[i] == sorted2[i],
        decreases n_usize - k3,
    {
        nums2.push(sorted2[k3]);
        k3 = k3 + 1;
    }

    proof {
        assert(nums1.len() == (m + n) as int);
        assert(nums2.len() == n as int);
        assert forall |i: int| 0 <= i < m as int implies
            -1_000_000_000 <= #[trigger] nums1[i] <= 1_000_000_000
        by {
            assert(nums1[i] == sorted1[i]);
        }
        assert forall |i: int, j: int| 0 <= i <= j < m as int implies
            nums1[i] <= nums1[j]
        by {
            assert(nums1[i] == sorted1[i]);
            assert(nums1[j] == sorted1[j]);
        }
    }

    (nums1, nums2)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
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

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn make_sorted(rng: &mut Rng, len: usize, mode: usize) -> Vec<i32> {
    let mut v: Vec<i32> = Vec::with_capacity(len);
    if len == 0 {
        return v;
    }
    match mode {
        0 => {
            // random then sort
            for _ in 0..len {
                v.push(rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32);
            }
            v.sort();
        }
        1 => {
            // all same
            let x = rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32;
            for _ in 0..len {
                v.push(x);
            }
        }
        2 => {
            // all min
            for _ in 0..len {
                v.push(-1_000_000_000);
            }
        }
        3 => {
            // all max
            for _ in 0..len {
                v.push(1_000_000_000);
            }
        }
        4 => {
            // increasing from -1e9
            let mut x: i64 = -1_000_000_000;
            for _ in 0..len {
                v.push(x as i32);
                x += 1;
            }
        }
        5 => {
            // decreasing - just use fixed
            let mut x: i64 = 1_000_000_000;
            for _ in 0..len {
                v.push(x as i32);
                x -= 1;
            }
            v.sort();
        }
        6 => {
            // tight cluster around 0
            for _ in 0..len {
                v.push(rng.gen_range_i64(-5, 5) as i32);
            }
            v.sort();
        }
        7 => {
            // all zeros
            for _ in 0..len {
                v.push(0);
            }
        }
        8 => {
            // half min, half max
            let half = len / 2;
            for _ in 0..half {
                v.push(-1_000_000_000);
            }
            for _ in half..len {
                v.push(1_000_000_000);
            }
        }
        9 => {
            // small negatives
            for _ in 0..len {
                v.push(rng.gen_range_i64(-1_000_000_000, -999_999_000) as i32);
            }
            v.sort();
        }
        _ => {
            for _ in 0..len {
                v.push(rng.gen_range_i64(-100, 100) as i32);
            }
            v.sort();
        }
    }
    v
}

fn print_json(nums1: &[i32], m: i32, nums2: &[i32], n: i32) {
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 { print!(","); }
        print!("{}", nums1[i]);
    }
    print!("],\"m\":{},\"nums2\":[", m);
    for i in 0..nums2.len() {
        if i > 0 { print!(","); }
        print!("{}", nums2[i]);
    }
    println!("],\"n\":{}}}", n);
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

    // adversarial fixed scenarios
    let fixed: Vec<(usize, usize)> = vec![
        (1, 0),
        (0, 1),
        (1, 1),
        (200, 0),
        (0, 200),
        (100, 100),
        (199, 1),
        (1, 199),
        (2, 2),
        (50, 150),
    ];

    let mut out_count = 0;
    for (m_u, n_u) in fixed.iter() {
        let m = *m_u as i32;
        let n = *n_u as i32;
        let mode = out_count % modes;
        let s1 = make_sorted(&mut rng, *m_u, mode);
        let s2 = make_sorted(&mut rng, *n_u, (mode + 1) % modes);
        let (nums1, nums2) = generate_test_case(&s1, &s2, m, n);
        print_json(&nums1, m, &nums2, n);
        out_count += 1;
    }

    while out_count < total {
        let t = out_count;
        let mode = t % modes;
        // total size 1..=200
        let total_size = rng.gen_range_usize(1, 200);
        let m_u = rng.gen_range_usize(0, total_size);
        let n_u = total_size - m_u;
        let m = m_u as i32;
        let n = n_u as i32;

        let s1 = make_sorted(&mut rng, m_u, mode);
        let s2 = make_sorted(&mut rng, n_u, (mode + 3) % modes);
        let (nums1, nums2) = generate_test_case(&s1, &s2, m, n);
        print_json(&nums1, m, &nums2, n);
        out_count += 1;
    }
}