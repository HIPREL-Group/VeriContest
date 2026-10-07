use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    vals1: &Vec<i32>,
    vals2: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= vals1.len() <= 100000,
        1 <= vals2.len() <= 100000,
        forall |i: int| 0 <= i < vals1.len() ==> 0 <= #[trigger] vals1[i] <= 1000000,
        forall |i: int| 0 <= i < vals2.len() ==> 0 <= #[trigger] vals2[i] <= 1000000,
    ensures
        1 <= result.0.len() <= 100000,
        1 <= result.1.len() <= 100000,
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000000,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000000,
{
    let mut nums1: Vec<i32> = Vec::new();
    let mut nums2: Vec<i32> = Vec::new();

    let n1 = vals1.len();
    let mut i: usize = 0;
    while i < n1
        invariant
            n1 == vals1.len(),
            0 <= i <= n1,
            nums1.len() == i,
            forall |k: int| 0 <= k < i as int ==> #[trigger] nums1[k] == vals1[k],
            forall |k: int| 0 <= k < vals1.len() ==> 0 <= #[trigger] vals1[k] <= 1000000,
        decreases n1 - i,
    {
        nums1.push(vals1[i]);
        i = i + 1;
    }

    let n2 = vals2.len();
    let mut j: usize = 0;
    while j < n2
        invariant
            n2 == vals2.len(),
            0 <= j <= n2,
            nums2.len() == j,
            forall |k: int| 0 <= k < j as int ==> #[trigger] nums2[k] == vals2[k],
            forall |k: int| 0 <= k < vals2.len() ==> 0 <= #[trigger] vals2[k] <= 1000000,
        decreases n2 - j,
    {
        nums2.push(vals2[j]);
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

    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        let v = (self.next_u64() % span) as i64;
        (lo as i64 + v) as i32
    }
}

fn make_array(rng: &mut Rng, n: usize, max_val: i32, zero_prob: u32) -> Vec<i32> {
    let mut v = Vec::with_capacity(n);
    for _ in 0..n {
        let r = (rng.next_u64() % 100) as u32;
        if r < zero_prob {
            v.push(0);
        } else {
            v.push(rng.gen_range_i32(1, max_val));
        }
    }
    v
}

fn make_array_mode(rng: &mut Rng, mode: usize) -> Vec<i32> {
    match mode {
        0 => {
            // small random
            let n = rng.gen_range_usize(1, 10);
            make_array(rng, n, 100, 30)
        }
        1 => {
            // single element
            let n = 1;
            make_array(rng, n, 1000000, 50)
        }
        2 => {
            // all zeros
            let n = rng.gen_range_usize(1, 20);
            vec![0; n]
        }
        3 => {
            // no zeros
            let n = rng.gen_range_usize(1, 20);
            make_array(rng, n, 1000, 0)
        }
        4 => {
            // one zero, rest big
            let n = rng.gen_range_usize(2, 20);
            let mut v = Vec::with_capacity(n);
            let zi = rng.gen_range_usize(0, n - 1);
            for k in 0..n {
                if k == zi { v.push(0); } else { v.push(rng.gen_range_i32(1, 1000000)); }
            }
            v
        }
        5 => {
            // max values
            let n = rng.gen_range_usize(1, 50);
            let mut v = Vec::with_capacity(n);
            for _ in 0..n {
                if rng.next_u64() % 3 == 0 { v.push(0); } else { v.push(1000000); }
            }
            v
        }
        6 => {
            // large n
            let n = 100000;
            make_array(rng, n, 1000000, 20)
        }
        7 => {
            // all ones
            let n = rng.gen_range_usize(1, 30);
            vec![1; n]
        }
        8 => {
            // mix with high zero rate
            let n = rng.gen_range_usize(1, 100);
            make_array(rng, n, 1000000, 70)
        }
        9 => {
            // small sum scenarios
            let n = rng.gen_range_usize(1, 5);
            make_array(rng, n, 10, 40)
        }
        _ => {
            let n = rng.gen_range_usize(1, 200);
            make_array(rng, n, 1000000, 25)
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
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 11usize;
    let total = 200usize;

    for t in 0..total {
        let m1 = t % modes;
        let m2 = (t / modes + 3) % modes;
        let vals1 = make_array_mode(&mut rng, m1);
        let vals2 = make_array_mode(&mut rng, m2);
        let (n1, n2) = generate_test_case(&vals1, &vals2);
        print_json(&n1, &n2);
    }
}