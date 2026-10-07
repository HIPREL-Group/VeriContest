use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums1: Vec<i32>,
    nums2: Vec<i32>,
    mutation_kind: u8,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        1 <= nums1.len() <= 100_000,
        1 <= nums2.len() <= 100_000,
        forall|i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1_000_000_000,
        forall|j: int| 0 <= j < nums2.len() ==> 0 <= #[trigger] nums2[j] <= 1_000_000_000,
    ensures
        1 <= result.0.len() <= 100_000,
        1 <= result.1.len() <= 100_000,
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1_000_000_000,
        forall|j: int| 0 <= j < result.1.len() ==> 0 <= #[trigger] result.1[j] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        (nums1, nums2)
    } else if mutation_kind == 1 {
        let mut n1 = nums1;
        let last = n1.len() - 1;
        n1.set(last, 0);
        (n1, nums2)
    } else if mutation_kind == 2 {
        let mut n2 = nums2;
        let last = n2.len() - 1;
        n2.set(last, 0);
        (nums1, n2)
    } else if mutation_kind == 3 {
        let mut n1 = nums1;
        let ghost orig_len = n1.len();
        let mut i: usize = 0;
        while i < n1.len()
            invariant
                0 <= i <= n1.len(),
                n1.len() == orig_len,
                1 <= n1.len() <= 100_000,
                forall|k: int| 0 <= k < i ==> n1[k] == 0i32,
                forall|k: int| i <= k < n1.len() ==> n1[k] == nums1[k],
            decreases n1.len() - i,
        {
            n1.set(i, 0);
            i += 1;
        }
        (n1, nums2)
    } else if mutation_kind == 4 {
        let mut n2 = nums2;
        let ghost orig_len = n2.len();
        let mut j: usize = 0;
        while j < n2.len()
            invariant
                0 <= j <= n2.len(),
                n2.len() == orig_len,
                1 <= n2.len() <= 100_000,
                forall|k: int| 0 <= k < j ==> n2[k] == 0i32,
                forall|k: int| j <= k < n2.len() ==> n2[k] == nums2[k],
            decreases n2.len() - j,
        {
            n2.set(j, 0);
            j += 1;
        }
        (nums1, n2)
    } else if mutation_kind == 5 && nums1.len() < 100_000 {
        let mut n1 = nums1;
        n1.push(0);
        (n1, nums2)
    } else if mutation_kind == 6 && nums2.len() < 100_000 {
        let mut n2 = nums2;
        n2.push(0);
        (nums1, n2)
    } else if mutation_kind == 7 && nums1.len() > 1 {
        let mut n1 = nums1;
        n1.pop();
        (n1, nums2)
    } else if mutation_kind == 8 && nums2.len() > 1 {
        let mut n2 = nums2;
        n2.pop();
        (nums1, n2)
    } else if mutation_kind == 9 {
        let mut n1 = nums1;
        n1.set(0, 1_000_000_000);
        (n1, nums2)
    } else if mutation_kind == 10 {
        let mut n2 = nums2;
        n2.set(0, 1_000_000_000);
        (nums1, n2)
    } else if mutation_kind == 11 {
        let mut n1 = nums1;
        let last = n1.len() - 1;
        if n1[last] < 1_000_000_000 {
            n1.set(last, n1[last] + 1);
        }
        (n1, nums2)
    } else if mutation_kind == 12 {
        let mut n2 = nums2;
        let last = n2.len() - 1;
        if n2[last] > 0 {
            n2.set(last, n2[last] - 1);
        }
        (nums1, n2)
    } else {
        (nums1, nums2)
    }
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
    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }
}

fn random_array(rng: &mut Rng, len: usize, lo: i64, hi: i64) -> Vec<i32> {
    let mut arr = Vec::with_capacity(len);
    for _ in 0..len {
        arr.push(rng.gen_range_i64(lo, hi) as i32);
    }
    arr
}

fn print_json(nums1: &[i32], nums2: &[i32]) {
    print!("{{\"nums1\":[");
    for i in 0..nums1.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums1[i]);
    }
    print!("],\"nums2\":[");
    for i in 0..nums2.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums2[i]);
    }
    println!("]}}");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };
    let mut rng = Rng::new(seed);
    let modes = 13usize;
    let total = 200usize;

    let seed_pairs: Vec<(Vec<i32>, Vec<i32>)> = vec![
        (vec![2, 1, 3], vec![10, 2, 5, 0]),
        (vec![1, 2], vec![3, 4]),
        (vec![0], vec![0]),
        (vec![1_000_000_000], vec![1_000_000_000]),
        (vec![0, 0, 0], vec![0, 0, 0]),
        (vec![1], vec![1]),
        (vec![999_999_999], vec![1]),
        (vec![123, 456, 789], vec![321, 654]),
    ];

    for t in 0..total {
        let mode = t % modes;
        let mk = (t % 14) as u8;
        let (n1, n2) = if t < seed_pairs.len() {
            seed_pairs[t].clone()
        } else {
            let len1 = match mode {
                0 => rng.gen_range_usize(1, 3),
                1 => rng.gen_range_usize(1, 10),
                2 => rng.gen_range_usize(11, 100),
                3 => rng.gen_range_usize(101, 1000),
                _ => rng.gen_range_usize(1001, 5000),
            };
            let len2 = match (t / 3) % 5 {
                0 => rng.gen_range_usize(1, 3),
                1 => rng.gen_range_usize(1, 10),
                2 => rng.gen_range_usize(11, 100),
                3 => rng.gen_range_usize(101, 1000),
                _ => rng.gen_range_usize(1001, 5000),
            };
            let (lo, hi) = if mode % 2 == 0 {
                (0i64, 1_000_000_000i64)
            } else {
                (0i64, 1i64)
            };
            let a = random_array(&mut rng, len1, lo, hi);
            let b = random_array(&mut rng, len2, lo, hi);
            (a, b)
        };
        let (o1, o2) = generate_test_case(n1, n2, mk);
        print_json(&o1, &o2);
    }
}
