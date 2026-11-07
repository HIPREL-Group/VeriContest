use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    nums: Vec<i32>,
    k: i32,
    mutation_kind: u8,
) -> (result: (Vec<i32>, i32))
    requires
        1 <= nums.len() <= 50,
        1 <= k <= nums.len(),
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] < 2_147_483_648,
    ensures
        1 <= result.0.len() <= 50,
        1 <= result.1 <= result.0.len(),
        forall|i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] < 2_147_483_648,
{
    if mutation_kind == 0 {
        (nums, k)
    } else if mutation_kind == 1 {
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 0);
        (d, k)
    } else if mutation_kind == 2 {
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 2_147_483_647);
        (d, k)
    } else if mutation_kind == 3 {
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 0i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 0);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 4 {
        (nums, 1)
    } else if mutation_kind == 5 {
        let n = nums.len() as i32;
        (nums, n)
    } else if mutation_kind == 6 {
        let mut d = nums;
        if d[0] < 2_147_483_646 {
            d.set(0, d[0] + 1);
        }
        (d, k)
    } else if mutation_kind == 7 {
        let mut d = nums;
        if d[0] > 0 {
            d.set(0, d[0] - 1);
        }
        (d, k)
    } else if mutation_kind == 8 && nums.len() < 50 {
        let mut d = nums;
        d.push(0);
        (d, k)
    } else if mutation_kind == 9 && nums.len() > 1 && k < nums.len() as i32 {
        let mut d = nums;
        d.pop();
        (d, k)
    } else if mutation_kind == 10 {
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 50,
                forall|j: int| 0 <= j < i ==> d[j] == 2_147_483_647i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 2_147_483_647);
            i += 1;
        }
        (d, k)
    } else if mutation_kind == 11 && nums.len() >= 2 {
        let mut d = nums;
        let tmp = d[0];
        d.set(0, d[1]);
        d.set(1, tmp);
        (d, k)
    } else {
        (nums, k)
    }
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self {
            state: seed.wrapping_add(1),
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        assert!(lo <= hi);
        let range = (hi as i128 - lo as i128 + 1) as u128;
        (lo as i128 + (self.next_u64() as u128 % range) as i128) as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        lo + (self.next_u64() as usize) % (hi - lo + 1)
    }
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(0, 2_147_483_647) as i32);
    }
    nums
}

fn print_json(nums: &[i32], k: i32) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 {
            print!(",");
        }
        print!("{}", nums[i]);
    }
    println!("],\"k\":{}}}", k);
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(2917)
    } else {
        2917
    };
    let mut rng = Rng::new(seed);
    let total = 200usize;
    let examples: Vec<(Vec<i32>, i32)> = vec![
        (vec![7, 12, 9, 8, 9, 15], 4),
        (vec![2, 12, 1, 11, 4, 5], 6),
        (vec![10, 8, 5, 9, 11, 6, 8], 1),
    ];

    for t in 0..total {
        let (nums, k, mk) = if t < examples.len() {
            let (n, kk) = examples[t].clone();
            (n, kk, 0u8)
        } else {
            let nlen = match t % 5 {
                0 => rng.gen_range_usize(1, 3),
                1 => rng.gen_range_usize(1, 10),
                2 => rng.gen_range_usize(11, 30),
                3 => rng.gen_range_usize(31, 50),
                _ => rng.gen_range_usize(1, 50),
            };
            let nums = random_nums(&mut rng, nlen);
            let k = rng.gen_range_usize(1, nlen) as i32;
            let mk = (t % 12) as u8;
            (nums, k, mk)
        };
        let (rn, rk) = generate_test_case(nums, k, mk);
        print_json(&rn, rk);
    }
}
