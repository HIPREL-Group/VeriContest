use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100_000,
        forall|i: int| 0 <= i < result.len() ==> -1_000_000_000 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        // identity
        nums
    } else if mutation_kind == 1 && nums.len() > 1 {
        // nudge first element up
        let mut d = nums;
        if d[0] < 1_000_000_000 {
            d.set(0, d[0] + 1);
        }
        d
    } else if mutation_kind == 2 && nums.len() > 1 {
        // nudge last element down
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > -1_000_000_000 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 3 {
        // set first element to 0
        let mut d = nums;
        d.set(0, 0);
        d
    } else if mutation_kind == 4 {
        // set first element to max boundary
        let mut d = nums;
        d.set(0, 1_000_000_000);
        d
    } else if mutation_kind == 5 {
        // set first element to min boundary
        let mut d = nums;
        d.set(0, -1_000_000_000);
        d
    } else if mutation_kind == 6 && nums.len() < 100_000 {
        // grow: push a 0
        let mut d = nums;
        d.push(0);
        d
    } else if mutation_kind == 7 && nums.len() > 1 {
        // shrink: pop last element
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 8 {
        // set all elements to the same value (first element)
        let val = nums[0];
        let len = nums.len();
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == len,
                1 <= d.len() <= 100_000,
                -1_000_000_000 <= val <= 1_000_000_000,
                forall|j: int| 0 <= j < i ==> d[j] == val,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, val);
            i += 1;
        }
        d
    } else if mutation_kind == 9 && nums.len() >= 2 {
        // swap first and last elements
        let mut d = nums;
        let last = d.len() - 1;
        let tmp = d[0];
        d.set(0, d[last]);
        d.set(last, tmp);
        d
    } else if mutation_kind == 10 {
        // negate first element
        let mut d = nums;
        if d[0] > -1_000_000_000 {
            d.set(0, -d[0]);
        }
        d
    } else {
        // fallback: identity
        nums
    }
}

} // verus!

struct Rng(u64);

impl Rng {
    fn new(seed: u64) -> Self { Self(seed) }

    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.0
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

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
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

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32);
    }
    nums
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed: u64 = args.get(1).and_then(|s| s.parse().ok()).unwrap_or(42);
    let mut rng = Rng::new(seed);

    let examples: Vec<Vec<i32>> = vec![
        vec![5, 3, 2, 4],
        vec![1, 5, 0, 10, 14],
        vec![3, 100, 20],
    ];
    for ex in &examples {
        print_json(ex);
    }

    let seeds: Vec<Vec<i32>> = vec![
        vec![1],
        vec![0, 0, 0, 0],
        vec![1, 2, 3, 4, 5],
        vec![-1_000_000_000, 1_000_000_000],
        vec![0, 0, 0, 0, 0],
        vec![1, 1, 1, 1, 1, 1, 1],
        vec![-5, -3, 0, 3, 5],
        vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10],
        vec![1_000_000_000, -1_000_000_000, 0, 999_999_999, -999_999_999],
        vec![7, 7, 7, 7, 7, 7, 7, 7],
    ];
    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    for seed_arr in &seeds {
        for &mk in &mutation_kinds {
            print_json(&mutate(seed_arr.clone(), mk));
        }
    }

    let size_classes: Vec<(usize, usize)> = vec![
        (1, 4),
        (5, 10),
        (11, 100),
        (101, 1000),
        (1001, 5000),
    ];
    for (lo, hi) in &size_classes {
        for _ in 0..5 {
            let len = rng.gen_range_usize(*lo, *hi);
            let arr = random_nums(&mut rng, len);
            let mk = rng.gen_range_usize(0, 10) as u8;
            print_json(&mutate(arr, mk));
        }
    }

    for t in 0..200 {
        let len = match t % 5 {
            0 => rng.gen_range_usize(1, 4),
            1 => rng.gen_range_usize(5, 10),
            2 => rng.gen_range_usize(11, 100),
            3 => rng.gen_range_usize(101, 1000),
            _ => rng.gen_range_usize(1001, 5000),
        };
        let arr = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 10) as u8;
        print_json(&mutate(arr, mk));
    }
}
