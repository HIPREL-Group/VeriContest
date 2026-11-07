use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 1 <= #[trigger] nums[i] <= 1_000_000_000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 1 <= #[trigger] result[i] <= 1_000_000_000,
{
    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 {
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1);
        d
    } else if mutation_kind == 2 {
        let mut d = nums;
        let last = d.len() - 1;
        d.set(last, 1_000_000_000);
        d
    } else if mutation_kind == 3 && nums.len() < 100 {
        let mut d = nums;
        d.push(1);
        d
    } else if mutation_kind == 4 && nums.len() > 1 {
        let mut d = nums;
        d.pop();
        d
    } else if mutation_kind == 5 {
        let mut d = nums;
        let mut i: usize = 0;
        while i < d.len()
            invariant
                0 <= i <= d.len(),
                d.len() == nums.len(),
                1 <= d.len() <= 100,
                forall|j: int| 0 <= j < i ==> d[j] == 1i32,
                forall|j: int| i <= j < d.len() ==> d[j] == nums[j],
            decreases d.len() - i,
        {
            d.set(i, 1);
            i += 1;
        }
        d
    } else if mutation_kind == 6 {
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] < 1_000_000_000 {
            d.set(last, d[last] + 1);
        }
        d
    } else if mutation_kind == 7 {
        let mut d = nums;
        let last = d.len() - 1;
        if d[last] > 1 {
            d.set(last, d[last] - 1);
        }
        d
    } else if mutation_kind == 8 && nums.len() >= 2 {
        let mut d = nums;
        let last = d.len() - 1;
        let first_val = d[0];
        let last_val = d[last];
        d.set(0, last_val);
        d.set(last, first_val);
        d
    } else {
        nums
    }
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self {
            state: if seed == 0 { 1 } else { seed },
        }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self.state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_i64(&mut self, lo: i64, hi: i64) -> i64 {
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        lo + (self.next_u64() as usize % (hi - lo + 1))
    }
}

fn mutate(nums: Vec<i32>, mutation_kind: u8) -> Vec<i32> {
    generate_test_case(nums, mutation_kind)
}

fn random_nums(rng: &mut Rng, len: usize) -> Vec<i32> {
    let mut nums = Vec::with_capacity(len);
    for _ in 0..len {
        nums.push(rng.gen_range_i64(1, 1_000_000_000) as i32);
    }
    nums
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

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(3769)
    } else {
        3769
    };

    let mut rng = Rng::new(seed);

    let seeds: Vec<Vec<i32>> = vec![
        vec![4, 5, 4],
        vec![3, 6, 5, 8],
        vec![1],
        vec![1_000_000_000],
        vec![1, 2, 3, 4, 5],
        vec![5, 4, 3, 2, 1],
        vec![1, 1, 1, 1],
        vec![7, 7, 7],
        vec![1, 1_000_000_000],
        vec![2, 4, 8, 16, 32],
        vec![1, 3, 7, 15, 31, 63],
        vec![512, 256, 128, 64, 32, 16, 8, 4, 2, 1],
    ];

    let mutation_kinds: Vec<u8> = vec![0, 1, 2, 3, 4, 5, 6, 7, 8];

    let total = 200usize;
    let mut count = 0usize;

    for s in &seeds {
        for &mk in &mutation_kinds {
            if count >= total {
                break;
            }
            let result = mutate(s.clone(), mk);
            print_json(&result);
            count += 1;
        }
        if count >= total {
            break;
        }
    }

    let size_classes: Vec<(usize, usize)> = vec![(1, 3), (4, 10), (11, 30), (31, 70), (71, 100)];

    while count < total {
        let (lo, hi) = size_classes[count % size_classes.len()];
        let len = rng.gen_range_usize(lo, hi);
        let s = random_nums(&mut rng, len);
        let mk = rng.gen_range_usize(0, 8) as u8;
        let result = mutate(s, mk);
        print_json(&result);
        count += 1;
    }
}
