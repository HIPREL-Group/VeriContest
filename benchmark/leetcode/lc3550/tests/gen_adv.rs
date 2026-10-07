use vstd::prelude::*;

verus! {

pub fn generate_test_case(nums: Vec<i32>, mutation_kind: u8) -> (result: Vec<i32>)
    requires
        1 <= nums.len() <= 100,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
    ensures
        1 <= result.len() <= 100,
        forall|i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
{
    if mutation_kind == 0 {
        nums
    } else if mutation_kind == 1 {
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 0);
        r
    } else if mutation_kind == 2 {
        let mut r = nums;
        let last = r.len() - 1;
        r.set(last, 1000);
        r
    } else if mutation_kind == 3 {
        let mut r = nums;
        let mut i: usize = 0;
        while i < r.len()
            invariant
                0 <= i <= r.len(),
                r.len() == nums.len(),
                1 <= r.len() <= 100,
                forall|j: int| 0 <= j < i ==> r[j] == 0i32,
                forall|j: int| i <= j < r.len() ==> r[j] == nums[j],
            decreases r.len() - i,
        {
            r.set(i, 0);
            i += 1;
        }
        r
    } else if mutation_kind == 4 && nums.len() < 100 {
        let mut r = nums;
        r.push(0);
        r
    } else if mutation_kind == 5 && nums.len() > 1 {
        let mut r = nums;
        r.pop();
        r
    } else if mutation_kind == 6 {
        let mut r = nums;
        if r[0] < 1000 {
            r.set(0, r[0] + 1);
        }
        r
    } else if mutation_kind == 7 {
        let mut r = nums;
        if r[0] > 0 {
            r.set(0, r[0] - 1);
        }
        r
    } else if mutation_kind == 8 {
        let mut r = nums;
        let v = r[0];
        let ds = v / 1000 + (v / 100) % 10 + (v / 10) % 10 + v % 10;
        r.set(0, ds);
        assert(0 <= ds <= 28) by {
            assert(0 <= v <= 1000);
            assert(0 <= v / 1000 <= 1);
            assert(0 <= (v / 100) % 10 <= 9);
            assert(0 <= (v / 10) % 10 <= 9);
            assert(0 <= v % 10 <= 9);
        }
        r
    } else if mutation_kind == 9 {
        let mut r = nums;
        let val = r[0];
        let mut i: usize = 1;
        while i < r.len()
            invariant
                1 <= i <= r.len(),
                r.len() == nums.len(),
                1 <= r.len() <= 100,
                0 <= val <= 1000,
                forall|j: int| 0 <= j < i ==> r[j] == val,
                forall|j: int| i <= j < r.len() ==> r[j] == nums[j],
            decreases r.len() - i,
        {
            r.set(i, val);
            i += 1;
        }
        r
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
        nums.push(rng.gen_range_i64(0, 1000) as i32);
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
        args[1].parse::<u64>().unwrap_or(3550)
    } else {
        3550
    };
    let mut rng = Rng::new(seed);
    let total = 220usize;
    let seeds: Vec<Vec<i32>> = vec![
        vec![1, 3, 2],
        vec![1, 10, 11],
        vec![1, 2, 3],
        vec![0],
        vec![999],
    ];

    for t in 0..total {
        let mk = (t % 10) as u8;
        let base = if t < seeds.len() {
            seeds[t].clone()
        } else {
            let len = match t % 5 {
                0 => rng.gen_range_usize(1, 5),
                1 => rng.gen_range_usize(1, 10),
                2 => rng.gen_range_usize(11, 30),
                3 => rng.gen_range_usize(31, 70),
                _ => rng.gen_range_usize(71, 100),
            };
            random_nums(&mut rng, len)
        };
        let out = generate_test_case(base, mk);
        print_json(&out);
    }
}
