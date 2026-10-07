use vstd::prelude::*;

verus! {

pub fn generate_test_case(
    max_val: i32,
    max_idx: usize,
    fillers: &Vec<i32>,
) -> (nums: Vec<i32>)
    requires
        1 <= max_val <= 100,
        fillers.len() + 1 >= 2,
        fillers.len() + 1 <= 50,
        max_idx < fillers.len() + 1,
        forall|i: int| 0 <= i < fillers.len() ==>
            0 <= #[trigger] fillers[i] < max_val,
    ensures
        2 <= nums.len() <= 50,
        forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 100,
        exists|i: int| #![trigger nums[i]] 0 <= i < nums.len() &&
            forall|j: int| 0 <= j < nums.len() && j != i ==> nums[i] > #[trigger] nums[j],
{
    let n: usize = fillers.len() + 1;
    let mut nums: Vec<i32> = Vec::new();
    let mut fi: usize = 0;
    let mut pos: usize = 0;

    while pos < n
        invariant
            n == fillers.len() + 1,
            2 <= n <= 50,
            0 <= pos <= n,
            nums.len() == pos,
            max_idx < n,
            1 <= max_val <= 100,
            0 <= fi <= fillers.len(),
            fi == pos - (if max_idx < pos { 1usize } else { 0usize }),
            forall|k: int| 0 <= k < pos as int && k == max_idx as int ==>
                #[trigger] nums[k] == max_val,
            forall|k: int| 0 <= k < pos as int && k < max_idx as int ==>
                #[trigger] nums[k] == fillers[k],
            forall|k: int| 0 <= k < pos as int && k > max_idx as int ==>
                #[trigger] nums[k] == fillers[k - 1],
            forall|k: int| 0 <= k < pos as int ==>
                0 <= #[trigger] nums[k] <= 100,
            forall|k: int| 0 <= k < pos as int && k != max_idx as int ==>
                #[trigger] nums[k] < max_val,
            forall|i: int| 0 <= i < fillers.len() ==>
                0 <= #[trigger] fillers[i] < max_val,
        decreases n - pos,
    {
        if pos == max_idx {
            nums.push(max_val);
        } else {
            assert(fi < fillers.len());
            let v = fillers[fi];
            nums.push(v);
            fi = fi + 1;
        }
        pos = pos + 1;
    }

    proof {
        assert(nums[max_idx as int] == max_val);
        assert forall|j: int| 0 <= j < nums.len() && j != max_idx as int
            implies nums[max_idx as int] > #[trigger] nums[j]
        by {
            if j < max_idx as int {
                assert(nums[j] == fillers[j]);
                assert(fillers[j] < max_val);
            } else {
                assert(nums[j] == fillers[j - 1]);
                assert(fillers[j - 1] < max_val);
            }
        }
        assert(exists|i: int| #![trigger nums[i]] 0 <= i < nums.len() &&
            forall|j: int| 0 <= j < nums.len() && j != i ==> nums[i] > #[trigger] nums[j])
        by {
            assert(0 <= max_idx < nums.len());
            assert(nums[max_idx as int] == max_val);
        }
    }

    nums
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
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
}

fn make_fillers(rng: &mut Rng, count: usize, max_val: i32, mode: usize) -> Vec<i32> {
    let mut res: Vec<i32> = Vec::with_capacity(count);
    for i in 0..count {
        let v = match mode {
            0 => rng.gen_range_i32(0, max_val - 1),
            1 => 0,
            2 => max_val - 1, // just below max
            3 => if max_val >= 2 { max_val / 2 } else { 0 },
            4 => if max_val >= 2 { max_val / 2 + 1 } else { 0 }, // not quite half
            5 => if max_val >= 2 { (max_val - 1) / 2 } else { 0 }, // exactly at boundary
            6 => {
                // alternate 0 and max-1
                if i % 2 == 0 { 0 } else { max_val - 1 }
            }
            7 => {
                // random 0..=max/2
                let hi = if max_val >= 2 { max_val / 2 } else { 0 };
                rng.gen_range_i32(0, hi)
            }
            8 => {
                // random around max/2
                let lo = if max_val >= 3 { max_val / 2 - 1 } else { 0 };
                let hi = if max_val >= 2 { max_val - 1 } else { 0 };
                rng.gen_range_i32(lo, hi)
            }
            _ => rng.gen_range_i32(0, max_val - 1),
        };
        let v = if v < 0 { 0 } else if v >= max_val { max_val - 1 } else { v };
        res.push(v);
    }
    res
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
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let modes = 9usize;
    let total = 200usize;

    for t in 0..total {
        let mode = t % modes;

        // Pick n in [2, 50]
        let n: usize = match t % 7 {
            0 => 2,
            1 => 50,
            2 => 3,
            3 => 10,
            4 => 25,
            5 => rng.gen_range_usize(2, 50),
            _ => rng.gen_range_usize(2, 20),
        };

        // Pick max_val in [1, 100]
        let max_val: i32 = match t % 5 {
            0 => 100,
            1 => 1,
            2 => 2,
            3 => 50,
            _ => rng.gen_range_i32(1, 100),
        };

        let max_idx: usize = match t % 4 {
            0 => 0,
            1 => n - 1,
            2 => n / 2,
            _ => rng.gen_range_usize(0, n - 1),
        };

        let fillers = make_fillers(&mut rng, n - 1, max_val, mode);

        let nums = generate_test_case(max_val, max_idx, &fillers);
        print_json(&nums);
    }
}