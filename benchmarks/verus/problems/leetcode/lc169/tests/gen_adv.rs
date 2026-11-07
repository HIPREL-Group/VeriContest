use vstd::prelude::*;

verus! {

pub open spec fn count_occ(s: Seq<i32>, value: i32) -> nat
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        count_occ(s.drop_last(), value) + 
            if s.last() == value { 1 as nat } else { 0 as nat }
    }
}

pub proof fn lemma_count_push(s: Seq<i32>, v: i32, value: i32)
    ensures count_occ(s.push(v), value) == count_occ(s, value) + (if v == value { 1 as nat } else { 0 as nat })
{
    let sp = s.push(v);
    assert(sp.len() == s.len() + 1);
    assert(sp.drop_last() =~= s);
    assert(sp.last() == v);
}

pub proof fn lemma_count_all_equal(s: Seq<i32>, value: i32)
    requires forall|i: int| 0 <= i < s.len() ==> s[i] == value,
    ensures count_occ(s, value) == s.len(),
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let t = s.drop_last();
        assert forall|i: int| 0 <= i < t.len() implies t[i] == value by {
            assert(t[i] == s[i]);
        }
        lemma_count_all_equal(t, value);
        assert(s.last() == value);
    }
}

pub fn generate_test_case(
    n: usize,
    maj_val: i32,
    maj_count: usize,
    filler: i32,
) -> (nums: Vec<i32>)
    requires
        1 <= n <= 50_000,
        -1_000_000_000 <= maj_val <= 1_000_000_000,
        -1_000_000_000 <= filler <= 1_000_000_000,
        maj_count > n / 2,
        maj_count <= n,
    ensures
        1 <= nums.len() <= 50_000,
        forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
        exists|i: int| 0 <= i < nums.len() && 
            #[trigger] count_occ(nums@, nums[i]) > nums.len() / 2,
{
    let mut nums: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    
    while k < maj_count
        invariant
            0 <= k <= maj_count,
            maj_count <= n,
            nums.len() == k,
            forall|i: int| 0 <= i < nums.len() ==> nums[i] == maj_val,
            -1_000_000_000 <= maj_val <= 1_000_000_000,
        decreases maj_count - k,
    {
        nums.push(maj_val);
        k += 1;
    }
    
    while k < n
        invariant
            maj_count <= k <= n,
            maj_count <= n,
            nums.len() == k,
            forall|i: int| 0 <= i < maj_count ==> nums[i] == maj_val,
            forall|i: int| 0 <= i < nums.len() ==> -1_000_000_000 <= #[trigger] nums[i] <= 1_000_000_000,
            -1_000_000_000 <= maj_val <= 1_000_000_000,
            -1_000_000_000 <= filler <= 1_000_000_000,
        decreases n - k,
    {
        nums.push(filler);
        k += 1;
    }
    
    proof {
        // Prove count_occ(nums@, maj_val) >= maj_count
        // Build up: for prefix of length maj_count, all are maj_val
        let prefix = nums@.subrange(0, maj_count as int);
        assert forall|i: int| 0 <= i < prefix.len() implies prefix[i] == maj_val by {
            assert(prefix[i] == nums@[i]);
        }
        lemma_count_all_equal(prefix, maj_val);
        assert(count_occ(prefix, maj_val) == maj_count);
        
        // Now prove count_occ(nums@, maj_val) >= count_occ(prefix, maj_val)
        lemma_count_monotone(nums@, maj_count as int, maj_val);
        assert(count_occ(nums@, maj_val) >= maj_count);
        assert(count_occ(nums@, maj_val) > n / 2);
        assert(nums.len() == n);
        assert(nums[0] == maj_val);
        assert(count_occ(nums@, nums[0]) > nums.len() / 2);
    }
    
    nums
}

pub proof fn lemma_count_monotone(s: Seq<i32>, k: int, value: i32)
    requires 0 <= k <= s.len(),
    ensures count_occ(s, value) >= count_occ(s.subrange(0, k), value),
    decreases s.len() - k
{
    if k == s.len() {
        assert(s.subrange(0, k) =~= s);
    } else {
        lemma_count_monotone(s, k + 1, value);
        let sp = s.subrange(0, k + 1);
        let spp = s.subrange(0, k);
        assert(sp.drop_last() =~= spp);
        assert(count_occ(sp, value) >= count_occ(spp, value));
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
        let span = (hi as i128 - lo as i128 + 1) as u128;
        let v = (self.next_u64() as u128) % span;
        lo + v as i64
    }
}

fn pick_test(rng: &mut Rng, mode: usize, idx: usize) -> (usize, i32, usize, i32) {
    match mode {
        0 => (1, 0, 1, 0),
        1 => (1, rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32, 1, 0),
        2 => {
            let n = 2 + (idx % 10);
            let maj = n / 2 + 1;
            (n, rng.gen_range_i64(-1000, 1000) as i32, maj, rng.gen_range_i64(-1000, 1000) as i32)
        }
        3 => {
            let n = 50_000;
            (n, 1, n, 0)
        }
        4 => {
            let n = 50_000;
            (n, -1_000_000_000, n / 2 + 1, 1_000_000_000)
        }
        5 => {
            let n = 49_999;
            (n, 0, n / 2 + 1, 1)
        }
        6 => {
            let n = 3;
            (n, rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32, 2, rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32)
        }
        7 => {
            let n = rng.gen_range_usize(100, 1000);
            let maj = n / 2 + 1;
            (n, rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32, maj, rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32)
        }
        8 => {
            let n = rng.gen_range_usize(1, 50_000);
            let maj = n / 2 + 1 + rng.gen_range_usize(0, (n - (n/2+1)).max(0) as usize);
            let maj = maj.min(n);
            (n, rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32, maj, rng.gen_range_i64(-1_000_000_000, 1_000_000_000) as i32)
        }
        9 => {
            let n = 2;
            (n, 7, 2, 0)
        }
        _ => {
            let n = rng.gen_range_usize(1, 100);
            let maj = n / 2 + 1;
            (n, rng.gen_range_i64(-5, 5) as i32, maj, rng.gen_range_i64(-5, 5) as i32)
        }
    }
}

// Simple shuffle for output diversity (not needed for validity; majority is still majority)
fn shuffle(rng: &mut Rng, nums: &mut Vec<i32>) {
    let n = nums.len();
    if n < 2 { return; }
    for i in (1..n).rev() {
        let j = rng.gen_range_usize(0, i);
        nums.swap(i, j);
    }
}

fn print_json(nums: &[i32]) {
    print!("{{\"nums\":[");
    for i in 0..nums.len() {
        if i > 0 { print!(","); }
        print!("{}", nums[i]);
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
        let (n, maj_val, maj_count, filler) = pick_test(&mut rng, mode, t);
        
        // Safety: validate constraints before calling
        if n < 1 || n > 50_000 { continue; }
        if maj_count <= n / 2 || maj_count > n { continue; }
        if maj_val < -1_000_000_000 || maj_val > 1_000_000_000 { continue; }
        if filler < -1_000_000_000 || filler > 1_000_000_000 { continue; }
        
        let mut nums = generate_test_case(n, maj_val, maj_count, filler);
        shuffle(&mut rng, &mut nums);
        print_json(&nums);
    }
}