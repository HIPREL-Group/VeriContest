use vstd::prelude::*;

verus! {

pub open spec fn count_plain_prefix_s(nums: Seq<i32>, end: int, v: int) -> int
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        count_plain_prefix_s(nums, end - 1, v) + if nums[end - 1] as int == v { 1int } else { 0int }
    }
}

pub open spec fn count_shift_prefix_s(nums: Seq<i32>, end: int, x: int, v: int) -> int
    decreases end,
{
    if end <= 0 {
        0int
    } else {
        count_shift_prefix_s(nums, end - 1, x, v) + if nums[end - 1] as int + x == v { 1int } else { 0int }
    }
}

// Lemma: if nums1 = nums2 prefixed/contains elements such that every shifted element is in nums2,
// then count_shift >= count_plain. We'll prove stronger: if nums1 = nums2 with two extra elements
// appended, then for all v, shift count >= plain count.

// Instead, we use a simpler construction: nums1 = (nums2[i] - x for i) ++ [extra1, extra2]
// Then count_shift_prefix(nums1, len, x, v) = count_plain_prefix(nums2, nums2.len, v)
//   + (extras shifted that equal v).
// So count_shift >= count_plain.

pub proof fn lemma_count_shift_equals_plain(nums1: Seq<i32>, nums2: Seq<i32>, x: int, v: int)
    requires
        nums1.len() == nums2.len(),
        forall |i: int| 0 <= i < nums2.len() ==> #[trigger] nums1[i] as int + x == nums2[i] as int,
    ensures
        count_shift_prefix_s(nums1, nums1.len() as int, x, v) == count_plain_prefix_s(nums2, nums2.len() as int, v),
    decreases nums1.len(),
{
    if nums1.len() == 0 {
    } else {
        let n1p = nums1.subrange(0, nums1.len() as int - 1);
        let n2p = nums2.subrange(0, nums2.len() as int - 1);
        assert(n1p.len() == nums1.len() - 1);
        assert(n2p.len() == nums2.len() - 1);
        assert forall |i: int| 0 <= i < n2p.len() implies #[trigger] n1p[i] as int + x == n2p[i] as int by {
            assert(n1p[i] == nums1[i]);
            assert(n2p[i] == nums2[i]);
        }
        lemma_count_shift_equals_plain(n1p, n2p, x, v);
        lemma_count_shift_prefix_extend(nums1, n1p, x, v);
        lemma_count_plain_prefix_extend(nums2, n2p, v);
    }
}

pub proof fn lemma_count_shift_prefix_extend(nums: Seq<i32>, prefix: Seq<i32>, x: int, v: int)
    requires
        nums.len() >= 1,
        prefix == nums.subrange(0, nums.len() as int - 1),
    ensures
        count_shift_prefix_s(nums, nums.len() as int, x, v) ==
            count_shift_prefix_s(prefix, prefix.len() as int, x, v) +
            (if nums[nums.len() as int - 1] as int + x == v { 1int } else { 0int }),
    decreases nums.len(),
{
    lemma_count_shift_prefix_agree(nums, prefix, nums.len() as int - 1, x, v);
}

pub proof fn lemma_count_shift_prefix_agree(nums: Seq<i32>, prefix: Seq<i32>, end: int, x: int, v: int)
    requires
        0 <= end <= prefix.len(),
        prefix.len() + 1 == nums.len(),
        prefix == nums.subrange(0, nums.len() as int - 1),
    ensures
        count_shift_prefix_s(nums, end, x, v) == count_shift_prefix_s(prefix, end, x, v),
    decreases end,
{
    if end <= 0 {
    } else {
        lemma_count_shift_prefix_agree(nums, prefix, end - 1, x, v);
        assert(nums[end - 1] == prefix[end - 1]);
    }
}

pub proof fn lemma_count_plain_prefix_extend(nums: Seq<i32>, prefix: Seq<i32>, v: int)
    requires
        nums.len() >= 1,
        prefix == nums.subrange(0, nums.len() as int - 1),
    ensures
        count_plain_prefix_s(nums, nums.len() as int, v) ==
            count_plain_prefix_s(prefix, prefix.len() as int, v) +
            (if nums[nums.len() as int - 1] as int == v { 1int } else { 0int }),
    decreases nums.len(),
{
    lemma_count_plain_prefix_agree(nums, prefix, nums.len() as int - 1, v);
}

pub proof fn lemma_count_plain_prefix_agree(nums: Seq<i32>, prefix: Seq<i32>, end: int, v: int)
    requires
        0 <= end <= prefix.len(),
        prefix.len() + 1 == nums.len(),
        prefix == nums.subrange(0, nums.len() as int - 1),
    ensures
        count_plain_prefix_s(nums, end, v) == count_plain_prefix_s(prefix, end, v),
    decreases end,
{
    if end <= 0 {
    } else {
        lemma_count_plain_prefix_agree(nums, prefix, end - 1, v);
        assert(nums[end - 1] == prefix[end - 1]);
    }
}

// Appending extras to shifted array preserves >= relation.
pub proof fn lemma_count_shift_append_nonneg(nums: Seq<i32>, extras: Seq<i32>, x: int, v: int)
    ensures
        count_shift_prefix_s(nums + extras, (nums.len() + extras.len()) as int, x, v) >=
            count_shift_prefix_s(nums, nums.len() as int, x, v),
    decreases extras.len(),
{
    if extras.len() == 0 {
        assert(nums + extras =~= nums);
    } else {
        let extras_prefix = extras.subrange(0, extras.len() as int - 1);
        let combined = nums + extras;
        let combined_prefix = nums + extras_prefix;
        assert(combined_prefix =~= combined.subrange(0, combined.len() as int - 1));
        lemma_count_shift_prefix_extend(combined, combined_prefix, x, v);
        lemma_count_shift_append_nonneg(nums, extras_prefix, x, v);
    }
}

pub fn generate_test_case(
    x: i32,
    extra1: i32,
    extra2: i32,
    base: &Vec<i32>,
) -> (result: (Vec<i32>, Vec<i32>))
    requires
        -1000 <= x <= 1000,
        0 <= extra1 <= 1000,
        0 <= extra2 <= 1000,
        1 <= base.len() <= 198,
        forall |i: int| 0 <= i < base.len() ==> 0 <= #[trigger] base[i] as int - x as int <= 1000,
        forall |i: int| 0 <= i < base.len() ==> 0 <= #[trigger] base[i] <= 1000,
    ensures
        3 <= result.0.len() <= 200,
        result.1.len() + 2 == result.0.len(),
        forall |i: int| 0 <= i < result.0.len() ==> 0 <= #[trigger] result.0[i] <= 1000,
        forall |i: int| 0 <= i < result.1.len() ==> 0 <= #[trigger] result.1[i] <= 1000,
        exists |xx: int| -1000 <= xx <= 1000 && Solution_valid_x_spec(result.0@, result.1@, xx),
{
    // nums2 = base (with values in [0,1000])
    // nums1 = [base[i] - x for all i] ++ [extra1, extra2]
    // So for nums1 shifted by x: shifted[i] == base[i] for i < base.len, plus extras+x
    
    let mut nums1: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < base.len()
        invariant
            0 <= i <= base.len(),
            nums1.len() == i,
            forall |k: int| 0 <= k < i ==> #[trigger] nums1[k] as int == base[k] as int - x as int,
            forall |k: int| 0 <= k < i ==> 0 <= #[trigger] nums1[k] <= 1000,
            forall |k: int| 0 <= k < base.len() ==> 0 <= #[trigger] base[k] as int - x as int <= 1000,
        decreases base.len() - i,
    {
        let v = base[i] - x;
        assert(v as int == base[i as int] as int - x as int);
        assert(0 <= v <= 1000);
        nums1.push(v);
        i = i + 1;
    }
    
    // Save shifted prefix for proof
    let shifted_len = nums1.len();
    nums1.push(extra1);
    nums1.push(extra2);
    
    let nums2: Vec<i32> = base.clone();
    
    proof {
        assert(nums1.len() == base.len() + 2);
        assert(nums2.len() == base.len());
        assert(nums1.len() >= 3);
        assert(nums1.len() <= 200);
        
        // Range checks
        assert forall |k: int| 0 <= k < nums1.len() implies 0 <= #[trigger] nums1[k] <= 1000 by {
            if k < shifted_len as int {
                // nums1[k] == base[k] - x, which is in [0,1000]
            } else if k == shifted_len as int {
                assert(nums1[k] == extra1);
            } else {
                assert(nums1[k] == extra2);
            }
        }
        
        assert forall |k: int| 0 <= k < nums2.len() implies 0 <= #[trigger] nums2[k] <= 1000 by {
            assert(nums2[k] == base[k]);
        }
        
        // Now prove exists x such that valid_x_spec.
        // For our x, count_shift(nums1, len, x, v) >= count_plain(nums2, len, v) for all v.
        
        let shifted_seq = nums1@.subrange(0, shifted_len as int);
        let full_seq = nums1@;
        let extras = seq![extra1, extra2];
        
        assert(shifted_seq.len() == base.len());
        assert(nums2@.len() == base.len());
        
        assert forall |k: int| 0 <= k < nums2@.len() implies 
            #[trigger] shifted_seq[k] as int + x as int == nums2@[k] as int by {
            assert(shifted_seq[k] == nums1@[k]);
            assert(nums2@[k] == base[k]);
        }
        
        // shifted_seq ++ extras == full_seq
        assert(full_seq.len() == shifted_len + 2);
        assert(shifted_seq + extras =~= full_seq) by {
            assert((shifted_seq + extras).len() == full_seq.len());
            assert forall |k: int| 0 <= k < full_seq.len() implies 
                (shifted_seq + extras)[k] == full_seq[k] by {
                if k < shifted_len as int {
                    assert((shifted_seq + extras)[k] == shifted_seq[k]);
                    assert(shifted_seq[k] == nums1@[k]);
                } else if k == shifted_len as int {
                    assert((shifted_seq + extras)[k] == extras[0]);
                    assert(full_seq[k] == extra1);
                } else {
                    assert((shifted_seq + extras)[k] == extras[1]);
                    assert(full_seq[k] == extra2);
                }
            }
        }
        
        assert forall |v: int| 0 <= v <= 1000 implies
            count_shift_prefix_s(nums1@, nums1@.len() as int, x as int, v) >=
            count_plain_prefix_s(nums2@, nums2@.len() as int, v) by {
            lemma_count_shift_equals_plain(shifted_seq, nums2@, x as int, v);
            lemma_count_shift_append_nonneg(shifted_seq, extras, x as int, v);
            assert(shifted_seq + extras == full_seq);
        }
        
        assert(Solution_valid_x_spec(nums1@, nums2@, x as int));
        assert(-1000 <= x as int <= 1000);
    }
    
    (nums1, nums2)
}

pub open spec fn Solution_valid_x_spec(nums1: Seq<i32>, nums2: Seq<i32>, x: int) -> bool {
    forall |v: int| 0 <= v <= 1000 ==> count_shift_prefix_s(nums1, nums1.len() as int, x, v) >= count_plain_prefix_s(nums2, nums2.len() as int, v)
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
    fn gen_range_i32(&mut self, lo: i32, hi: i32) -> i32 {
        let span = (hi as i64 - lo as i64 + 1) as u64;
        lo + (self.next_u64() % span) as i32
    }
    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        let span = (hi - lo + 1) as u64;
        lo + (self.next_u64() % span) as usize
    }
}

fn build_test(rng: &mut Rng, mode: usize) -> (i32, i32, i32, Vec<i32>) {
    // Decide x, extras, base such that:
    // - x in [-1000,1000]
    // - extras in [0,1000]
    // - base has length in [1,198]
    // - for each base[i]: base[i] in [0,1000] AND base[i]-x in [0,1000]
    //   i.e., base[i] in [max(0,x), min(1000,1000+x)]
    
    let x: i32 = match mode {
        0 => 0,
        1 => 1000,
        2 => -1000,
        3 => 1,
        4 => -1,
        5 => 500,
        6 => -500,
        7 => rng.gen_range_i32(-1000, 1000),
        8 => rng.gen_range_i32(-10, 10),
        9 => rng.gen_range_i32(-100, 100),
        _ => rng.gen_range_i32(-1000, 1000),
    };
    
    let base_len: usize = match mode {
        0 => 1,
        1 => 198,
        2 => 198,
        3 => rng.gen_range_usize(1, 5),
        _ => rng.gen_range_usize(1, 198),
    };
    
    let lo_base: i32 = if x > 0 { x } else { 0 };
    let hi_base: i32 = if x < 0 { 1000 + x } else { 1000 };
    
    let mut base: Vec<i32> = Vec::with_capacity(base_len);
    for _ in 0..base_len {
        let v = rng.gen_range_i32(lo_base, hi_base);
        base.push(v);
    }
    
    let extra1 = rng.gen_range_i32(0, 1000);
    let extra2 = rng.gen_range_i32(0, 1000);
    
    (x, extra1, extra2, base)
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
    let total = 200usize;
    let modes = 10usize;
    
    for t in 0..total {
        let mode = t % modes;
        let (x, e1, e2, base) = build_test(&mut rng, mode);
        let (nums1, nums2) = generate_test_case(x, e1, e2, &base);
        print_json(&nums1, &nums2);
    }
}