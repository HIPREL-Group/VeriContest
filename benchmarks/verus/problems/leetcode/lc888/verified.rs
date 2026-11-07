use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn seq_sum(s: Seq<i32>, end: int) -> int
        decreases end,
    {
        if end <= 0 {
            0
        } else {
            Self::seq_sum(s, end - 1) + s[end - 1] as int
        }
    }

    proof fn seq_sum_prefix_same(s: Seq<i32>, x: i32, end: int)
        requires
            0 <= end <= s.len(),
        ensures
            Self::seq_sum(s.push(x), end) == Self::seq_sum(s, end),
        decreases end,
    {
        if end > 0 {
            Self::seq_sum_prefix_same(s, x, end - 1);
            assert(s.push(x)[end - 1] == s[end - 1]);
        }
    }

    proof fn seq_sum_push(s: Seq<i32>, x: i32)
        ensures
            Self::seq_sum(s.push(x), s.len() as int + 1) == Self::seq_sum(s, s.len() as int) + x as int,
    {
        Self::seq_sum_prefix_same(s, x, s.len() as int);
        assert(s.push(x)[s.len() as int] == x);
        assert(Self::seq_sum(s.push(x), s.len() as int) == Self::seq_sum(s, s.len() as int));
    }

    pub open spec fn appears_in(s: Seq<i32>, value: i32) -> bool {
        exists |i: int| 0 <= i < s.len() && #[trigger] s[i] == value
    }

    pub open spec fn valid_swap_int(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>, alice_box: int, bob_box: int) -> bool {
        &&& 1 <= alice_box <= 100_000
        &&& 1 <= bob_box <= 100_000
        &&& Self::appears_in(alice_sizes, alice_box as i32)
        &&& Self::appears_in(bob_sizes, bob_box as i32)
        &&& Self::seq_sum(alice_sizes, alice_sizes.len() as int) - alice_box + bob_box
            == Self::seq_sum(bob_sizes, bob_sizes.len() as int) - bob_box + alice_box
    }

    pub open spec fn valid_swap(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>, alice_box: i32, bob_box: i32) -> bool {
        Self::valid_swap_int(alice_sizes, bob_sizes, alice_box as int, bob_box as int)
    }

    pub open spec fn delta(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>) -> int {
        (Self::seq_sum(alice_sizes, alice_sizes.len() as int) - Self::seq_sum(bob_sizes, bob_sizes.len() as int)) / 2
    }

    fn set_flag(flags: &mut Vec<bool>, idx: usize, value: bool)
        requires
            idx < old(flags)@.len(),
        ensures
            flags@.len() == old(flags)@.len(),
            forall |k: int| 0 <= k < flags@.len() ==> #[trigger] flags@[k] == if k == idx as int { value } else { old(flags)@[k] },
    {
        flags[idx] = value;
    }

    proof fn lemma_i128_sum_as_int(a: int, b: int)
        requires
            -500_000_000 <= a <= 500_000_000,
            -500_000_000 <= b <= 500_000_000,
        ensures
            (a as i128 + b as i128) as int == a + b,
    {
    }

    proof fn valid_swap_has_delta(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>, alice_box: int, bob_box: int)
        requires
            Self::valid_swap_int(alice_sizes, bob_sizes, alice_box, bob_box),
        ensures
            alice_box == bob_box + Self::delta(alice_sizes, bob_sizes),
    {
        let sum_a = Self::seq_sum(alice_sizes, alice_sizes.len() as int);
        let sum_b = Self::seq_sum(bob_sizes, bob_sizes.len() as int);
        assert(sum_a - alice_box + bob_box == sum_b - bob_box + alice_box);
        assert(sum_a - sum_b == (sum_a - alice_box + bob_box) - sum_b + alice_box - bob_box) by (nonlinear_arith);
        assert((sum_a - alice_box + bob_box) - sum_b + alice_box - bob_box
            == (sum_b - bob_box + alice_box) - sum_b + alice_box - bob_box);
        assert((sum_b - bob_box + alice_box) - sum_b + alice_box - bob_box == 2 * (alice_box - bob_box)) by (nonlinear_arith);
        assert(sum_a - sum_b == 2 * (alice_box - bob_box));
        assert(Self::delta(alice_sizes, bob_sizes) == (sum_a - sum_b) / 2);
        assert((2 * (alice_box - bob_box)) / 2 == alice_box - bob_box) by (nonlinear_arith);
    }

    proof fn valid_swap_implies_even_diff(alice_sizes: Seq<i32>, bob_sizes: Seq<i32>)
        requires
            exists |alice_box: int, bob_box: int| Self::valid_swap_int(alice_sizes, bob_sizes, alice_box, bob_box),
        ensures
            2 * Self::delta(alice_sizes, bob_sizes) == Self::seq_sum(alice_sizes, alice_sizes.len() as int)
                - Self::seq_sum(bob_sizes, bob_sizes.len() as int),
    {
        let (alice_box, bob_box) = choose |alice_box: int, bob_box: int|
            Self::valid_swap_int(alice_sizes, bob_sizes, alice_box, bob_box);
        Self::valid_swap_has_delta(alice_sizes, bob_sizes, alice_box, bob_box);
        let sum_a = Self::seq_sum(alice_sizes, alice_sizes.len() as int);
        let sum_b = Self::seq_sum(bob_sizes, bob_sizes.len() as int);
        assert(sum_a - alice_box + bob_box == sum_b - bob_box + alice_box);
        assert((sum_a - alice_box + bob_box) - (sum_b - bob_box + alice_box) == 0);
        assert((sum_a - alice_box + bob_box) - (sum_b - bob_box + alice_box)
            == (sum_a - sum_b) - 2 * (alice_box - bob_box)) by (nonlinear_arith);
        assert((sum_a - sum_b) - 2 * (alice_box - bob_box) == 0);
        assert(sum_a - sum_b == 2 * (alice_box - bob_box));
        assert(alice_box - bob_box == Self::delta(alice_sizes, bob_sizes));
        assert(sum_a - sum_b == 2 * Self::delta(alice_sizes, bob_sizes));
    }

    pub fn fair_candy_swap(alice_sizes: Vec<i32>, bob_sizes: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= alice_sizes.len() <= 10_000,
            1 <= bob_sizes.len() <= 10_000,
            forall |i: int| 0 <= i < alice_sizes.len() ==> 1 <= #[trigger] alice_sizes[i] <= 100_000,
            forall |j: int| 0 <= j < bob_sizes.len() ==> 1 <= #[trigger] bob_sizes[j] <= 100_000,
            Self::seq_sum(alice_sizes@, alice_sizes.len() as int) != Self::seq_sum(bob_sizes@, bob_sizes.len() as int),
            exists |alice_box: int, bob_box: int| Self::valid_swap_int(alice_sizes@, bob_sizes@, alice_box, bob_box),
        ensures
            result.len() == 2,
            Self::valid_swap(alice_sizes@, bob_sizes@, result[0], result[1]),
    {
        let mut sum_a = 0i128;
        let mut i = 0usize;
        while i < alice_sizes.len()
            invariant
                1 <= alice_sizes.len() <= 10_000,
                forall |k: int| 0 <= k < alice_sizes.len() ==> 1 <= #[trigger] alice_sizes[k] <= 100_000,
                0 <= i <= alice_sizes.len(),
                sum_a as int == Self::seq_sum(alice_sizes@.subrange(0, i as int), i as int),
                0 <= sum_a as int <= 100_000 * i as int,
            decreases alice_sizes.len() - i,
        {
            let ghost prev_sum = sum_a as int;
            proof {
                assert(alice_sizes@.subrange(0, i as int + 1) =~= alice_sizes@.subrange(0, i as int).push(alice_sizes@[i as int]));
            }
            sum_a = sum_a + alice_sizes[i] as i128;
            proof {
                Self::seq_sum_push(alice_sizes@.subrange(0, i as int), alice_sizes@[i as int]);
                assert(sum_a as int == prev_sum + alice_sizes@[i as int] as int);
                assert(sum_a as int == Self::seq_sum(alice_sizes@.subrange(0, i as int + 1), i as int + 1));
                assert(0 <= sum_a as int <= 100_000 * (i as int + 1)) by (nonlinear_arith)
                    requires
                        0 <= prev_sum <= 100_000 * i as int,
                        1 <= alice_sizes@[i as int] as int <= 100_000,
                        sum_a as int == prev_sum + alice_sizes@[i as int] as int,
                {}
            }
            i = i + 1;
        }
        proof {
            assert(alice_sizes@.subrange(0, alice_sizes.len() as int) =~= alice_sizes@);
            assert(sum_a as int == Self::seq_sum(alice_sizes@, alice_sizes.len() as int));
        }

        let mut sum_b = 0i128;
        i = 0usize;
        while i < bob_sizes.len()
            invariant
                1 <= bob_sizes.len() <= 10_000,
                forall |k: int| 0 <= k < bob_sizes.len() ==> 1 <= #[trigger] bob_sizes[k] <= 100_000,
                0 <= i <= bob_sizes.len(),
                sum_b as int == Self::seq_sum(bob_sizes@.subrange(0, i as int), i as int),
                0 <= sum_b as int <= 100_000 * i as int,
            decreases bob_sizes.len() - i,
        {
            let ghost prev_sum = sum_b as int;
            proof {
                assert(bob_sizes@.subrange(0, i as int + 1) =~= bob_sizes@.subrange(0, i as int).push(bob_sizes@[i as int]));
            }
            sum_b = sum_b + bob_sizes[i] as i128;
            proof {
                Self::seq_sum_push(bob_sizes@.subrange(0, i as int), bob_sizes@[i as int]);
                assert(sum_b as int == prev_sum + bob_sizes@[i as int] as int);
                assert(sum_b as int == Self::seq_sum(bob_sizes@.subrange(0, i as int + 1), i as int + 1));
                assert(0 <= sum_b as int <= 100_000 * (i as int + 1)) by (nonlinear_arith)
                    requires
                        0 <= prev_sum <= 100_000 * i as int,
                        1 <= bob_sizes@[i as int] as int <= 100_000,
                        sum_b as int == prev_sum + bob_sizes@[i as int] as int,
                {}
            }
            i = i + 1;
        }
        proof {
            assert(bob_sizes@.subrange(0, bob_sizes.len() as int) =~= bob_sizes@);
            assert(sum_b as int == Self::seq_sum(bob_sizes@, bob_sizes.len() as int));
        }

        let delta = (sum_a - sum_b) / 2;
        proof {
            assert(sum_a as int == Self::seq_sum(alice_sizes@, alice_sizes.len() as int));
            assert(sum_b as int == Self::seq_sum(bob_sizes@, bob_sizes.len() as int));
            assert(delta as int == Self::delta(alice_sizes@, bob_sizes@));
            assert(0 <= sum_a as int <= 1_000_000_000) by (nonlinear_arith)
                requires
                    0 <= sum_a as int <= 100_000 * alice_sizes.len() as int,
                    alice_sizes.len() <= 10_000,
            {}
            assert(0 <= sum_b as int <= 1_000_000_000) by (nonlinear_arith)
                requires
                    0 <= sum_b as int <= 100_000 * bob_sizes.len() as int,
                    bob_sizes.len() <= 10_000,
            {}
            assert(-500_000_000 <= delta as int <= 500_000_000) by (nonlinear_arith)
                requires
                    0 <= sum_a as int <= 1_000_000_000,
                    0 <= sum_b as int <= 1_000_000_000,
                    delta as int == (sum_a as int - sum_b as int) / 2,
            {}
        }

        let mut present: Vec<bool> = Vec::new();
        let mut size = 0usize;
        while size <= 100000usize
            invariant
                0 <= size <= 100001,
                present@.len() == size as int,
                forall |k: int| 0 <= k < present@.len() ==> #[trigger] present@[k] == false,
            decreases 100001usize - size,
        {
            let ghost before = present@;
            present.push(false);
            proof {
                assert(present@ == before.push(false));
                assert forall |k: int| 0 <= k < present@.len() implies #[trigger] present@[k] == false by {
                    if k < before.len() {
                        assert(present@[k] == before[k]);
                    } else {
                        assert(k == before.len());
                        assert(present@[k] == false);
                    }
                };
            }
            size = size + 1;
        }
        proof {
            assert(size == 100001usize);
            assert(present@.len() == 100001);
        }

        i = 0usize;
        while i < alice_sizes.len()
            invariant
                1 <= alice_sizes.len() <= 10_000,
                forall |k: int| 0 <= k < alice_sizes.len() ==> 1 <= #[trigger] alice_sizes[k] <= 100_000,
                present@.len() == 100001,
                0 <= i <= alice_sizes.len(),
                forall |v: int|
                    0 <= v < 100001 ==> #[trigger] present@[v] == (exists |k: int| 0 <= k < i as int && alice_sizes[k] == v),
            decreases alice_sizes.len() - i,
        {
            let idx = alice_sizes[i] as usize;
            let ghost before = present@;
            Self::set_flag(&mut present, idx, true);
            proof {
                assert(idx as int == alice_sizes[i as int]);
                assert forall |v: int|
                    0 <= v < 100001
                    implies #[trigger] present@[v] == (exists |k: int| 0 <= k < i as int + 1 && alice_sizes[k] == v)
                by {
                    if v == idx as int {
                        assert(present@[v]);
                        assert(exists |k: int| 0 <= k < i as int + 1 && alice_sizes[k] == v);
                    } else {
                        assert(present@[v] == before[v]);
                        if exists |k: int| 0 <= k < i as int + 1 && alice_sizes[k] == v {
                            let k = choose |k: int| 0 <= k < i as int + 1 && alice_sizes[k] == v;
                            assert(k < i as int);
                            assert(before[v]);
                        } else {
                            assert(!(exists |k: int| 0 <= k < i as int && alice_sizes[k] == v));
                            assert(!before[v]);
                        }
                    }
                };
            }
            i = i + 1;
        }
        proof {
            if i < alice_sizes.len() {
                assert(false);
            }
            assert(i == alice_sizes.len());
            assert forall |v: int| 0 <= v < 100001 implies #[trigger] present@[v] == Self::appears_in(alice_sizes@, v as i32) by {
                if present@[v] {
                    let k = choose |k: int| 0 <= k < i as int && alice_sizes[k] == v;
                    assert(0 <= k < alice_sizes.len());
                    assert(Self::appears_in(alice_sizes@, v as i32));
                } else {
                    if Self::appears_in(alice_sizes@, v as i32) {
                        let k = choose |k: int| 0 <= k < alice_sizes.len() && alice_sizes[k] == v as i32;
                        assert(0 <= k < i as int);
                        assert(present@[v]);
                        assert(false);
                    }
                }
            };
        }

        proof {
            Self::valid_swap_implies_even_diff(alice_sizes@, bob_sizes@);
            assert(2 * (delta as int) == Self::seq_sum(alice_sizes@, alice_sizes.len() as int)
                - Self::seq_sum(bob_sizes@, bob_sizes.len() as int));
        }
        let mut j = 0usize;
        while j < bob_sizes.len()
            invariant
                1 <= alice_sizes.len() <= 10_000,
                1 <= bob_sizes.len() <= 10_000,
                forall |k: int| 0 <= k < alice_sizes.len() ==> 1 <= #[trigger] alice_sizes[k] <= 100_000,
                forall |k: int| 0 <= k < bob_sizes.len() ==> 1 <= #[trigger] bob_sizes[k] <= 100_000,
                present@.len() == 100001,
                forall |v: int| 0 <= v < 100001 ==> #[trigger] present@[v] == Self::appears_in(alice_sizes@, v as i32),
                delta as int == Self::delta(alice_sizes@, bob_sizes@),
                2 * (delta as int) == Self::seq_sum(alice_sizes@, alice_sizes.len() as int)
                    - Self::seq_sum(bob_sizes@, bob_sizes.len() as int),
                -500_000_000 <= delta as int <= 500_000_000,
                0 <= j <= bob_sizes.len(),
                forall |k: int|
                    0 <= k < j ==> !Self::valid_swap_int(alice_sizes@, bob_sizes@, bob_sizes[k] as int + Self::delta(alice_sizes@, bob_sizes@), bob_sizes[k] as int),
            decreases bob_sizes.len() - j,
        {
            let ghost target_math = bob_sizes[j as int] as int + delta as int;
            let target = bob_sizes[j] as i128 + delta as i128;
            if 1 <= target && target <= 100000 && present[target as usize] {
                let mut answer = Vec::new();
                answer.push(target as i32);
                answer.push(bob_sizes[j]);
                proof {
                    Self::lemma_i128_sum_as_int(bob_sizes@[j as int] as int, delta as int);
                    assert(target as int == target_math);
                    assert(present[target as int]);
                    assert(Self::appears_in(alice_sizes@, target as i32));
                    assert(Self::appears_in(bob_sizes@, bob_sizes[j as int]));
                    assert(delta as int == Self::delta(alice_sizes@, bob_sizes@));
                    assert(target_math == bob_sizes@[j as int] as int + Self::delta(alice_sizes@, bob_sizes@));
                    let sum_a = Self::seq_sum(alice_sizes@, alice_sizes.len() as int);
                    let sum_b = Self::seq_sum(bob_sizes@, bob_sizes.len() as int);
                    let bob_val = bob_sizes@[j as int] as int;
                    assert(2 * (delta as int) == sum_a - sum_b);
                    assert(sum_a - target as int + bob_val == sum_a - target_math + bob_val);
                    assert(sum_b - bob_val + target as int == sum_b - bob_val + target_math);
                    assert(sum_a - target_math + bob_val == sum_b - bob_val + target_math) by (nonlinear_arith)
                        requires
                            target_math == bob_val + delta as int,
                            2 * (delta as int) == sum_a - sum_b,
                    {};
                    assert(
                        Self::seq_sum(alice_sizes@, alice_sizes.len() as int) - target as int + bob_sizes@[j as int] as int
                        == Self::seq_sum(bob_sizes@, bob_sizes.len() as int) - bob_sizes@[j as int] as int + target as int
                    );
                    assert(Self::valid_swap_int(alice_sizes@, bob_sizes@, target as int, bob_sizes@[j as int] as int));
                    assert(Self::valid_swap(alice_sizes@, bob_sizes@, target as i32, bob_sizes@[j as int]));
                }
                return answer;
            }
            proof {
                Self::lemma_i128_sum_as_int(bob_sizes@[j as int] as int, delta as int);
                assert(target as int == target_math);
                assert(delta as int == Self::delta(alice_sizes@, bob_sizes@));
                assert(target_math == bob_sizes@[j as int] as int + Self::delta(alice_sizes@, bob_sizes@));
                assert(!Self::valid_swap_int(alice_sizes@, bob_sizes@, target as int, bob_sizes@[j as int] as int)) by {
                    if Self::valid_swap_int(alice_sizes@, bob_sizes@, target as int, bob_sizes@[j as int] as int) {
                        assert(Self::appears_in(alice_sizes@, target as i32));
                        let k = choose |k: int| 0 <= k < alice_sizes.len() && alice_sizes[k] == target as i32;
                        if !(1 <= target && target <= 100000) {
                            assert(false);
                        }
                        assert(1 <= target <= 100_000);
                        assert(present[target as int] == Self::appears_in(alice_sizes@, target as i32));
                        assert(present[target as int]);
                        if !present[target as int] {
                            assert(false);
                        }
                    }
                };
            }
            j = j + 1;
        }

        proof {
            let pair = choose |alice_box: int, bob_box: int| Self::valid_swap_int(alice_sizes@, bob_sizes@, alice_box, bob_box);
            let alice_box = pair.0;
            let bob_box = pair.1;
            Self::valid_swap_has_delta(alice_sizes@, bob_sizes@, alice_box, bob_box);
            let k = choose |k: int| 0 <= k < bob_sizes.len() && bob_sizes[k] == bob_box as i32;
            assert(0 <= k < j);
            assert(bob_sizes[k] as int == bob_box);
            assert(Self::valid_swap_int(alice_sizes@, bob_sizes@, bob_sizes[k] as int + Self::delta(alice_sizes@, bob_sizes@), bob_sizes[k] as int));
            assert(!Self::valid_swap_int(alice_sizes@, bob_sizes@, bob_sizes[k] as int + Self::delta(alice_sizes@, bob_sizes@), bob_sizes[k] as int));
            assert(false);
        }
        Vec::new()
    }
}

}
