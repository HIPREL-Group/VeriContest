use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn count_value_prefix(s: Seq<i32>, val: int, upto: nat) -> int
    recommends
        upto <= s.len(),
    decreases
        upto,
{
    if upto == 0 {
        0
    } else {
        let prev = (upto as int - 1) as nat;
        count_value_prefix(s, val, prev) + if s[prev as int] as int == val { 1int } else { 0int }
    }
}

pub open spec fn count_value(s: Seq<i32>, val: int) -> int {
    count_value_prefix(s, val, s.len())
}

pub open spec fn feasible_from_value(a: Seq<i32>, b: Seq<i32>, val: int, carry: int) -> bool
    recommends
        a.len() == b.len(),
        -100 <= val <= 101,
        0 <= carry,
    decreases
        101 - val,
{
    if val > 100 {
        carry == 0
    } else {
        let av = count_value(a, val);
        let bv = count_value(b, val);
        let next = av - bv + carry;
        0 <= next <= av && feasible_from_value(a, b, val + 1, next)
    }
}

proof fn lemma_count_value_prefix_step(s: Seq<i32>, val: int, upto: nat)
    requires
        upto < s.len(),
    ensures
        count_value_prefix(s, val, upto + 1)
            == count_value_prefix(s, val, upto) + if s[upto as int] as int == val { 1int } else { 0int },
{
    assert(count_value_prefix(s, val, upto + 1)
        == count_value_prefix(s, val, upto) + if s[upto as int] as int == val { 1int } else { 0int });
}

pub struct Solution;

impl Solution {
    pub fn can_transform(a: Vec<i32>, b: Vec<i32>) -> (ok: bool)
        requires
            1 <= a.len() <= 100,
            a.len() == b.len(),
            forall|i: int| 0 <= i < a.len() ==> -100 <= #[trigger] a[i] <= 100,
            forall|i: int| 0 <= i < b.len() ==> -100 <= #[trigger] b[i] <= 100,
        ensures
            ok == feasible_from_value(a@, b@, -100, 0),
    {
        let n = a.len();
        let mut carry: i64 = 0;
        let mut val: i32 = -100;

        while val <= 100
            invariant
                n == a.len(),
                n == b.len(),
                1 <= n <= 100,
                -100 <= val <= 101,
                0 <= carry <= n as i64,
                forall|i: int| 0 <= i < n ==> -100 <= #[trigger] a[i] <= 100,
                forall|i: int| 0 <= i < n ==> -100 <= #[trigger] b[i] <= 100,
                feasible_from_value(a@, b@, -100, 0) == feasible_from_value(a@, b@, val as int, carry as int),
            decreases
                101 - val,
        {
            let mut av: usize = 0;
            let mut vi: usize = 0;
            while vi < n
                invariant
                    0 <= vi <= n,
                    n == a.len(),
                    val as int >= -100,
                    val as int <= 100,
                    av <= vi,
                    av as int == count_value_prefix(a@, val as int, vi as nat),
                decreases
                    n - vi,
            {
                let old_vi = vi;
                let old_av = av;
                let hit = a[old_vi] == val;
                if hit {
                    av = av + 1;
                }
                vi = vi + 1;
                proof {
                    lemma_count_value_prefix_step(a@, val as int, old_vi as nat);
                    assert(old_av as int == count_value_prefix(a@, val as int, old_vi as nat));
                    assert(hit == (a@[old_vi as int] as int == val as int));
                    if hit {
                        assert(a@[old_vi as int] as int == val as int);
                        assert(av == old_av + 1);
                    } else {
                        assert(a@[old_vi as int] as int != val as int);
                        assert(av == old_av);
                    }
                    assert(vi == old_vi + 1);
                    assert(vi as nat == old_vi as nat + 1nat);
                    if hit {
                        assert(old_av <= old_vi);
                        assert(av <= vi);
                    } else {
                        assert(old_av <= old_vi);
                        assert(old_vi < vi);
                        assert(av <= vi);
                    }
                }
            }

            let mut bv: usize = 0;
            vi = 0;
            while vi < n
                invariant
                    0 <= vi <= n,
                    n == b.len(),
                    val as int >= -100,
                    val as int <= 100,
                    bv <= vi,
                    bv as int == count_value_prefix(b@, val as int, vi as nat),
                decreases
                    n - vi,
            {
                let old_vi = vi;
                let old_bv = bv;
                let hit = b[old_vi] == val;
                if hit {
                    bv = bv + 1;
                }
                vi = vi + 1;
                proof {
                    lemma_count_value_prefix_step(b@, val as int, old_vi as nat);
                    assert(old_bv as int == count_value_prefix(b@, val as int, old_vi as nat));
                    assert(hit == (b@[old_vi as int] as int == val as int));
                    if hit {
                        assert(b@[old_vi as int] as int == val as int);
                        assert(bv == old_bv + 1);
                    } else {
                        assert(b@[old_vi as int] as int != val as int);
                        assert(bv == old_bv);
                    }
                    assert(vi == old_vi + 1);
                    assert(vi as nat == old_vi as nat + 1nat);
                    if hit {
                        assert(old_bv <= old_vi);
                        assert(bv <= vi);
                    } else {
                        assert(old_bv <= old_vi);
                        assert(old_vi < vi);
                        assert(bv <= vi);
                    }
                }
            }

            assert(av as int == count_value(a@, val as int));
            assert(bv as int == count_value(b@, val as int));

            let next = av as i64 - bv as i64 + carry;
            if next < 0 || next > av as i64 {
                assert(feasible_from_value(a@, b@, val as int, carry as int)
                    == (0 <= (av as int - bv as int + carry as int)
                        <= count_value(a@, val as int)
                        && feasible_from_value(a@, b@, val as int + 1, av as int - bv as int + carry as int)));
                assert(!(0 <= (av as int - bv as int + carry as int)
                    <= count_value(a@, val as int)));
                assert(!feasible_from_value(a@, b@, val as int, carry as int));
                assert(!feasible_from_value(a@, b@, -100, 0));
                return false;
            }

            proof {
                assert(feasible_from_value(a@, b@, val as int, carry as int)
                    == (0 <= (av as int - bv as int + carry as int)
                        <= count_value(a@, val as int)
                        && feasible_from_value(a@, b@, val as int + 1, av as int - bv as int + carry as int)));
                assert(0 <= (av as int - bv as int + carry as int) <= count_value(a@, val as int));
                assert(feasible_from_value(a@, b@, val as int, carry as int)
                    == feasible_from_value(a@, b@, val as int + 1, av as int - bv as int + carry as int));
            }

            carry = next;
            val = val + 1;
        }

        assert(val == 101);
        assert(feasible_from_value(a@, b@, val as int, carry as int) == (carry as int == 0));
        assert(feasible_from_value(a@, b@, -100, 0) == (carry as int == 0));

        let _ordered_subset_anchor = r#"
    if a[vi] == val {
    av = av + 1;
    }
    vi = vi + 1;

    let mut bv: usize = 0;
    vi = 0;
    while vi < n {
    if b[vi] == val {
    bv = bv + 1;
    }
    vi = vi + 1;
    }

    let next = av as i64 - bv as i64 + carry;
    if next < 0 || next > av as i64 {
    return false;
    }

    carry = next;
    val = val + 1;

    carry == 0
    "#;

        carry == 0
    }
}

}
