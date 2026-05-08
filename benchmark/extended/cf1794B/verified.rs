use vstd::prelude::*;

fn main() {}

verus! {

pub open spec fn seq_elements_positive(s: Seq<i32>) -> bool {
    forall|i: int|
        #![trigger s[i]]
        0 <= i && i < s.len() ==> s[i] >= 1 && s[i] <= 1_000_000_000
}

pub open spec fn seq_neighbors_not_dividing(s: Seq<i32>) -> bool {
    forall|i: int|
        #![trigger s[i]]
        0 <= i && i < s.len() - 1 ==> s[i] >= 1 && s[i + 1] >= 1 && (s[i + 1] as int) % (s[i] as int) != 0
}

pub open spec fn seq_pointwise_ge(orig: Seq<i32>, res: Seq<i32>) -> bool {
    orig.len() == res.len()
        && (forall|i: int|
            #![trigger res[i]]
            0 <= i && i < orig.len() ==> res[i] >= orig[i])
}

pub open spec fn seq_increase_per_index_bounded(orig: Seq<i32>, res: Seq<i32>) -> bool {
    orig.len() == res.len()
        && (forall|i: int|
            #![trigger res[i]]
            0 <= i && i < orig.len() ==> (res[i] as int) - (orig[i] as int) <= 2)
}

proof fn lemma_i32_mod_nonneg(a: i32, b: i32)
    requires
        a >= 0,
        b > 0,
    ensures
        (a % b) as int == (a as int) % (b as int),
{
}

proof fn lemma_divisible_plus_one_not_divisible(x: i32, y: i32)
    requires
        x >= 2,
        y >= 2,
        x % y == 0,
    ensures
        ((x + 1) as int) % (y as int) != 0,
{
    lemma_i32_mod_nonneg(x, y);
    assert((x as int) % (y as int) == 0);
    assert(((x + 1) as int) % (y as int) != 0) by(nonlinear_arith)
        requires
            x >= 2,
            y >= 2,
            (x as int) % (y as int) == 0;
}

pub struct Solution;

impl Solution {
    pub fn not_dividing_array(a: Vec<i32>) -> (res: Vec<i32>)
        requires
            1 <= a.len() <= 10000,
            seq_elements_positive(a@),
        ensures
            res@.len() == a@.len(),
            seq_neighbors_not_dividing(res@),
            seq_pointwise_ge(a@, res@),
            seq_increase_per_index_bounded(a@, res@),
    {
        let n = a.len();
        let ghost old_a = a@;
        let mut v = a;
        let mut i: usize = 0;
        while i < n
            invariant
                v.len() == n,
                old_a.len() == n as int,
                seq_elements_positive(old_a),
                i <= n,
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < n as int ==> v@[k] >= old_a[k],
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < i ==> v@[k] >= 2,
                forall|k: int|
                    #![trigger v@[k]]
                    i <= k && k < n as int ==> v@[k] == old_a[k],
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < i ==> v@[k] as int - old_a[k] as int <= 1,
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < n as int ==> v@[k] <= 1_000_000_000,
            decreases n - i,
        {
            if v[i] == 1 {
                proof {
                    assert(i < n);
                    assert(old_a[i as int] == 1);
                }
                v.set(i, 2);
                proof {
                    assert(v@[i as int] == 2);
                    assert(v@[i as int] as int - old_a[i as int] as int == 1);
                }
            } else {
                proof {
                    assert(v@[i as int] == old_a[i as int]);
                    assert(old_a[i as int] != 1);
                    assert(old_a[i as int] >= 1);
                    assert(old_a[i as int] >= 2);
                    assert(v@[i as int] >= 2);
                    assert(v@[i as int] as int - old_a[i as int] as int == 0);
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(forall|k: int|
                #![trigger v@[k]]
                0 <= k && k < n as int ==> v@[k] >= 2);
            assert(forall|k: int|
                #![trigger v@[k]]
                0 <= k && k < n as int ==> v@[k] as int - old_a[k] as int <= 1);
            assert(forall|k: int|
                #![trigger v@[k]]
                0 <= k && k < n as int ==> v@[k] <= 1_000_000_000);
        }
        let ghost v_mid = v@;
        proof {
            assert(forall|k: int|
                #![trigger v_mid[k]]
                0 <= k && k < n as int ==> v_mid[k] <= 1_000_000_000);
        }
        let mut j: usize = 0;
        while j + 1 < n
            invariant
                v.len() == n,
                old_a.len() == n as int,
                v_mid.len() == n as int,
                seq_elements_positive(old_a),
                j < n,
                forall|k: int|
                    #![trigger v_mid[k]]
                    0 <= k && k < n as int ==> v_mid[k] <= 1_000_000_000,
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < n as int ==> v@[k] >= old_a[k],
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < n as int ==> v@[k] >= 2,
                forall|k: int|
                    #![trigger v@[k]]
                    (j as int) < k && k < n as int ==> v@[k] == v_mid[k],
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < n as int ==> v@[k] as int - v_mid[k] as int <= 1,
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < n as int ==> v@[k] >= v_mid[k],
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < n as int ==> v@[k] <= 1_000_000_001,
                forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < j as int ==> (v@[k + 1] as int) % (v@[k] as int) != 0,
            decreases n - j,
        {
            proof {
                assert((j as int) + 1 < n as int);
            }
            let vj = v[j];
            let vj1 = v[j + 1];
            if vj1 % vj == 0 {
                proof {
                    assert((j as int) + 1 < n as int);
                    assert(v@[(j + 1) as int] == v_mid[(j + 1) as int]);
                    assert(v_mid[(j + 1) as int] <= 1_000_000_000);
                    assert(vj1 <= 1_000_000_000);
                    assert(vj1 + 1 <= 1_000_000_001);
                    assert(v@[j as int] >= 2);
                    assert(v@[(j + 1) as int] >= 2);
                    lemma_divisible_plus_one_not_divisible(vj1, vj);
                }
                let vj1_next: i32 = vj1 + 1;
                v.set(j + 1, vj1_next);
                proof {
                    lemma_i32_mod_nonneg(vj1_next, vj);
                    assert(vj1_next >= 0);
                    assert(v@[(j + 1) as int] == vj1_next);
                    assert((v@[(j + 1) as int] as int) % (v@[j as int] as int) != 0);
                }
            } else {
                proof {
                    assert((v@[(j + 1) as int] as int) % (v@[j as int] as int) != 0);
                }
            }
            proof {
                assert(forall|k: int|
                    #![trigger v@[k]]
                    0 <= k && k < (j + 1) as int ==> (v@[k + 1] as int) % (v@[k] as int) != 0);
            }
            j = j + 1;
        }
        proof {
            assert(n >= 1);
            assert(j + 1 >= n);
            assert(j == n - 1);
            assert(forall|k: int|
                #![trigger v@[k]]
                0 <= k && k < n as int - 1 ==> (v@[k + 1] as int) % (v@[k] as int) != 0);
            assert(seq_neighbors_not_dividing(v@));
            assert(forall|k: int|
                #![trigger v@[k]]
                0 <= k && k < n as int ==> v@[k] >= old_a[k]);
            assert(seq_pointwise_ge(old_a, v@));
            assert(forall|k: int|
                #![trigger v@[k]]
                0 <= k && k < n as int ==> v@[k] as int - old_a[k] as int <= 2);
            assert(seq_increase_per_index_bounded(old_a, v@));
        }
        v
    }
}

}
