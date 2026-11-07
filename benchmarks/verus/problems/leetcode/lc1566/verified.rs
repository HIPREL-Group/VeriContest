use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn elem_match(arr: Seq<i32>, start: int, m: int, i: int) -> bool {
    arr[start + i] == arr[start + m + i]
}

pub open spec fn has_pattern(arr: Seq<i32>, start: int, m: int, k: int) -> bool {
    forall |i: int| 0 <= i < (k - 1) * m ==> #[trigger] elem_match(arr, start, m, i)
}

proof fn lemma_no_pattern_from_mismatch(arr: Seq<i32>, s: int, m: int, k: int, witness: int)
    requires
        0 <= witness < (k - 1) * m,
        !elem_match(arr, s, m, witness),
    ensures
        !has_pattern(arr, s, m, k),
{
}

impl Solution {
    pub fn contains_pattern(arr: Vec<i32>, m: i32, k: i32) -> (res: bool)
        requires
            2 <= arr.len() <= 100,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
            1 <= m <= 100,
            2 <= k <= 100,
        ensures
            res == exists |start: int| 0 <= start && start + (k as int) * (m as int) <= arr.len() && has_pattern(arr@, start, m as int, k as int),
    {
        let n = arr.len();
        let mu = m as usize;
        let ku = k as usize;

        proof {
            assert(mu as int * ku as int <= 10000) by(nonlinear_arith)
                requires mu as int <= 100, ku as int <= 100;
            assert((ku as int - 1) * mu as int <= 9900) by(nonlinear_arith)
                requires ku as int <= 100, mu as int <= 100;
            assert((ku as int - 1) * mu as int >= 1) by(nonlinear_arith)
                requires ku as int >= 2, mu as int >= 1;
        }

        let mk = mu * ku;
        if mk > n {
            return false;
        }

        let target = (ku - 1) * mu;
        let mut consecutive: usize = 0;
        let mut pos: usize = mu;

        proof {
            assert(mu <= n) by(nonlinear_arith)
                requires mk <= n, mk == mu * ku, ku >= 2, mu >= 1;
            assert forall |s: int| 0 <= s && s + (k as int) * (m as int) <= mu as int implies
                !has_pattern(arr@, s, m as int, k as int)
            by {
                assert(false) by(nonlinear_arith)
                    requires s >= 0, s + (k as int) * (m as int) <= mu as int,
                             mu as int == m as int, k as int >= 2, m as int >= 1;
            }
        }

        while pos < n
            invariant
                n == arr.len(),
                mu as int == m as int,
                ku as int == k as int,
                mk == mu * ku,
                target == (ku - 1) * mu,
                mk <= n,
                1 <= m <= 100,
                2 <= k <= 100,
                2 <= n <= 100,
                mu >= 1,
                ku >= 2,
                target >= 1,
                pos >= mu,
                pos <= n,
                consecutive <= pos - mu,
                consecutive < target,
                target as int == (k as int - 1) * (m as int),
                mk as int == (k as int) * (m as int),
                forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100,
                forall |j: int| 0 <= j < consecutive as int ==>
                    #[trigger] elem_match(arr@, pos as int - consecutive as int - mu as int, m as int, j),
                (pos as int - consecutive as int > mu as int) ==>
                    arr@[pos as int - consecutive as int - 1] != arr@[pos as int - consecutive as int - 1 - mu as int],
                forall |s: int| 0 <= s && s + (k as int) * (m as int) <= pos as int ==>
                    !has_pattern(arr@, s, m as int, k as int),
            decreases n - pos,
        {
            if arr[pos] == arr[pos - mu] {
                consecutive = consecutive + 1;

                if consecutive >= target {
                    proof {
                        let start = pos as int + 1 - consecutive as int - mu as int;

                        assert forall |j: int| 0 <= j < (k as int - 1) * (m as int) implies
                            #[trigger] elem_match(arr@, start, m as int, j)
                        by {
                            
                            
                            
                            
                            
                            
                            
                            
                            if j < consecutive as int - 1 {
                                assert(elem_match(arr@, start, m as int, j));
                            } else {
                                
                                assert(arr@[pos as int - mu as int] == arr@[pos as int]);
                                assert(start + j + m as int == pos as int);
                                assert(start + j == pos as int - m as int);
                                assert(elem_match(arr@, start, m as int, j));
                            }
                        }
                        assert(has_pattern(arr@, start, m as int, k as int));
                        assert(start >= 0int);
                        assert(start + (k as int) * (m as int) <= n as int) by {
                            assert(target as int + mu as int == mk as int) by(nonlinear_arith)
                                requires
                                    target as int == (ku as int - 1) * mu as int,
                                    mk as int == mu as int * ku as int,
                                    ku as int >= 2,
                                    mu as int >= 1;
                        }
                    }
                    return true;
                }

                proof {
                    
                    assert forall |s: int| 0 <= s && s + (k as int) * (m as int) <= pos as int + 1 implies
                        !has_pattern(arr@, s, m as int, k as int)
                    by {
                        if s + (k as int) * (m as int) <= pos as int {
                            assert(!has_pattern(arr@, s, m as int, k as int));
                        } else {
                            
                            
                            
                            
                            let witness: int = target as int - 1 - consecutive as int;
                            
                            
                            
                            
                            
                            
                            
                            assert(pos as int - consecutive as int >= mu as int) by(nonlinear_arith)
                                requires
                                    s >= 0,
                                    s + mk as int == pos as int + 1,
                                    mk as int == (k as int) * (m as int),
                                    consecutive as int + 1 <= target as int,
                                    target as int == (k as int - 1) * (m as int),
                                    mu as int == m as int,
                                    m as int >= 1,
                                    k as int >= 2;
                            assert(pos as int - consecutive as int + 1 > mu as int);
                            
                            
                            
                            
                            assert(arr@[pos as int - consecutive as int] != arr@[pos as int - consecutive as int - mu as int]);
                            
                            
                            assert(s + m as int + witness == pos as int - consecutive as int) by(nonlinear_arith)
                                requires
                                    s + mk as int == pos as int + 1,
                                    mk as int == (k as int) * (m as int),
                                    witness == target as int - 1 - consecutive as int,
                                    target as int == (k as int - 1) * (m as int),
                                    mu as int == m as int;
                            assert(s + witness == pos as int - consecutive as int - m as int) by(nonlinear_arith)
                                requires
                                    s + m as int + witness == pos as int - consecutive as int;
                            assert(!elem_match(arr@, s, m as int, witness));
                            lemma_no_pattern_from_mismatch(arr@, s, m as int, k as int, witness);
                        }
                    }
                }
            } else {
                proof {
                    
                    assert forall |s: int| 0 <= s && s + (k as int) * (m as int) <= pos as int + 1 implies
                        !has_pattern(arr@, s, m as int, k as int)
                    by {
                        if s + (k as int) * (m as int) <= pos as int {
                            assert(!has_pattern(arr@, s, m as int, k as int));
                        } else {
                            
                            
                            
                            let witness: int = target as int - 1;
                            assert(s + m as int + witness == pos as int) by(nonlinear_arith)
                                requires
                                    s + mk as int == pos as int + 1,
                                    mk as int == (k as int) * (m as int),
                                    witness == target as int - 1,
                                    target as int == (k as int - 1) * (m as int);
                            assert(s + witness == pos as int - m as int);
                            assert(arr@[pos as int] != arr@[pos as int - mu as int]);
                            assert(!elem_match(arr@, s, m as int, witness));
                            lemma_no_pattern_from_mismatch(arr@, s, m as int, k as int, witness);
                        }
                    }
                }
                consecutive = 0;
            }
            pos = pos + 1;
        }

        proof {
            assert forall |s: int| 0 <= s && s + (k as int) * (m as int) <= arr.len() implies
                !has_pattern(arr@, s, m as int, k as int)
            by {
                assert(!has_pattern(arr@, s, m as int, k as int));
            }
        }
        false
    }
}

}