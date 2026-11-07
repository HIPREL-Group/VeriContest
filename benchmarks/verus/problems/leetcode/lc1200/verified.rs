use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn abs_diff(a: int, b: int) -> int {
    if a >= b { a - b } else { b - a }
}

pub open spec fn seq_contains(s: Seq<i32>, v: i32) -> bool {
    exists |i: int| 0 <= i < s.len() && s[i] == v
}

pub open spec fn consec_diff(s: Seq<i32>, k: int) -> int
    recommends 0 <= k < s.len() - 1,
{
    s[k + 1] - s[k]
}

pub open spec fn has_pair(res: Seq<Vec<i32>>, a: i32, b: i32) -> bool {
    exists |k: int| 0 <= k < res.len() && res[k][0] == a && res[k][1] == b
}

impl Solution {
    pub fn minimum_abs_difference(arr: Vec<i32>) -> (res: Vec<Vec<i32>>)
        requires
            2 <= arr.len() <= 100_000,
            forall |i: int| 0 <= i < arr.len() ==> -1_000_000 <= #[trigger] arr[i] <= 1_000_000,
            forall |i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] != arr[j],
        ensures
            res.len() >= 1,
            forall |i: int| 0 <= i < res.len() ==> (#[trigger] res[i]).len() == 2,
            forall |i: int| 0 <= i < res.len() ==> (#[trigger] res[i])[0] < res[i][1],
            forall |i: int| 0 <= i < res.len() ==>
                #[trigger] seq_contains(arr@, res[i][0]),
            forall |i: int| 0 <= i < res.len() ==>
                #[trigger] seq_contains(arr@, res[i][1]),
            forall |i: int| 0 <= i < res.len() ==>
                ((#[trigger] res[i])[1] - res[i][0]) == (res[0][1] - res[0][0]),
            forall |p: int, q: int| 0 <= p < q < arr.len() ==>
                #[trigger] abs_diff(arr[p] as int, arr[q] as int) >= (res[0][1] - res[0][0]) as int,
            forall |i: int, j: int| 0 <= i < j < res.len() ==>
                (#[trigger] res[i])[0] < (#[trigger] res[j])[0],
            forall |p: int, q: int| 0 <= p < arr.len() && 0 <= q < arr.len()
                && arr[p] < arr[q]
                && #[trigger] abs_diff(arr[p] as int, arr[q] as int) == (res[0][1] - res[0][0]) as int
                ==> has_pair(res@, arr[p], arr[q]),
    {
        let ghost original_arr = arr@;
        let n = arr.len();
        let mut sorted = arr;

        let mut i: usize = 1;
        while i < n
            invariant
                n == sorted.len(),
                2 <= n <= 100_000,
                1 <= i <= n,
                forall |a: int, b: int| 0 <= a < b < i as int ==> sorted[a] < sorted[b],
                forall |a: int, b: int| 0 <= a < b < n as int ==> sorted[a] != sorted[b],
                forall |k: int| 0 <= k < n as int ==> -1_000_000 <= #[trigger] sorted[k] <= 1_000_000,
                forall |k: int| 0 <= k < n as int ==>
                    #[trigger] seq_contains(original_arr, sorted[k]),
                forall |k: int| 0 <= k < n as int ==>
                    seq_contains(sorted@, #[trigger] original_arr[k]),
            decreases n - i,
        {
            let key = sorted[i];
            let ghost pre_inner = sorted@;

            proof {
                assert(forall |a: int, b: int| 0 <= a < b < i as int ==> pre_inner[a] < pre_inner[b]);
                assert(forall |a: int, b: int| 0 <= a < b < n as int ==> pre_inner[a] != pre_inner[b]);
            }

            let mut j = i;
            while j > 0 && sorted[j - 1] > key
                invariant
                    n == sorted.len(),
                    2 <= n <= 100_000,
                    0 <= j <= i,
                    i < n,
                    pre_inner.len() == n as int,
                    key == pre_inner[i as int],
                    -1_000_000 <= key <= 1_000_000,
                    forall |a: int, b: int| 0 <= a < b < i as int ==> pre_inner[a] < pre_inner[b],
                    forall |a: int, b: int| 0 <= a < b < n as int ==> pre_inner[a] != pre_inner[b],
                    forall |k: int| 0 <= k < j as int ==> sorted[k] == pre_inner[k],
                    forall |k: int| k > j as int ==> k <= i as int ==> sorted[k] == pre_inner[k - 1],
                    forall |k: int| k > i as int ==> k < n as int ==> sorted[k] == pre_inner[k],
                    j < i ==> sorted[j as int + 1] > key,
                    forall |k: int| 0 <= k < n as int ==> -1_000_000 <= #[trigger] sorted[k] <= 1_000_000,
                decreases j,
            {
                sorted.set(j, sorted[j - 1]);
                j = j - 1;
            }
            sorted.set(j, key);

            proof {
                
                assert forall |a: int, b: int| 0 <= a < b < i as int + 1 implies sorted[a] < sorted[b] by {
                    if a < j as int && b < j as int {
                        assert(sorted[a] == pre_inner[a]);
                        assert(sorted[b] == pre_inner[b]);
                    } else if a < j as int && b == j as int {
                        assert(sorted[a] == pre_inner[a]);
                        assert(sorted[b] == key);
                        if j as int > 0 {
                            assert(pre_inner[j as int - 1] != pre_inner[i as int]);
                            assert(pre_inner[a] <= pre_inner[j as int - 1]);
                            assert(pre_inner[j as int - 1] < key);
                        }
                    } else if a == j as int && b > j as int {
                        assert(sorted[a] == key);
                        if j < i {
                            
                            assert(sorted[j as int + 1] > key);
                            
                            if b > j as int + 1 {
                                assert(sorted[j as int + 1] == pre_inner[j as int]);
                                assert(sorted[b] == pre_inner[b - 1]);
                                assert(pre_inner[j as int] < pre_inner[b - 1]);
                                assert(sorted[b] > key);
                            }
                        }
                    } else if a > j as int && b > j as int {
                        assert(sorted[a] == pre_inner[a - 1]);
                        assert(sorted[b] == pre_inner[b - 1]);
                        assert(a - 1 < b - 1);
                        assert(pre_inner[a - 1] < pre_inner[b - 1]);
                    } else if a < j as int && b > j as int {
                        assert(sorted[a] == pre_inner[a]);
                        if j as int > 0 {
                            assert(pre_inner[j as int - 1] != pre_inner[i as int]);
                            assert(pre_inner[a] <= pre_inner[j as int - 1]);
                            assert(pre_inner[j as int - 1] < key);
                        }
                        assert(sorted[a] < key);
                        assert(sorted[j as int + 1] > key);
                        if b > j as int + 1 {
                            assert(sorted[j as int + 1] == pre_inner[j as int]);
                            assert(sorted[b] == pre_inner[b - 1]);
                            assert(pre_inner[j as int] < pre_inner[b - 1]);
                        }
                    }
                };

                
                assert forall |a: int, b: int| 0 <= a < b < n as int implies sorted[a] != sorted[b] by {
                    if a <= i as int && b <= i as int {
                        
                        if a < i as int + 1 && b < i as int + 1 {
                            assert(sorted[a] < sorted[b]);
                        } else {
                            
                            
                            
                            if a < j as int {
                                assert(sorted[a] == pre_inner[a]);
                                assert(sorted[b] == pre_inner[b]);
                                assert(pre_inner[a] != pre_inner[b]);
                            } else if a == j as int {
                                assert(sorted[a] == key);
                                assert(sorted[b] == pre_inner[b]);
                                assert(key == pre_inner[i as int]);
                                assert(pre_inner[i as int] != pre_inner[b]);
                            } else {
                                assert(sorted[a] == pre_inner[a - 1]);
                                assert(sorted[b] == pre_inner[b]);
                                assert(a - 1 < b);
                                assert(pre_inner[a - 1] != pre_inner[b]);
                            }
                        }
                    } else if a <= i as int && b > i as int {
                        assert(sorted[b] == pre_inner[b]);
                        if a < j as int {
                            assert(sorted[a] == pre_inner[a]);
                            assert(pre_inner[a] != pre_inner[b]);
                        } else if a == j as int {
                            assert(sorted[a] == key);
                            assert(key == pre_inner[i as int]);
                            assert(pre_inner[i as int] != pre_inner[b]);
                        } else {
                            assert(sorted[a] == pre_inner[a - 1]);
                            assert(a - 1 < b);
                            assert(pre_inner[a - 1] != pre_inner[b]);
                        }
                    } else {
                        
                        assert(sorted[a] == pre_inner[a]);
                        assert(sorted[b] == pre_inner[b]);
                        assert(pre_inner[a] != pre_inner[b]);
                    }
                };

                assert forall |k: int| 0 <= k < n as int implies
                    #[trigger] seq_contains(original_arr, sorted[k]) by {
                    if k < j as int {
                        assert(sorted[k] == pre_inner[k]);
                        assert(seq_contains(original_arr, pre_inner[k]));
                    } else if k == j as int {
                        assert(sorted[k] == key);
                        assert(key == pre_inner[i as int]);
                        assert(seq_contains(original_arr, pre_inner[i as int]));
                    } else if k <= i as int {
                        assert(sorted[k] == pre_inner[k - 1]);
                        assert(seq_contains(original_arr, pre_inner[k - 1]));
                    } else {
                        assert(sorted[k] == pre_inner[k]);
                        assert(seq_contains(original_arr, pre_inner[k]));
                    }
                };

                assert forall |k: int| 0 <= k < n as int implies
                    seq_contains(sorted@, #[trigger] original_arr[k]) by {
                    assert(seq_contains(pre_inner, original_arr[k]));
                    let w = choose |l: int| 0 <= l < n as int && pre_inner[l] == original_arr[k];
                    if w < j as int {
                        assert(sorted[w] == pre_inner[w]);
                    } else if w == i as int {
                        assert(sorted[j as int] == pre_inner[i as int]);
                    } else if w >= j as int && w < i as int {
                        assert(sorted[w + 1] == pre_inner[w]);
                    } else {
                        assert(sorted[w] == pre_inner[w]);
                    }
                };
            }

            i = i + 1;
        }

        let mut min_diff: i32 = sorted[1] - sorted[0];

        proof {
            assert(min_diff > 0) by {
                assert(sorted[0] < sorted[1]);
            };
            assert(consec_diff(sorted@, 0) == min_diff as int);
        }

        let mut i: usize = 2;
        while i < n
            invariant
                2 <= i <= n,
                n == sorted.len(),
                2 <= n <= 100_000,
                forall |a: int, b: int| 0 <= a < b < n as int ==> sorted[a] < sorted[b],
                forall |k: int| 0 <= k < n as int ==> -1_000_000 <= #[trigger] sorted[k] <= 1_000_000,
                min_diff > 0,
                forall |k: int| 0 <= k < i as int - 1 ==>
                    #[trigger] consec_diff(sorted@, k) >= min_diff as int,
                exists |k: int| 0 <= k < i as int - 1 &&
                    consec_diff(sorted@, k) == min_diff as int,
            decreases n - i,
        {
            let diff = sorted[i] - sorted[i - 1];
            proof {
                assert(diff == consec_diff(sorted@, i as int - 1));
            }
            if diff < min_diff {
                min_diff = diff;
                proof {
                    assert(consec_diff(sorted@, i as int - 1) == min_diff as int);
                }
            }
            i = i + 1;
        }

        proof {
            assert forall |p: int, q: int| 0 <= p < q < n as int implies
                abs_diff(sorted[p] as int, sorted[q] as int) >= min_diff as int by {
                assert(sorted[p] < sorted[q]);
                assert(abs_diff(sorted[p] as int, sorted[q] as int) == sorted[q] as int - sorted[p] as int);
                assert(sorted[q] as int - sorted[p] as int >= sorted[p + 1] as int - sorted[p] as int);
                assert(consec_diff(sorted@, p) >= min_diff as int);
            };

            assert forall |p: int, q: int| 0 <= p < q < n as int implies
                #[trigger] abs_diff(original_arr[p] as int, original_arr[q] as int) >= min_diff as int by {
                assert(seq_contains(sorted@, original_arr[p]));
                assert(seq_contains(sorted@, original_arr[q]));
                let lp = choose |l: int| 0 <= l < n as int && sorted@[l] == original_arr[p];
                let lq = choose |l: int| 0 <= l < n as int && sorted@[l] == original_arr[q];
                if lp == lq {
                    assert(original_arr[p] == original_arr[q]);
                    assert(p != q);
                    assert(original_arr[p] != original_arr[q]);
                } else if lp < lq {
                    assert(abs_diff(sorted[lp] as int, sorted[lq] as int) >= min_diff as int);
                } else {
                    assert(abs_diff(sorted[lq] as int, sorted[lp] as int) >= min_diff as int);
                }
            };
        }

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 1;
        while i < n
            invariant
                1 <= i <= n,
                n == sorted.len(),
                2 <= n <= 100_000,
                min_diff > 0,
                forall |a: int, b: int| 0 <= a < b < n as int ==> sorted[a] < sorted[b],
                forall |k: int| 0 <= k < n as int ==> -1_000_000 <= #[trigger] sorted[k] <= 1_000_000,
                forall |k: int| 0 <= k < n as int - 1 ==>
                    #[trigger] consec_diff(sorted@, k) >= min_diff as int,
                exists |k: int| 0 <= k < n as int - 1 &&
                    consec_diff(sorted@, k) == min_diff as int,
                forall |k: int| 0 <= k < n as int ==>
                    #[trigger] seq_contains(original_arr, sorted[k]),
                forall |k: int| 0 <= k < result.len() ==> (#[trigger] result[k]).len() == 2,
                forall |k: int| 0 <= k < result.len() ==> (#[trigger] result[k])[0] < result[k][1],
                forall |k: int| 0 <= k < result.len() ==>
                    ((#[trigger] result[k])[1] - result[k][0]) == min_diff,
                forall |k: int| 0 <= k < result.len() ==>
                    #[trigger] seq_contains(original_arr, result[k][0]),
                forall |k: int| 0 <= k < result.len() ==>
                    #[trigger] seq_contains(original_arr, result[k][1]),
                forall |k: int, l: int| 0 <= k < l < result.len() ==>
                    (#[trigger] result[k])[0] < (#[trigger] result[l])[0],
                
                (exists |k: int| 0 <= k < i as int - 1 && consec_diff(sorted@, k) == min_diff as int) ==> result.len() > 0,
                
                result.len() > 0 ==> result[result.len() - 1 as int][0] < sorted[i as int - 1],
                forall |k: int| 0 <= k < n as int ==>
                    seq_contains(sorted@, #[trigger] original_arr[k]),
                forall |kk: int| 0 <= kk < i as int - 1 ==>
                    consec_diff(sorted@, kk) == min_diff as int ==>
                    has_pair(result@, sorted[kk], sorted[kk + 1]),
            decreases n - i,
        {
            if sorted[i] - sorted[i - 1] == min_diff {
                let ghost old_result_len = result.len();
                let ghost old_result_seq = result@;

                proof {
                    assert(consec_diff(sorted@, i as int - 1) == min_diff as int);
                }

                let pair: Vec<i32> = vec![sorted[i - 1], sorted[i]];
                result.push(pair);

                proof {
                    assert(result[old_result_len as int][0] == sorted[i as int - 1]);
                    assert(result[old_result_len as int][1] == sorted[i as int]);
                    assert(result.len() == old_result_len + 1);

                    
                    assert forall |k: int, l: int| 0 <= k < l < result.len() implies
                        (#[trigger] result[k])[0] < (#[trigger] result[l])[0] by {
                        if l < old_result_len as int {
                            
                        } else if k < old_result_len as int {
                            
                            assert(result[l][0] == sorted[i as int - 1]);
                            if old_result_len > 0 {
                                
                                if k < old_result_len as int - 1 {
                                    
                                    assert(result[k][0] < result[old_result_len as int - 1][0]);
                                }
                                
                                assert(result[old_result_len as int - 1][0] < sorted[i as int - 1]);
                            }
                        }
                    };

                    
                    assert forall |k: int| 0 <= k < result.len() implies
                        #[trigger] seq_contains(original_arr, result[k][0]) by {
                        if k < old_result_len as int {
                        } else {
                            assert(result[k][0] == sorted[i as int - 1]);
                            assert(seq_contains(original_arr, sorted[i as int - 1]));
                        }
                    };

                    assert forall |k: int| 0 <= k < result.len() implies
                        #[trigger] seq_contains(original_arr, result[k][1]) by {
                        if k < old_result_len as int {
                        } else {
                            assert(result[k][1] == sorted[i as int]);
                            assert(seq_contains(original_arr, sorted[i as int]));
                        }
                    };

                    
                    assert(result[result.len() - 1 as int][0] == sorted[i as int - 1]);
                    assert(sorted[i as int - 1] < sorted[i as int]);

                    
                    assert forall |kk: int| 0 <= kk < i as int
                        && consec_diff(sorted@, kk) == min_diff as int
                        implies has_pair(result@, sorted[kk], sorted[kk + 1]) by {
                        if kk == i as int - 1 {
                            assert(result@[old_result_len as int][0] == sorted[kk]);
                            assert(result@[old_result_len as int][1] == sorted[kk + 1]);
                        } else if consec_diff(sorted@, kk) == min_diff as int {
                            assert(has_pair(old_result_seq, sorted[kk], sorted[kk + 1]));
                            let w = choose |m: int| 0 <= m < old_result_seq.len()
                                && old_result_seq[m][0] == sorted[kk]
                                && old_result_seq[m][1] == sorted[kk + 1];
                            assert(0 <= w < old_result_len as int);
                            assert(w < result@.len());
                            assert(result@[w] == old_result_seq[w]);
                            assert(result@[w][0] == sorted[kk]);
                            assert(result@[w][1] == sorted[kk + 1]);
                        }
                    };
                }
            } else {
                proof {
                    assert(consec_diff(sorted@, i as int - 1) != min_diff as int) by {
                        assert(sorted[i as int] - sorted[i as int - 1] != min_diff);
                    };
                    
                    if result.len() > 0 {
                        assert(result[result.len() - 1 as int][0] < sorted[i as int - 1]);
                        assert(sorted[i as int - 1] < sorted[i as int]);
                    }
                }
            }
            i = i + 1;
        }

        proof {
            
            
            
            let witness_k = choose |k: int| 0 <= k < n as int - 1 && consec_diff(sorted@, k) == min_diff as int;
            assert(0 <= witness_k < n as int - 1);
            assert(witness_k < i as int - 1);
            assert(consec_diff(sorted@, witness_k) == min_diff as int);
            assert(result.len() > 0);
            assert(result.len() >= 1);

            assert(result[0][1] - result[0][0] == min_diff);

            assert forall |i: int| 0 <= i < result.len() implies
                ((#[trigger] result[i])[1] - result[i][0]) == (result[0][1] - result[0][0]) by {
                assert((result[i][1] - result[i][0]) == min_diff);
            };

            assert forall |p: int, q: int| 0 <= p < q < n as int implies
                #[trigger] abs_diff(original_arr[p] as int, original_arr[q] as int) >= (result[0][1] - result[0][0]) as int by {
                assert(result[0][1] - result[0][0] == min_diff);
            };

            
            assert forall |p: int, q: int| 0 <= p < n as int && 0 <= q < n as int
                && original_arr[p] < original_arr[q]
                && #[trigger] abs_diff(original_arr[p] as int, original_arr[q] as int) == (result[0][1] - result[0][0]) as int
                implies has_pair(result@, original_arr[p], original_arr[q]) by {
                assert(result[0][1] - result[0][0] == min_diff);
                assert(abs_diff(original_arr[p] as int, original_arr[q] as int) == min_diff as int);
                
                assert((original_arr[p] as int) < (original_arr[q] as int));
                assert((original_arr[q] as int) - (original_arr[p] as int) == min_diff as int);

                
                assert(seq_contains(sorted@, original_arr[p]));
                assert(seq_contains(sorted@, original_arr[q]));
                let sp = choose |l: int| 0 <= l < n as int && sorted@[l] == original_arr[p];
                let sq = choose |l: int| 0 <= l < n as int && sorted@[l] == original_arr[q];
                assert(sorted[sp] == original_arr[p]);
                assert(sorted[sq] == original_arr[q]);
                assert(sorted[sp] < sorted[sq]);

                
                if sp >= sq {
                    if sp > sq {
                        assert(sorted[sq] < sorted[sp]); 
                    }
                    assert(false);
                }
                assert(sp < sq);
                assert(sp < n as int - 1);

                
                
                assert(consec_diff(sorted@, sp) >= min_diff as int);
                
                
                assert(sorted[sp + 1] as int - sorted[sp] as int >= min_diff as int);
                assert(sorted[sq] as int - sorted[sp] as int == min_diff as int);
                assert(sorted[sp + 1] as int >= sorted[sq] as int);

                if sq > sp + 1 {
                    
                    assert(sorted[sp + 1] < sorted[sq]);
                    assert(false);
                }
                assert(sq == sp + 1);

                
                assert(consec_diff(sorted@, sp) == min_diff as int);
                assert(has_pair(result@, sorted[sp], sorted[sp + 1]));
            };
        }

        result
    }
}

}
