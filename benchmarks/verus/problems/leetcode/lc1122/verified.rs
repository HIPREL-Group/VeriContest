use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn count(s: Seq<i32>, v: i32) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            0
        } else {
            (if s[0] == v { 1int } else { 0int }) + Self::count(s.subrange(1, s.len() as int), v)
        }
    }

    pub open spec fn index_of(v: i32, s: Seq<i32>) -> int
        decreases s.len()
    {
        if s.len() == 0 {
            -1int
        } else if s[0] == v {
            0int
        } else {
            let r = Self::index_of(v, s.subrange(1, s.len() as int));
            if r == -1 { -1int } else { 1 + r }
        }
    }

    pub open spec fn rank(v: i32, arr2: Seq<i32>) -> int {
        let idx = Self::index_of(v, arr2);
        if idx >= 0 {
            idx
        } else {
            arr2.len() + v as int
        }
    }

    pub open spec fn sum_range(cnt: Seq<i32>, lo: int, hi: int) -> int
        decreases hi - lo
    {
        if lo >= hi { 0 } else { cnt[lo] as int + Self::sum_range(cnt, lo + 1, hi) }
    }

    proof fn count_push(s: Seq<i32>, x: i32, v: i32)
        ensures
            Self::count(s.push(x), v) == Self::count(s, v) + if x == v { 1int } else { 0int }
        decreases s.len()
    {
        if s.len() == 0 {
            assert(Self::count(s, v) == 0);
            assert(s.push(x).len() == 1);
            assert(s.push(x)[0] == x);
            let rest = s.push(x).subrange(1, s.push(x).len() as int);
            assert(rest =~= Seq::<i32>::empty());
            assert(rest.len() == 0);
            assert(Self::count(rest, v) == 0);
        } else {
            let tail = s.subrange(1, s.len() as int);
            Self::count_push(tail, x, v);
            assert(s.push(x).len() > 0);
            assert(s.push(x)[0] == s[0]);
            let rest = s.push(x).subrange(1, s.push(x).len() as int);
            assert(rest =~= tail.push(x));
            assert(Self::count(rest, v) == Self::count(tail.push(x), v));
            assert(Self::count(s, v) == (if s[0] == v { 1int } else { 0int }) + Self::count(tail, v));
        }
    }

    proof fn count_le_len(s: Seq<i32>, v: i32)
        ensures
            Self::count(s, v) <= s.len()
        decreases s.len()
    {
        if s.len() > 0 {
            Self::count_le_len(s.subrange(1, s.len() as int), v);
        }
    }

    proof fn count_zero_not_present(s: Seq<i32>, v: i32)
        requires
            forall |i: int| 0 <= i < s.len() ==> s[i] != v
        ensures
            Self::count(s, v) == 0
        decreases s.len()
    {
        if s.len() > 0 {
            let sub = s.subrange(1, s.len() as int);
            assert forall |i: int| 0 <= i < sub.len() implies sub[i] != v by {
                assert(sub[i] == s[i + 1]);
            };
            Self::count_zero_not_present(sub, v);
        }
    }

    proof fn index_of_self(s: Seq<i32>, k: int)
        requires
            0 <= k < s.len(),
            forall |i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j],
        ensures
            Self::index_of(s[k], s) == k
        decreases k
    {
        if k > 0 {
            let sub = s.subrange(1, s.len() as int);
            assert(sub[k - 1] == s[k]);
            assert forall |i: int, j: int| 0 <= i < j < sub.len() implies sub[i] != sub[j] by {
                assert(sub[i] == s[i + 1]);
                assert(sub[j] == s[j + 1]);
            };
            Self::index_of_self(sub, k - 1);
        }
    }

    proof fn index_of_not_found(v: i32, s: Seq<i32>)
        requires
            forall |k: int| 0 <= k < s.len() ==> s[k] != v,
        ensures
            Self::index_of(v, s) == -1
        decreases s.len()
    {
        if s.len() > 0 {
            let sub = s.subrange(1, s.len() as int);
            assert forall |k: int| 0 <= k < sub.len() implies sub[k] != v by {
                assert(sub[k] == s[k + 1]);
            };
            Self::index_of_not_found(v, sub);
        }
    }

    proof fn index_of_bound(v: i32, s: Seq<i32>)
        ensures
            Self::index_of(v, s) < s.len() as int,
            Self::index_of(v, s) >= -1,
        decreases s.len()
    {
        if s.len() > 0 && s[0] != v {
            Self::index_of_bound(v, s.subrange(1, s.len() as int));
        }
    }

    proof fn sum_range_set(old_s: Seq<i32>, new_s: Seq<i32>, idx: int, lo: int, hi: int)
        requires
            old_s.len() == new_s.len(),
            lo <= idx < hi,
            0 <= lo,
            hi <= old_s.len(),
            forall |k: int| lo <= k < hi && k != idx ==> new_s[k] == old_s[k],
        ensures
            Self::sum_range(new_s, lo, hi)
                == Self::sum_range(old_s, lo, hi) - old_s[idx] as int + new_s[idx] as int
        decreases hi - lo
    {
        if idx == lo {
            if lo + 1 < hi {
                Self::sum_range_same(old_s, new_s, lo + 1, hi);
            }
            assert(Self::sum_range(new_s, lo, hi) == new_s[lo] as int + Self::sum_range(new_s, lo + 1, hi));
            assert(Self::sum_range(old_s, lo, hi) == old_s[lo] as int + Self::sum_range(old_s, lo + 1, hi));
        } else {
            assert(new_s[lo] == old_s[lo]);
            Self::sum_range_set(old_s, new_s, idx, lo + 1, hi);
        }
    }

    proof fn sum_range_same(s1: Seq<i32>, s2: Seq<i32>, lo: int, hi: int)
        requires
            forall |k: int| lo <= k < hi ==> s1[k] == s2[k],
            0 <= lo,
        ensures
            Self::sum_range(s1, lo, hi) == Self::sum_range(s2, lo, hi)
        decreases hi - lo
    {
        if lo < hi {
            Self::sum_range_same(s1, s2, lo + 1, hi);
        }
    }

    proof fn sum_range_all_zero(cnt: Seq<i32>, lo: int, hi: int)
        requires
            0 <= lo,
            hi <= cnt.len(),
            forall |v: int| lo <= v < hi ==> cnt[v] == 0i32,
        ensures
            Self::sum_range(cnt, lo, hi) == 0
        decreases hi - lo
    {
        if lo < hi {
            Self::sum_range_all_zero(cnt, lo + 1, hi);
        }
    }

    pub fn relative_sort_array(arr1: Vec<i32>, arr2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= arr1@.len() <= 1000,
            1 <= arr2@.len() <= 1000,
            forall |i: int| 0 <= i < arr1@.len() ==> 0 <= #[trigger] arr1@[i] <= 1000,
            forall |i: int| 0 <= i < arr2@.len() ==> 0 <= #[trigger] arr2@[i] <= 1000,
            forall |i: int, j: int| 0 <= i < j < arr2@.len() ==> arr2@[i] != arr2@[j],
            forall |i: int| 0 <= i < arr2@.len() ==>
                Self::count(arr1@, arr2@[i]) >= 1,
        ensures
            result@.len() == arr1@.len(),
            forall |v: i32| Self::count(result@, v) == Self::count(arr1@, v),
            
            forall |i: int, j: int| 0 <= i < j < result@.len()
                && Self::index_of(result@[i], arr2@) < 0
                && Self::index_of(result@[j], arr2@) >= 0
                ==> false,
            
            forall |i: int, j: int| 0 <= i < j < result@.len()
                && Self::index_of(result@[i], arr2@) >= 0
                && Self::index_of(result@[j], arr2@) >= 0
                ==> Self::index_of(result@[i], arr2@) <= Self::index_of(result@[j], arr2@),
            
            forall |i: int, j: int| 0 <= i < j < result@.len()
                && Self::index_of(result@[i], arr2@) < 0
                && Self::index_of(result@[j], arr2@) < 0
                ==> result@[i] <= result@[j],
    {
        let mut cnt: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < 1001
            invariant
                cnt@.len() == i as int,
                0 <= i <= 1001,
                forall |v: int| 0 <= v < i as int ==> cnt@[v] == 0i32,
            decreases 1001 - i
        {
            cnt.push(0);
            i = i + 1;
        }

        proof {
            Self::sum_range_all_zero(cnt@, 0, 1001);
        }

        let mut j: usize = 0;
        while j < arr1.len()
            invariant
                cnt@.len() == 1001,
                0 <= j <= arr1@.len(),
                1 <= arr1@.len() <= 1000,
                forall |ii: int| 0 <= ii < arr1@.len() ==> 0 <= #[trigger] arr1@[ii] <= 1000,
                forall |v: int| 0 <= v <= 1000 ==>
                    cnt@[v] as int == Self::count(arr1@.subrange(0, j as int), v as i32),
                forall |v: int| 0 <= v <= 1000 ==> 0 <= #[trigger] cnt@[v],
                forall |v: int| 0 <= v <= 1000 ==> #[trigger] cnt@[v] as int <= j as int,
                Self::sum_range(cnt@, 0, 1001) == j as int,
            decreases arr1@.len() - j
        {
            let v = arr1[j] as usize;
            let ghost old_cnt = cnt@;

            proof {
                let prev = arr1@.subrange(0, j as int);
                Self::count_le_len(prev, v as i32);
                assert(prev.len() == j as int);
                assert(cnt@[v as int] as int <= j as int);
                assert(cnt@[v as int] < 1000);
            }
            cnt.set(v, cnt[v] + 1);

            proof {
                let prev = arr1@.subrange(0, j as int);
                let next = arr1@.subrange(0, j as int + 1);
                assert(next =~= prev.push(arr1@[j as int]));

                assert forall |w: int| 0 <= w <= 1000 implies
                    cnt@[w] as int == Self::count(next, w as i32)
                by {
                    Self::count_push(prev, arr1@[j as int], w as i32);
                };

                assert forall |w: int| 0 <= w <= 1000 implies
                    #[trigger] cnt@[w] as int <= (j + 1) as int
                by {
                    Self::count_le_len(next, w as i32);
                    assert(next.len() == j as int + 1);
                };

                Self::sum_range_set(old_cnt, cnt@, v as int, 0, 1001);
            }

            j = j + 1;
        }

        proof {
            assert(arr1@.subrange(0, arr1@.len() as int) =~= arr1@);
        }

        let mut result: Vec<i32> = Vec::new();
        let mut k: usize = 0;
        while k < arr2.len()
            invariant
                cnt@.len() == 1001,
                0 <= k <= arr2@.len(),
                1 <= arr1@.len() <= 1000,
                1 <= arr2@.len() <= 1000,
                forall |ii: int| 0 <= ii < arr1@.len() ==> 0 <= #[trigger] arr1@[ii] <= 1000,
                forall |ii: int| 0 <= ii < arr2@.len() ==> 0 <= #[trigger] arr2@[ii] <= 1000,
                forall |ii: int, jj: int| 0 <= ii < jj < arr2@.len() ==> arr2@[ii] != arr2@[jj],
                forall |v: int| 0 <= v <= 1000 ==>
                    Self::count(result@, v as i32) + cnt@[v] as int == Self::count(arr1@, v as i32),
                forall |v: int| 0 <= v <= 1000 ==> 0 <= #[trigger] cnt@[v],
                result@.len() as int + Self::sum_range(cnt@, 0, 1001) == arr1@.len() as int,
                forall |jj: int| 0 <= jj < k as int ==> cnt@[arr2@[jj] as int] == 0i32,
                forall |ii: int, jj: int| 0 <= ii < jj < result@.len() ==>
                    Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@),
                forall |ii: int| 0 <= ii < result@.len() ==>
                    Self::rank(result@[ii], arr2@) < k as int,
                forall |ii: int| 0 <= ii < result@.len() ==> 0 <= #[trigger] result@[ii] <= 1000,
            decreases arr2@.len() - k
        {
            let v = arr2[k];

            proof {
                Self::index_of_self(arr2@, k as int);
            }

            while cnt[v as usize] > 0
                invariant
                    cnt@.len() == 1001,
                    0 <= k < arr2@.len(),
                    v == arr2@[k as int],
                    1 <= arr1@.len() <= 1000,
                    1 <= arr2@.len() <= 1000,
                    forall |ii: int| 0 <= ii < arr2@.len() ==> 0 <= #[trigger] arr2@[ii] <= 1000,
                    forall |ii: int, jj: int| 0 <= ii < jj < arr2@.len() ==> arr2@[ii] != arr2@[jj],
                    0 <= v <= 1000,
                    forall |w: int| 0 <= w <= 1000 ==>
                        Self::count(result@, w as i32) + cnt@[w] as int == Self::count(arr1@, w as i32),
                    forall |w: int| 0 <= w <= 1000 ==> 0 <= #[trigger] cnt@[w],
                    result@.len() as int + Self::sum_range(cnt@, 0, 1001) == arr1@.len() as int,
                    forall |jj: int| 0 <= jj < k as int ==> cnt@[arr2@[jj] as int] == 0i32,
                    forall |ii: int, jj: int| 0 <= ii < jj < result@.len() ==>
                        Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@),
                    forall |ii: int| 0 <= ii < result@.len() ==>
                        Self::rank(result@[ii], arr2@) <= k as int,
                    forall |ii: int| 0 <= ii < result@.len() ==> 0 <= #[trigger] result@[ii] <= 1000,
                    Self::index_of(arr2@[k as int], arr2@) == k as int,
                decreases cnt@[v as int] as int
            {
                let ghost old_result = result@;
                let ghost old_cnt = cnt@;
                result.push(v);
                cnt.set(v as usize, cnt[v as usize] - 1);

                proof {
                    assert forall |w: int| 0 <= w <= 1000 implies
                        Self::count(result@, w as i32) + cnt@[w] as int == Self::count(arr1@, w as i32)
                    by {
                        Self::count_push(old_result, v, w as i32);
                    };

                    Self::sum_range_set(old_cnt, cnt@, v as int, 0, 1001);

                    assert(Self::rank(v, arr2@) == k as int);

                    assert forall |jj: int| 0 <= jj < k as int implies
                        cnt@[arr2@[jj] as int] == 0i32
                    by {
                        assert(arr2@[jj] != arr2@[k as int]);
                    };

                    assert forall |ii: int, jj: int| 0 <= ii < jj < result@.len() implies
                        Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@)
                    by {
                        if jj < old_result.len() as int {
                            assert(result@[ii] == old_result[ii]);
                            assert(result@[jj] == old_result[jj]);
                        } else {
                            if ii < old_result.len() as int {
                                assert(result@[ii] == old_result[ii]);
                                assert(Self::rank(result@[ii], arr2@) <= k as int);
                            }
                            assert(result@[jj] == v);
                        }
                    };

                    assert forall |ii: int| 0 <= ii < result@.len() implies
                        Self::rank(result@[ii], arr2@) <= k as int
                    by {
                        if ii < old_result.len() as int {
                            assert(result@[ii] == old_result[ii]);
                        } else {
                            assert(result@[ii] == v);
                        }
                    };
                }
            }

            proof {
                assert forall |ii: int| 0 <= ii < result@.len() implies
                    Self::rank(result@[ii], arr2@) < (k + 1) as int
                by {};

                assert forall |jj: int| 0 <= jj < (k + 1) as int implies
                    cnt@[arr2@[jj] as int] == 0i32
                by {
                    if jj < k as int {
                    } else {
                        assert(jj == k as int);
                        assert(v == arr2@[k as int]);
                    }
                };
            }

            k = k + 1;
        }

        let mut m: usize = 0;
        while m < 1001
            invariant
                cnt@.len() == 1001,
                0 <= m <= 1001,
                1 <= arr1@.len() <= 1000,
                1 <= arr2@.len() <= 1000,
                forall |ii: int| 0 <= ii < arr2@.len() ==> 0 <= #[trigger] arr2@[ii] <= 1000,
                forall |ii: int, jj: int| 0 <= ii < jj < arr2@.len() ==> arr2@[ii] != arr2@[jj],
                forall |w: int| 0 <= w <= 1000 ==>
                    Self::count(result@, w as i32) + cnt@[w] as int == Self::count(arr1@, w as i32),
                forall |w: int| 0 <= w <= 1000 ==> 0 <= #[trigger] cnt@[w],
                result@.len() as int + Self::sum_range(cnt@, 0, 1001) == arr1@.len() as int,
                forall |jj: int| 0 <= jj < arr2@.len() ==> cnt@[arr2@[jj] as int] == 0i32,
                forall |v: int| 0 <= v < m as int ==> cnt@[v] == 0i32,
                forall |ii: int, jj: int| 0 <= ii < jj < result@.len() ==>
                    Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@),
                forall |ii: int| 0 <= ii < result@.len() ==>
                    Self::rank(result@[ii], arr2@) < arr2@.len() + m as int,
                forall |ii: int| 0 <= ii < result@.len() ==> 0 <= #[trigger] result@[ii] <= 1000,
            decreases 1001 - m
        {
            while cnt[m] > 0
                invariant
                    cnt@.len() == 1001,
                    0 <= m <= 1000,
                    1 <= arr2@.len() <= 1000,
                    forall |ii: int| 0 <= ii < arr2@.len() ==> 0 <= #[trigger] arr2@[ii] <= 1000,
                    forall |ii: int, jj: int| 0 <= ii < jj < arr2@.len() ==> arr2@[ii] != arr2@[jj],
                    forall |w: int| 0 <= w <= 1000 ==>
                        Self::count(result@, w as i32) + cnt@[w] as int == Self::count(arr1@, w as i32),
                    forall |w: int| 0 <= w <= 1000 ==> 0 <= #[trigger] cnt@[w],
                    result@.len() as int + Self::sum_range(cnt@, 0, 1001) == arr1@.len() as int,
                    forall |jj: int| 0 <= jj < arr2@.len() ==> cnt@[arr2@[jj] as int] == 0i32,
                    forall |v: int| 0 <= v < m as int ==> cnt@[v] == 0i32,
                    forall |ii: int, jj: int| 0 <= ii < jj < result@.len() ==>
                        Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@),
                    forall |ii: int| 0 <= ii < result@.len() ==>
                        Self::rank(result@[ii], arr2@) <= arr2@.len() + m as int,
                    forall |ii: int| 0 <= ii < result@.len() ==> 0 <= #[trigger] result@[ii] <= 1000,
                decreases cnt@[m as int] as int
            {
                let ghost old_result = result@;
                let ghost old_cnt = cnt@;
                result.push(m as i32);
                cnt.set(m, cnt[m] - 1);

                proof {
                    assert forall |jj: int| 0 <= jj < arr2@.len() implies arr2@[jj] != m as i32 by {
                        if arr2@[jj] == m as i32 {
                            assert(old_cnt[arr2@[jj] as int] == 0i32);
                            assert(old_cnt[m as int] == 0i32);
                        }
                    };
                    Self::index_of_not_found(m as i32, arr2@);
                    assert(Self::rank(m as i32, arr2@) == arr2@.len() + m as int);

                    assert forall |w: int| 0 <= w <= 1000 implies
                        Self::count(result@, w as i32) + cnt@[w] as int == Self::count(arr1@, w as i32)
                    by {
                        Self::count_push(old_result, m as i32, w as i32);
                    };

                    Self::sum_range_set(old_cnt, cnt@, m as int, 0, 1001);

                    assert forall |jj: int| 0 <= jj < arr2@.len() implies
                        cnt@[arr2@[jj] as int] == 0i32
                    by {
                        assert(arr2@[jj] != m as i32);
                    };

                    assert forall |v: int| 0 <= v < m as int implies cnt@[v] == 0i32
                    by {};

                    assert forall |ii: int, jj: int| 0 <= ii < jj < result@.len() implies
                        Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@)
                    by {
                        if jj < old_result.len() as int {
                            assert(result@[ii] == old_result[ii]);
                            assert(result@[jj] == old_result[jj]);
                        } else {
                            if ii < old_result.len() as int {
                                assert(result@[ii] == old_result[ii]);
                                assert(Self::rank(result@[ii], arr2@) <= arr2@.len() + m as int);
                            }
                            assert(result@[jj] == m as i32);
                        }
                    };

                    assert forall |ii: int| 0 <= ii < result@.len() implies
                        Self::rank(result@[ii], arr2@) <= arr2@.len() + m as int
                    by {
                        if ii < old_result.len() as int {
                            assert(result@[ii] == old_result[ii]);
                        } else {
                            assert(result@[ii] == m as i32);
                        }
                    };
                }
            }

            proof {
                assert forall |ii: int| 0 <= ii < result@.len() implies
                    Self::rank(result@[ii], arr2@) < arr2@.len() + (m + 1) as int
                by {};

                assert forall |v: int| 0 <= v < (m + 1) as int implies cnt@[v] == 0i32
                by {};
            }

            m = m + 1;
        }

        proof {
            Self::sum_range_all_zero(cnt@, 0, 1001);

            assert forall |v: i32| Self::count(result@, v) == Self::count(arr1@, v)
            by {
                if 0 <= v <= 1000 {
                    assert(cnt@[v as int] == 0i32);
                } else {
                    Self::count_zero_not_present(result@, v);
                    Self::count_zero_not_present(arr1@, v);
                }
            };

            
            assert forall |ii: int, jj: int| 0 <= ii < jj < result@.len()
                && Self::index_of(result@[ii], arr2@) < 0
                && Self::index_of(result@[jj], arr2@) >= 0
                implies false
            by {
                let ri = result@[ii];
                let rj = result@[jj];
                let idx_j = Self::index_of(rj, arr2@);
                Self::index_of_bound(rj, arr2@);
                
                assert(Self::rank(rj, arr2@) == idx_j);
                
                assert(Self::rank(ri, arr2@) == arr2@.len() + ri as int);
                
                assert(Self::rank(ri, arr2@) >= arr2@.len() as int);
                
                assert(Self::rank(ri, arr2@) <= Self::rank(rj, arr2@));
            };

            assert forall |ii: int, jj: int| 0 <= ii < jj < result@.len()
                && Self::index_of(result@[ii], arr2@) >= 0
                && Self::index_of(result@[jj], arr2@) >= 0
                implies Self::index_of(result@[ii], arr2@) <= Self::index_of(result@[jj], arr2@)
            by {
                assert(Self::rank(result@[ii], arr2@) == Self::index_of(result@[ii], arr2@));
                assert(Self::rank(result@[jj], arr2@) == Self::index_of(result@[jj], arr2@));
                assert(Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@));
            };

            assert forall |ii: int, jj: int| 0 <= ii < jj < result@.len()
                && Self::index_of(result@[ii], arr2@) < 0
                && Self::index_of(result@[jj], arr2@) < 0
                implies result@[ii] <= result@[jj]
            by {
                assert(Self::rank(result@[ii], arr2@) == arr2@.len() + result@[ii] as int);
                assert(Self::rank(result@[jj], arr2@) == arr2@.len() + result@[jj] as int);
                assert(Self::rank(result@[ii], arr2@) <= Self::rank(result@[jj], arr2@));
            };
        }

        result
    }
}

}
