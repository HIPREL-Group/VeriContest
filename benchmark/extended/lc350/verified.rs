use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn nat_min(a: nat, b: nat) -> nat {
        if a <= b { a } else { b }
    }

    pub open spec fn count_occ_prefix(s: Seq<i32>, n: nat, v: i32) -> nat
        recommends
            n <= s.len(),
        decreases n
    {
        if n == 0 {
            0nat
        } else {
            Solution::count_occ_prefix(s, (n - 1) as nat, v) + if s[(n - 1) as int] == v { 1nat } else { 0nat }
        }
    }

    pub open spec fn count_occ(s: Seq<i32>, v: i32) -> nat {
        Solution::count_occ_prefix(s, s.len() as nat, v)
    }

    proof fn lemma_count_occ_prefix_step(s: Seq<i32>, n: nat, v: i32)
        requires
            n < s.len(),
        ensures
            Solution::count_occ_prefix(s, n + 1, v)
                == Solution::count_occ_prefix(s, n, v) + if s[n as int] == v { 1nat } else { 0nat },
    {
    }

    proof fn lemma_count_occ_prefix_push_same(s: Seq<i32>, a: i32, n: nat, v: i32)
        requires
            n <= s.len(),
        ensures
            Solution::count_occ_prefix(s.push(a), n, v) == Solution::count_occ_prefix(s, n, v),
        decreases n
    {
        if n == 0 {
        } else {
            Solution::lemma_count_occ_prefix_push_same(s, a, (n - 1) as nat, v);
        }
    }

    proof fn lemma_count_occ_push(s: Seq<i32>, a: i32, v: i32)
        ensures
            Solution::count_occ(s.push(a), v)
                == Solution::count_occ(s, v) + if a == v { 1nat } else { 0nat },
    {
        Solution::lemma_count_occ_prefix_step(s.push(a), s.len() as nat, v);
        Solution::lemma_count_occ_prefix_push_same(s, a, s.len() as nat, v);
        assert(s.push(a)[s.len() as int] == a);
    }

    pub fn intersect(nums1: Vec<i32>, nums2: Vec<i32>) -> (result: Vec<i32>)
        requires
            1 <= nums1.len() <= 1000,
            1 <= nums2.len() <= 1000,
            forall |i: int| 0 <= i < nums1.len() ==> 0 <= #[trigger] nums1[i] <= 1000,
            forall |i: int| 0 <= i < nums2.len() ==> 0 <= #[trigger] nums2[i] <= 1000,
        ensures
            forall |v: int| 0 <= v <= 1000 ==> #[trigger] Solution::count_occ(result@, v as i32)
                == Solution::nat_min(Solution::count_occ(nums1@, v as i32), Solution::count_occ(nums2@, v as i32)),
            forall |i: int| 0 <= i < result.len() ==> 0 <= #[trigger] result[i] <= 1000,
    {
        let mut freq1: Vec<i32> = Vec::new();
        let mut t: usize = 0;
        while t <= 1000
            invariant
                t <= 1001,
                freq1.len() == t,
                forall |k: int| 0 <= k < freq1.len() ==> #[trigger] freq1[k] == 0,
            decreases 1001 - t
        {
            freq1.push(0);
            t = t + 1;
        }
        let mut i: usize = 0;
        while i < nums1.len()
            invariant
                i <= nums1.len(),
                nums1.len() <= 1000,
                freq1.len() == 1001,
                forall |k: int| 0 <= k < nums1.len() ==> 0 <= #[trigger] nums1[k] <= 1000,
                forall |k: int| 0 <= k < 1001 ==> 0 <= #[trigger] freq1[k] && freq1[k] as int <= i as int,
                forall |v: int| 0 <= v <= 1000 ==> #[trigger] freq1[v] as nat
                    == Solution::count_occ_prefix(nums1@, i as nat, v as i32),
            decreases nums1.len() - i
        {
            proof {
                assert(0 <= nums1[i as int] <= 1000);
            }
            let idx: usize = nums1[i] as usize;
            proof {
                Solution::lemma_count_occ_prefix_step(nums1@, i as nat, idx as i32);
            }
            freq1.set(idx, freq1[idx] + 1);
            proof {
                assert forall |v: int| 0 <= v <= 1000 implies #[trigger] freq1[v] as nat
                    == Solution::count_occ_prefix(nums1@, (i + 1) as nat, v as i32) by {
                    if v == idx as int {
                        assert(nums1@[i as int] == v as i32);
                        Solution::lemma_count_occ_prefix_step(nums1@, i as nat, v as i32);
                    } else {
                        Solution::lemma_count_occ_prefix_step(nums1@, i as nat, v as i32);
                        assert(nums1@[i as int] != v as i32);
                    }
                }
            }
            i = i + 1;
        }

        let mut freq2: Vec<i32> = Vec::new();
        let mut t2: usize = 0;
        while t2 <= 1000
            invariant
                t2 <= 1001,
                freq2.len() == t2,
                forall |k: int| 0 <= k < freq2.len() ==> #[trigger] freq2[k] == 0,
            decreases 1001 - t2
        {
            freq2.push(0);
            t2 = t2 + 1;
        }
        let mut result: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        while j < nums2.len()
            invariant
                j <= nums2.len(),
                nums2.len() <= 1000,
                freq2.len() == 1001,
                forall |k: int| 0 <= k < nums2.len() ==> 0 <= #[trigger] nums2[k] <= 1000,
                forall |k: int| 0 <= k < 1001 ==> 0 <= #[trigger] freq2[k] && freq2[k] as int <= j as int,
                forall |v: int| 0 <= v <= 1000 ==> #[trigger] freq2[v] as nat
                    == Solution::count_occ_prefix(nums2@, j as nat, v as i32),
            decreases nums2.len() - j
        {
            proof {
                assert(0 <= nums2[j as int] <= 1000);
            }
            let idx: usize = nums2[j] as usize;
            proof {
                Solution::lemma_count_occ_prefix_step(nums2@, j as nat, idx as i32);
            }
            freq2.set(idx, freq2[idx] + 1);
            proof {
                assert forall |v: int| 0 <= v <= 1000 implies #[trigger] freq2[v] as nat
                    == Solution::count_occ_prefix(nums2@, (j + 1) as nat, v as i32) by {
                    if v == idx as int {
                        assert(nums2@[j as int] == v as i32);
                        Solution::lemma_count_occ_prefix_step(nums2@, j as nat, v as i32);
                    } else {
                        Solution::lemma_count_occ_prefix_step(nums2@, j as nat, v as i32);
                        assert(nums2@[j as int] != v as i32);
                    }
                }
            }
            j = j + 1;
        }

        let mut v: usize = 0;
        while v <= 1000
            invariant
                v <= 1001,
                freq1.len() == 1001,
                freq2.len() == 1001,
                forall |k: int| 0 <= k < 1001 ==> 0 <= #[trigger] freq1[k],
                forall |k: int| 0 <= k < 1001 ==> 0 <= #[trigger] freq2[k],
                forall |idx: int| 0 <= idx < result.len() ==> 0 <= #[trigger] result[idx] <= 1000,
                forall |x: int| 0 <= x < v ==> #[trigger] Solution::count_occ(result@, x as i32)
                    == Solution::nat_min(Solution::count_occ(nums1@, x as i32), Solution::count_occ(nums2@, x as i32)),
                forall |x: int| v <= x <= 1000 ==> #[trigger] Solution::count_occ(result@, x as i32) == 0,
                forall |x: int| 0 <= x <= 1000 ==> #[trigger] freq1[x] as nat == Solution::count_occ(nums1@, x as i32),
                forall |x: int| 0 <= x <= 1000 ==> #[trigger] freq2[x] as nat == Solution::count_occ(nums2@, x as i32),
            decreases 1001 - v
        {
            let copies: i32 = if freq1[v] < freq2[v] { freq1[v] } else { freq2[v] };
            proof {
                assert(0 <= freq1[v as int]);
                assert(0 <= freq2[v as int]);
            }
            let mut c: i32 = if freq1[v] < freq2[v] { freq1[v] } else { freq2[v] };
            while c > 0
                invariant
                    0 <= c <= copies,
                    0 <= copies,
                    v <= 1000,
                    forall |idx: int| 0 <= idx < result.len() ==> 0 <= #[trigger] result[idx] <= 1000,
                    forall |x: int| 0 <= x < v ==> #[trigger] Solution::count_occ(result@, x as i32)
                        == Solution::nat_min(Solution::count_occ(nums1@, x as i32), Solution::count_occ(nums2@, x as i32)),
                    forall |x: int| v < x <= 1000 ==> #[trigger] Solution::count_occ(result@, x as i32) == 0,
                    Solution::count_occ(result@, v as i32) + c as nat == copies as nat,
                decreases c
            {
                let ghost prev = result@;
                result.push(v as i32);
                proof {
                    Solution::lemma_count_occ_push(prev, v as i32, v as i32);
                    assert forall |x: int| 0 <= x < v implies #[trigger] Solution::count_occ(result@, x as i32)
                        == Solution::count_occ(prev, x as i32) by {
                        Solution::lemma_count_occ_push(prev, v as i32, x as i32);
                    }
                    assert forall |x: int| v < x <= 1000 implies #[trigger] Solution::count_occ(result@, x as i32)
                        == Solution::count_occ(prev, x as i32) by {
                        Solution::lemma_count_occ_push(prev, v as i32, x as i32);
                    }
                }
                c = c - 1;
            }

            proof {
                assert(Solution::count_occ(result@, v as i32) == copies as nat);
                assert(copies as nat == Solution::nat_min(freq1[v as int] as nat, freq2[v as int] as nat));
                assert(Solution::count_occ(result@, v as i32)
                    == Solution::nat_min(Solution::count_occ(nums1@, v as i32), Solution::count_occ(nums2@, v as i32)));
                assert forall |x: int| 0 <= x <= 1000 implies
                    (if x < v + 1 {
                        #[trigger] Solution::count_occ(result@, x as i32)
                        == Solution::nat_min(Solution::count_occ(nums1@, x as i32), Solution::count_occ(nums2@, x as i32))
                    } else {
                        #[trigger] Solution::count_occ(result@, x as i32) == 0
                    }) by {
                    if x < v {
                    } else if x == v {
                    } else {
                    }
                }
            }
            v = v + 1;
        }
        result
    }
}

}
