use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

impl Solution {
    pub open spec fn sorted(s: Seq<i32>) -> bool {
        forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
    }

    pub open spec fn is_index_permutation(p: Seq<int>, n: int) -> bool {
        p.len() == n
            && forall|i: int| 0 <= i < n ==> 0 <= #[trigger] p[i] < n
            && forall|i: int, j: int| 0 <= i < j < n ==> p[i] != p[j]
    }

    pub open spec fn count_pairs_from(s: Seq<i32>, last: int, left: int, right: int) -> nat
        recommends
            0 <= left <= right <= last < s.len(),
        decreases if left < right { (right - left) as nat } else { 0nat }
    {
        if right <= 1 || left >= right {
            0nat
        } else {
            let mid = right - 1;
            if left < mid {
                if s[left] as int + s[mid] as int > s[last] as int {
                    (mid - left) as nat + Self::count_pairs_from(s, last, left, mid)
                } else {
                    Self::count_pairs_from(s, last, left + 1, right)
                }
            } else {
                0nat
            }
        }
    }

    pub open spec fn triangle_count_from(s: Seq<i32>, start_last: int) -> nat
        decreases if start_last <= s.len() { (s.len() - start_last + 1) as nat } else { 0nat }
    {
        if start_last >= s.len() {
            0nat
        } else {
            Self::count_pairs_from(s, start_last, 0, start_last)
                + Self::triangle_count_from(s, start_last + 1)
        }
    }

    pub open spec fn triangle_count(s: Seq<i32>) -> nat {
        if s.len() < 3 {
            0nat
        } else {
            Self::triangle_count_from(s, 2)
        }
    }

    proof fn lemma_swap_preserves_index_permutation(p: Seq<int>, i: int, j: int, n: int)
        requires
            Self::is_index_permutation(p, n),
            0 <= i < n,
            0 <= j < n,
        ensures
            Self::is_index_permutation(p.update(i, p[j]).update(j, p[i]), n),
    {
        let q = p.update(i, p[j]).update(j, p[i]);
        assert(q.len() == n);
        assert forall|k: int| 0 <= k < n implies 0 <= #[trigger] q[k] < n by {
            if k == i {
                assert(q[k] == p[j]);
            } else if k == j {
                assert(q[k] == p[i]);
            } else {
                assert(q[k] == p[k]);
            }
        }
        assert forall|a: int, b: int| 0 <= a < b < n implies q[a] != q[b] by {
            if a == i {
                if b == j {
                    assert(q[a] == p[j]);
                    assert(q[b] == p[i]);
                    assert(i != j);
                } else {
                    assert(q[a] == p[j]);
                    assert(q[b] == p[b]);
                    assert(j != b);
                }
            } else if a == j {
                assert(q[a] == p[i]);
                if b == i {
                    assert(q[b] == p[j]);
                    assert(i != j);
                } else {
                    assert(q[b] == p[b]);
                    assert(i != b);
                }
            } else {
                assert(q[a] == p[a]);
                if b == i {
                    assert(q[b] == p[j]);
                    assert(a != j);
                } else if b == j {
                    assert(q[b] == p[i]);
                    assert(a != i);
                } else {
                    assert(q[b] == p[b]);
                }
            }
        }
    }

    proof fn lemma_count_pairs_no_room(s: Seq<i32>, last: int, left: int, right: int)
        requires
            0 <= left < right <= last < s.len(),
            left + 1 >= right,
        ensures
            Self::count_pairs_from(s, last, left, right) == 0nat,
        decreases right - left,
    {
        let mid = right - 1;
        assert(left >= mid);
        assert(Self::count_pairs_from(s, last, left, right) == Self::count_pairs_from(s, last, left, mid));
        if mid > left {
            Self::lemma_count_pairs_no_room(s, last, left, mid);
        } else {
            assert(mid <= 1 || left + 1 >= mid);
            assert(Self::count_pairs_from(s, last, left, mid) == 0nat);
        }
    }

    proof fn lemma_count_pairs_bound(s: Seq<i32>, last: int, left: int, right: int)
        requires
            0 <= left < right <= last < s.len(),
        ensures
            Self::count_pairs_from(s, last, left, right) <= (right * right) as nat,
        decreases right - left,
    {
        let mid = right - 1;
        if left < mid {
            if s[left] as int + s[mid] as int > s[last] as int {
                Self::lemma_count_pairs_bound(s, last, left, mid);
                assert(Self::count_pairs_from(s, last, left, right)
                    == (mid - left) as nat + Self::count_pairs_from(s, last, left, mid));
                assert((mid - left) as nat + (mid * mid) as nat <= (right * right) as nat) by (nonlinear_arith)
                    requires
                        left < mid,
                        mid == right - 1,
                        0 <= left,
                        0 <= right,
                ;
            } else {
                Self::lemma_count_pairs_bound(s, last, left + 1, right);
                assert(Self::count_pairs_from(s, last, left, right)
                    == Self::count_pairs_from(s, last, left + 1, right));
            }
        } else {
            assert(Self::count_pairs_from(s, last, left, right)
                == Self::count_pairs_from(s, last, left, mid));
            if mid > left {
                Self::lemma_count_pairs_bound(s, last, left, mid);
            } else {
                assert(Self::count_pairs_from(s, last, left, mid) == 0nat);
            }
        }
    }

    pub fn triangle_number(nums: Vec<i32>) -> (result: i32)
        requires
            1 <= nums.len() <= 1000,
            forall|i: int| 0 <= i < nums.len() ==> 0 <= #[trigger] nums[i] <= 1000,
        ensures
            result >= 0,
            exists|sorted_nums: Seq<i32>, perm: Seq<int>|
                Self::sorted(sorted_nums)
                && Self::is_index_permutation(perm, nums.len() as int)
                && sorted_nums.len() == nums.len()
                && (forall|i: int| 0 <= i < nums.len() ==> #[trigger] sorted_nums[i] == nums[perm[i]])
                && result as nat == Self::triangle_count(sorted_nums),
    {
        let ghost orig = nums@;
        proof { assert(orig.len() == nums.len()); }
        let mut nums = nums;
        let n = nums.len();
        let ghost mut perm: Seq<int> = Seq::new(n as nat, |i: int| i);
        let mut i = 0usize;
        while i < n
            invariant
                n == nums.len(),
                orig.len() == n,
                1 <= n <= 1000,
                forall|k: int| 0 <= k < n ==> 0 <= #[trigger] nums[k] <= 1000,
                perm.len() == n,
                Self::is_index_permutation(perm, n as int),
                forall|k: int| 0 <= k < n ==> 0 <= #[trigger] perm[k] < n && nums[k] == orig[perm[k]],
                0 <= i <= n,
                forall|a: int, b: int| 0 <= a < b < i ==> nums[a] <= nums[b],
                forall|a: int, b: int| 0 <= a < i && i <= b < n ==> nums[a] <= nums[b],
            decreases n - i,
        {
            let mut min_idx = i;
            let mut j = i + 1;
            while j < n
                invariant
                    n == nums.len(),
                    orig.len() == n,
                    1 <= n <= 1000,
                    i < n,
                    i <= min_idx < n,
                    i + 1 <= j <= n,
                    forall|k: int| 0 <= k < n ==> 0 <= #[trigger] nums[k] <= 1000,
                    forall|k: int| i <= k < j ==> nums[min_idx as int] <= #[trigger] nums[k],
                    perm.len() == n,
                    Self::is_index_permutation(perm, n as int),
                    forall|k: int| 0 <= k < n ==> 0 <= #[trigger] perm[k] < n && nums[k] == orig[perm[k]],
                    forall|a: int, b: int| 0 <= a < b < i ==> nums[a] <= nums[b],
                    forall|a: int, b: int| 0 <= a < i && i <= b < n ==> nums[a] <= nums[b],
                decreases n - j,
            {
                if nums[j] < nums[min_idx] {
                    min_idx = j;
                }
                j += 1;
            }

            let old_i = i;
            let old_min_idx = min_idx;
            let tmp = nums[i];
            let ghost old_perm = perm;
            nums[i] = nums[min_idx];
            nums[min_idx] = tmp;
            proof {
                perm = old_perm.update(old_i as int, old_perm[old_min_idx as int]).update(old_min_idx as int, old_perm[old_i as int]);
                Self::lemma_swap_preserves_index_permutation(old_perm, old_i as int, old_min_idx as int, n as int);
                assert forall|k: int| 0 <= k < n implies 0 <= #[trigger] perm[k] < n && nums[k] == orig[perm[k]] by {
                    if k == old_i as int {
                        assert(nums[k] == orig[old_perm[old_min_idx as int]]);
                        assert(perm[k] == old_perm[old_min_idx as int]);
                    } else if k == old_min_idx as int {
                        assert(nums[k] == orig[old_perm[old_i as int]]);
                        assert(perm[k] == old_perm[old_i as int]);
                    } else {
                        assert(nums[k] == orig[old_perm[k]]);
                        assert(perm[k] == old_perm[k]);
                    }
                }
                assert forall|a: int, b: int| 0 <= a < b < old_i + 1 implies nums[a] <= nums[b] by {
                    if b < old_i {
                    } else {
                        assert(b == old_i);
                        assert(old_perm.len() == n);
                        if a < old_i {
                            assert(nums[a] <= orig[old_perm[old_min_idx as int]]);
                            assert(nums[b] == orig[old_perm[old_min_idx as int]]);
                        }
                    }
                }
                assert forall|a: int, b: int| 0 <= a < old_i + 1 && old_i + 1 <= b < n implies nums[a] <= nums[b] by {
                    if a < old_i {
                        if b == old_min_idx as int {
                            assert(nums[b] == orig[old_perm[old_i as int]]);
                        } else {
                            assert(nums[b] == orig[old_perm[b]]);
                        }
                    } else {
                        assert(a == old_i);
                        if b == old_min_idx as int {
                            assert(nums[a] == orig[old_perm[old_min_idx as int]]);
                            assert(nums[b] == orig[old_perm[old_i as int]]);
                        } else {
                            assert(nums[a] == orig[old_perm[old_min_idx as int]]);
                            assert(nums[b] == orig[old_perm[b]]);
                            assert(orig[old_perm[old_min_idx as int]] <= orig[old_perm[b]]);
                        }
                    }
                }
            }
            i += 1;
        }

        if n < 3 {
            proof {
                assert(Self::triangle_count(nums@) == 0nat);
                assert(exists|sorted_nums: Seq<i32>, p: Seq<int>|
                    Self::sorted(sorted_nums)
                    && Self::is_index_permutation(p, n as int)
                    && sorted_nums.len() == n
                    && (forall|idx: int| 0 <= idx < n ==> #[trigger] sorted_nums[idx] == orig[p[idx]])
                    && 0nat == Self::triangle_count(sorted_nums)) by {
                    let sorted_nums = nums@;
                    let p = perm;
                }
            }
            return 0;
        }

        let mut count: usize = 0;
        let mut k = n;
        while k > 2
            invariant
                n == nums.len(),
                orig.len() == n,
                3 <= n <= 1000,
                forall|idx: int| 0 <= idx < n ==> 0 <= #[trigger] nums[idx] <= 1000,
                Self::sorted(nums@),
                perm.len() == n,
                Self::is_index_permutation(perm, n as int),
                forall|idx: int| 0 <= idx < n ==> 0 <= #[trigger] perm[idx] < n && nums[idx] == orig[perm[idx]],
                2 <= k <= n,
                count as nat == Self::triangle_count_from(nums@, k as int),
                count <= (n - k) * n * n,
            decreases k - 2,
        {
            let old_k = k;
            let last = k - 1;
            let mut left = 0usize;
            let mut right = last;
            let mut pair_count: usize = 0;
            while right > 1 && left + 1 < right
                invariant
                    n == nums.len(),
                    orig.len() == n,
                    3 <= n <= 1000,
                    0 <= left < right <= last,
                    2 <= last < n,
                    forall|idx: int| 0 <= idx < n ==> 0 <= #[trigger] nums[idx] <= 1000,
                    Self::sorted(nums@),
                    pair_count as nat + Self::count_pairs_from(nums@, last as int, left as int, right as int)
                        == Self::count_pairs_from(nums@, last as int, 0, last as int),
                    pair_count <= n * n,
                decreases right - left,
            {
                let mid = right - 1;
                if nums[left] + nums[mid] > nums[last] {
                    proof {
                        assert(left + 1 < right);
                        assert((left as int) < (right as int) - 1);
                        assert(mid == right - 1);
                        assert(left < mid);
                        let total = Self::count_pairs_from(nums@, last as int, 0, last as int);
                        assert(Self::count_pairs_from(nums@, last as int, left as int, right as int)
                            == (mid - left) as nat + Self::count_pairs_from(nums@, last as int, left as int, mid as int));
                        Self::lemma_count_pairs_bound(nums@, last as int, 0, last as int);
                        assert(total <= (last as int * last as int) as nat);
                        assert((last as int * last as int) as nat <= (n * n) as nat) by (nonlinear_arith)
                            requires 2 <= last, last < n, 3 <= n
                        {};
                        assert(total <= (n * n) as nat);
                        assert(pair_count as nat + (mid - left) as nat
                            <= total);
                        assert(pair_count + (mid - left) <= n * n);
                        assert(pair_count as nat + (mid - left) as nat
                            + Self::count_pairs_from(nums@, last as int, left as int, mid as int)
                            == total);
                        assert(pair_count + (mid - left) <= 1_000_000_000) by (nonlinear_arith)
                            requires pair_count <= n * n, mid <= last, last < n, n <= 1000, 0 <= left
                        {};
                    }
                    pair_count = pair_count + (mid - left);
                    right -= 1;
                } else {
                    proof {
                        assert(Self::count_pairs_from(nums@, last as int, left as int, right as int)
                            == Self::count_pairs_from(nums@, last as int, left as int + 1, right as int));
                    }
                    left += 1;
                }
            }
            proof {
                if right > 1 {
                    assert(left + 1 >= right);
                    Self::lemma_count_pairs_no_room(nums@, last as int, left as int, right as int);
                } else {
                    assert(Self::count_pairs_from(nums@, last as int, left as int, right as int) == 0nat);
                }
                assert(Self::count_pairs_from(nums@, last as int, 0, last as int)
                    == pair_count as nat);
                assert(Self::triangle_count_from(nums@, last as int)
                    == Self::count_pairs_from(nums@, last as int, 0, last as int)
                        + Self::triangle_count_from(nums@, old_k as int));
                assert(pair_count <= n * n);
                assert(count + pair_count <= (n - old_k) * n * n + n * n);
                assert((n - old_k) * n * n + n * n == (n - last) * n * n) by (nonlinear_arith)
                    requires
                        last == old_k - 1,
                ;
                assert(count <= (n - old_k) * n * n);
                assert((n - last) * n * n <= 1_000_000_000) by (nonlinear_arith)
                    requires n <= 1000, 3 <= n
                {};
            }
            count = count + pair_count;
            k -= 1;
        }
        proof {
            assert(k == 2usize);
            assert(Self::triangle_count(nums@) == Self::triangle_count_from(nums@, 2));
            assert(Self::triangle_count(nums@) == Self::triangle_count_from(nums@, 2));
            assert(count <= n * n * n) by (nonlinear_arith)
                requires
                    count <= (n - 2) * n * n,
                    n >= 3,
            ;
            assert(count <= 1_000_000_000) by (nonlinear_arith)
                requires
                    n <= 1000,
                    count <= n * n * n,
            ;
            assert(exists|sorted_nums: Seq<i32>, p: Seq<int>|
                Self::sorted(sorted_nums)
                && Self::is_index_permutation(p, n as int)
                && sorted_nums.len() == n
                && (forall|idx: int| 0 <= idx < n ==> #[trigger] sorted_nums[idx] == orig[p[idx]])
                && count as nat == Self::triangle_count(sorted_nums)) by {
                let sorted_nums = nums@;
                let p = perm;
            }
        }
        count as i32
    }
}

}
