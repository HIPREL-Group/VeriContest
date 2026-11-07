use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn room_fits_two(p: i64, q: i64) -> bool {
    (q as int) - (p as int) >= 2
}

pub open spec fn accommodation_count_prefix(p: Seq<i64>, q: Seq<i64>, k: int) -> int
    recommends
        p.len() == q.len(),
        0 <= k <= p.len(),
    decreases k,
{
    if k <= 0 {
        0int
    } else {
        accommodation_count_prefix(p, q, k - 1) + if room_fits_two(p[k - 1], q[k - 1]) { 1int } else { 0int }
    }
}

proof fn lemma_accommodation_prefix_succ(p: Seq<i64>, q: Seq<i64>, i: int)
    requires
        p.len() == q.len(),
        0 <= i < p.len(),
    ensures
        accommodation_count_prefix(p, q, i + 1) == accommodation_count_prefix(p, q, i) + if room_fits_two(p[i], q[i]) { 1int } else { 0int },
{
    reveal_with_fuel(accommodation_count_prefix, 2);
}

proof fn lemma_room_fits_iff_sub_ge_two(p: i64, q: i64)
    requires
        0 <= (p as int) && (p as int) <= (q as int) && (q as int) <= 100,
    ensures
        room_fits_two(p, q) <==> (q - p >= 2),
{
    assert((q as int) - (p as int) == (q - p) as int);
}

proof fn lemma_accommodation_prefix_le_k(p: Seq<i64>, q: Seq<i64>, k: int)
    requires
        p.len() == q.len(),
        0 <= k <= p.len(),
    ensures
        accommodation_count_prefix(p, q, k) <= k,
    decreases k,
{
    if k <= 0 {
        reveal_with_fuel(accommodation_count_prefix, 1);
    } else {
        lemma_accommodation_prefix_le_k(p, q, k - 1);
        reveal_with_fuel(accommodation_count_prefix, 2);
        assert(accommodation_count_prefix(p, q, k - 1) + 1 <= (k - 1) + 1);
    }
}

impl Solution {
    pub fn count_accommodation_rooms(p: Vec<i64>, q: Vec<i64>) -> (result: usize)
        requires
            1 <= p.len() <= 100,
            p.len() == q.len(),
            forall|j: int| 0 <= j < p.len() ==> 0 <= (#[trigger] p[j] as int) && (p[j] as int) <= (q[j] as int) && (q[j] as int) <= 100,
        ensures
            result as int == accommodation_count_prefix(p@, q@, p.len() as int),
    {
        let n = p.len();
        let mut cnt = 0usize;
        let mut i = 0usize;
        while i < n
            invariant
                p.len() == q.len(),
                n == p.len(),
                1 <= n && n <= 100,
                forall|j: int| 0 <= j < p.len() ==> 0 <= (#[trigger] p[j] as int) && (p[j] as int) <= (q[j] as int) && (q[j] as int) <= 100,
                0 <= i <= n,
                cnt as int == accommodation_count_prefix(p@, q@, i as int),
            decreases n - i,
        {
            proof {
                assert(0 <= i as int && (i as int) < (p.len() as int));
                assert(0 <= (p@[i as int] as int) && (p@[i as int] as int) <= (q@[i as int] as int) && (q@[i as int] as int) <= 100);
                lemma_room_fits_iff_sub_ge_two(p@[i as int], q@[i as int]);
            }
            let fits = q[i] - p[i] >= 2;
            proof {
                assert(room_fits_two(p@[i as int], q@[i as int]) == fits);
            }
            if fits {
                proof {
                    lemma_accommodation_prefix_succ(p@, q@, i as int);
                    assert(cnt as int == accommodation_count_prefix(p@, q@, i as int));
                    assert((cnt + 1) as int == accommodation_count_prefix(p@, q@, i as int + 1));
                    lemma_accommodation_prefix_le_k(p@, q@, i as int);
                    assert((cnt + 1) as int <= (i as int + 1));
                    assert((cnt + 1) as int <= (n as int));
                }
                cnt = cnt + 1;
            } else {
                proof {
                    lemma_accommodation_prefix_succ(p@, q@, i as int);
                    assert(cnt as int == accommodation_count_prefix(p@, q@, i as int + 1));
                }
            }
            i = i + 1;
        }
        proof {
            assert(i == n);
            assert(cnt as int == accommodation_count_prefix(p@, q@, n as int));
            assert forall|j: int| 0 <= j < p.len() implies accommodation_count_prefix(p@, q@, j + 1) == accommodation_count_prefix(p@, q@, j) + if room_fits_two(p[j], q[j]) { 1int } else { 0int } by {
                lemma_accommodation_prefix_succ(p@, q@, j);
            }
        }
        cnt
    }
}

}
