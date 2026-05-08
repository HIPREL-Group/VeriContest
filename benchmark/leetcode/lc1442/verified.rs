use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn xor_range(arr: Seq<i32>, start: int, end: int) -> i32
    decreases end - start
{
    if start >= end {
        0i32
    } else {
        xor_range(arr, start, end - 1) ^ arr[end - 1]
    }
}

pub open spec fn count_k(arr: Seq<i32>, i: int, k: int) -> int
    decreases arr.len() - k
{
    if k >= arr.len() {
        0
    } else {
        (if xor_range(arr, i, k + 1) == 0i32 { k - i } else { 0int })
        + count_k(arr, i, k + 1)
    }
}

pub open spec fn count_all(arr: Seq<i32>, i: int) -> int
    decreases arr.len() - i
{
    if i >= arr.len() {
        0
    } else {
        count_k(arr, i, i + 1) + count_all(arr, i + 1)
    }
}


pub open spec fn contrib_at(pref: Seq<i32>, m: int, start: int) -> int
    decreases m - start
{
    if start >= m || m <= 0 {
        0int
    } else {
        (if pref[start] == pref[m] { m - 1 - start } else { 0int })
        + contrib_at(pref, m, start + 1)
    }
}


pub open spec fn total_contrib(pref: Seq<i32>, end: int) -> int
    decreases end
{
    if end <= 0 {
        0int
    } else {
        total_contrib(pref, end - 1) + contrib_at(pref, end - 1, 0)
    }
}


pub open spec fn count_val(pref: Seq<i32>, val: i32, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0int
    } else {
        (if pref[start] == val { 1int } else { 0int })
        + count_val(pref, val, start + 1, end)
    }
}


pub open spec fn sum_val(pref: Seq<i32>, val: i32, start: int, end: int) -> int
    decreases end - start
{
    if start >= end {
        0int
    } else {
        (if pref[start] == val { start } else { 0int })
        + sum_val(pref, val, start + 1, end)
    }
}

proof fn xor_identity(x: i32)
    ensures 0i32 ^ x == x, x ^ 0i32 == x
{
    assert(0i32 ^ x == x) by(bit_vector);
    assert(x ^ 0i32 == x) by(bit_vector);
}

proof fn lemma_xor_nonneg(a: i32, b: i32)
    requires
        0 <= a <= i32::MAX,
        0 <= b <= i32::MAX,
    ensures
        (a ^ b) >= 0,
{
    assert(a ^ b >= 0) by(bit_vector)
        requires
            0 <= a <= i32::MAX,
            0 <= b <= i32::MAX;
}

proof fn count_k_nonneg(arr: Seq<i32>, i: int, k: int)
    requires i <= k
    ensures count_k(arr, i, k) >= 0
    decreases arr.len() - k
{
    if k >= arr.len() {
    } else {
        count_k_nonneg(arr, i, k + 1);
    }
}

proof fn count_all_nonneg(arr: Seq<i32>, i: int)
    requires 0 <= i
    ensures count_all(arr, i) >= 0
    decreases arr.len() - i
{
    if i >= arr.len() {
    } else {
        count_k_nonneg(arr, i, i + 1);
        count_all_nonneg(arr, i + 1);
    }
}

proof fn count_k_upper(arr: Seq<i32>, i: int, k: int)
    requires 0 <= i, i < k, k <= arr.len(), arr.len() <= 300
    ensures count_k(arr, i, k) <= (arr.len() - k) * 300
    decreases arr.len() - k
{
    if k >= arr.len() {
    } else {
        count_k_nonneg(arr, i, k + 1);
        if k + 1 < arr.len() as int {
            count_k_upper(arr, i, k + 1);
        }
        if xor_range(arr, i, k + 1) == 0i32 {
            assert(count_k(arr, i, k) == (k - i) + count_k(arr, i, k + 1));
            assert(k - i < 300);
        } else {
            assert(count_k(arr, i, k) == count_k(arr, i, k + 1));
        }
    }
}

proof fn count_all_upper(arr: Seq<i32>, i: int)
    requires 0 <= i, i <= arr.len(), arr.len() <= 300
    ensures count_all(arr, i) <= (arr.len() - i) * 90_000
    decreases arr.len() - i
{
    if i >= arr.len() {
    } else {
        count_k_upper(arr, i, i + 1);
        if i + 1 < arr.len() as int {
            count_all_upper(arr, i + 1);
        }
        count_all_nonneg(arr, i + 1);
        let ck = count_k(arr, i, i + 1);
        let ca = count_all(arr, i + 1);
        let d = arr.len() - i;
        assert(ck <= (d - 1) * 300);
        assert(ca <= (d - 1) * 90_000);
        assert(ck + ca <= (d - 1) * 300 + (d - 1) * 90_000);
        assert((d - 1) * 300 + (d - 1) * 90_000 == (d - 1) * 90_300) by(nonlinear_arith);
        assert((d - 1) * 90_300 <= d * 90_000) by(nonlinear_arith)
            requires d <= 300;
    }
}

proof fn count_val_nonneg(pref: Seq<i32>, val: i32, start: int, end: int)
    requires 0 <= start
    ensures count_val(pref, val, start, end) >= 0
    decreases end - start
{
    if start >= end {} else {
        count_val_nonneg(pref, val, start + 1, end);
    }
}

proof fn sum_val_nonneg(pref: Seq<i32>, val: i32, start: int, end: int)
    requires 0 <= start
    ensures sum_val(pref, val, start, end) >= 0
    decreases end - start
{
    if start >= end {} else {
        sum_val_nonneg(pref, val, start + 1, end);
    }
}

proof fn count_val_extend(pref: Seq<i32>, val: i32, start: int, end: int)
    requires
        0 <= start,
        start <= end,
        end < pref.len(),
    ensures
        count_val(pref, val, start, end + 1) == count_val(pref, val, start, end)
            + if pref[end] == val { 1int } else { 0int },
    decreases end - start
{
    if start == end {
        assert(count_val(pref, val, start, end) == 0int);
        assert(count_val(pref, val, start + 1, end + 1) == 0int);
    } else {
        count_val_extend(pref, val, start + 1, end);
    }
}

proof fn sum_val_extend(pref: Seq<i32>, val: i32, start: int, end: int)
    requires
        0 <= start,
        start <= end,
        end < pref.len(),
    ensures
        sum_val(pref, val, start, end + 1) == sum_val(pref, val, start, end)
            + if pref[end] == val { end } else { 0int },
    decreases end - start
{
    if start == end {
        assert(sum_val(pref, val, start, end) == 0int);
        assert(sum_val(pref, val, start + 1, end + 1) == 0int);
    } else {
        sum_val_extend(pref, val, start + 1, end);
    }
}

proof fn contrib_at_nonneg(pref: Seq<i32>, m: int, start: int)
    requires 0 <= start
    ensures contrib_at(pref, m, start) >= 0
    decreases m - start
{
    if start >= m || m <= 0 {
    } else {
        contrib_at_nonneg(pref, m, start + 1);
    }
}

proof fn contrib_at_upper_mul2(pref: Seq<i32>, m: int, start: int)
    requires 0 <= start, m >= 1, m < pref.len()
    ensures contrib_at(pref, m, start) * 2 <= (m - start) * (m - start - 1)
    decreases m - start
{
    if start >= m {
        assert((m - start) * (m - start - 1) >= 0) by(nonlinear_arith)
            requires start >= m;
    } else {
        contrib_at_upper_mul2(pref, m, start + 1);
        contrib_at_nonneg(pref, m, start + 1);
        let k = m - start;
        assert(2 * (k - 1) + (k - 1) * (k - 2) == k * (k - 1)) by(nonlinear_arith);
    }
}

proof fn total_contrib_bounds(pref: Seq<i32>, end: int)
    requires 0 <= end, end <= pref.len(), end <= 301
    ensures
        total_contrib(pref, end) >= 0,
        total_contrib(pref, end) * 2 <= end * end * (end - 1),
    decreases end
{
    if end <= 0 {
    } else {
        total_contrib_bounds(pref, end - 1);
        contrib_at_nonneg(pref, end - 1, 0);
        if end - 1 >= 1 {
            contrib_at_upper_mul2(pref, end - 1, 0);
            let e = end;
            assert((e - 1) * (e - 1) * (e - 2) + (e - 1) * (e - 2)
                == (e - 2) * (e - 1) * e) by(nonlinear_arith);
            assert((e - 2) * (e - 1) * e <= e * e * (e - 1)) by(nonlinear_arith)
                requires e >= 2;
        }
    }
}

proof fn count_val_zero(pref: Seq<i32>, val: i32, start: int, end: int)
    requires
        0 <= start,
        forall |j: int| start <= j < end ==> pref[j] != val,
    ensures count_val(pref, val, start, end) == 0
    decreases end - start
{
    if start >= end {} else {
        count_val_zero(pref, val, start + 1, end);
    }
}

proof fn sum_val_zero(pref: Seq<i32>, val: i32, start: int, end: int)
    requires
        0 <= start,
        forall |j: int| start <= j < end ==> pref[j] != val,
    ensures sum_val(pref, val, start, end) == 0
    decreases end - start
{
    if start >= end {} else {
        sum_val_zero(pref, val, start + 1, end);
    }
}

proof fn count_val_upper(pref: Seq<i32>, val: i32, start: int, end: int)
    requires 0 <= start, start <= end
    ensures count_val(pref, val, start, end) <= end - start
    decreases end - start
{
    if start >= end {} else {
        count_val_upper(pref, val, start + 1, end);
    }
}

proof fn sum_val_from0_mul2_upper(pref: Seq<i32>, val: i32, n: int)
    requires 0 <= n, n <= pref.len()
    ensures sum_val(pref, val, 0, n) * 2 <= n * (n - 1)
    decreases n
{
    if n <= 0 {
        assert(sum_val(pref, val, 0, n) == 0int);
    } else if n == 1 {
        sum_val_extend(pref, val, 0, 0);
        assert(sum_val(pref, val, 0, 1) == 0int);
    } else {
        sum_val_from0_mul2_upper(pref, val, n - 1);
        sum_val_extend(pref, val, 0, n - 1);
        sum_val_nonneg(pref, val, 0, n);
        let sv_prev = sum_val(pref, val, 0, n - 1);
        let sv = sum_val(pref, val, 0, n);
        if pref[n - 1] == val {
            assert(sv == sv_prev + (n - 1));
            assert((n - 1) * (n - 2) + 2 * (n - 1) == n * (n - 1)) by(nonlinear_arith);
        } else {
            assert(sv == sv_prev);
            assert((n - 1) * (n - 2) <= n * (n - 1)) by(nonlinear_arith)
                requires n >= 2;
        }
    }
    assert(sum_val(pref, val, 0, n) * 2 <= n * (n - 1));
}


proof fn contrib_at_split(pref: Seq<i32>, m: int, start: int)
    requires
        0 <= start,
        start <= m,
        m > 0,
        m < pref.len(),
    ensures
        contrib_at(pref, m, start) == count_val(pref, pref[m], start, m) * (m - 1) - sum_val(pref, pref[m], start, m),
    decreases m - start
{
    if start >= m {
    } else {
        contrib_at_split(pref, m, start + 1);
        if pref[start] == pref[m] {
            assert(contrib_at(pref, m, start) == (m - 1 - start) + contrib_at(pref, m, start + 1));
            assert(count_val(pref, pref[m], start, m) == 1 + count_val(pref, pref[m], start + 1, m));
            assert(sum_val(pref, pref[m], start, m) == start + sum_val(pref, pref[m], start + 1, m));
            let c = count_val(pref, pref[m], start + 1, m);
            let s = sum_val(pref, pref[m], start + 1, m);
            assert((1 + c) * (m - 1) - (start + s) == (m - 1 - start) + c * (m - 1) - s)
                by(nonlinear_arith);
        }
    }
}


pub open spec fn row_sum(pref: Seq<i32>, p: int, end: int) -> int
    decreases end - p
{
    if p + 1 >= end {
        0int
    } else {
        (if pref[p] == pref[end - 1] { end - 2 - p } else { 0int })
        + row_sum(pref, p, end - 1)
    }
}

proof fn row_sum_unfold(pref: Seq<i32>, p: int, end: int)
    requires p + 1 < end
    ensures row_sum(pref, p, end) == (if pref[p] == pref[end - 1] { end - 2 - p } else { 0int }) + row_sum(pref, p, end - 1)
{}


pub open spec fn total_rows(pref: Seq<i32>, p_end: int, end: int) -> int
    decreases p_end
{
    if p_end <= 0 {
        0int
    } else {
        total_rows(pref, p_end - 1, end) + row_sum(pref, p_end - 1, end)
    }
}

proof fn lemma_extend_column(pref: Seq<i32>, p_end: int, end: int)
    requires 0 <= p_end, end > 0, end <= pref.len()
    ensures total_rows(pref, p_end, end) == total_rows(pref, p_end, end - 1)
        + contrib_at(pref, end - 1, 0) - contrib_at(pref, end - 1, p_end)
    decreases p_end
{
    if p_end <= 0 {
    } else {
        lemma_extend_column(pref, p_end - 1, end);
        
        
        
        
        if p_end < end {
            
        } else {
            
            
            contrib_at_nonneg(pref, end - 1, p_end - 1);
            contrib_at_nonneg(pref, end - 1, p_end);
        }
    }
}

proof fn double_sum_reorder(pref: Seq<i32>, end: int)
    requires 0 <= end, end <= pref.len()
    ensures total_contrib(pref, end) == total_rows(pref, end, end)
    decreases end
{
    if end <= 0 {
    } else {
        double_sum_reorder(pref, end - 1);
        lemma_extend_column(pref, end - 1, end);
        
        
        
        
    }
}

proof fn xor_range_split(arr: Seq<i32>, pref: Seq<i32>, i: int, j: int)
    requires
        0 <= i <= j,
        j <= arr.len(),
        pref.len() == arr.len() + 1,
        forall |k: int| 0 <= k <= arr.len() as int ==> pref[k] == xor_range(arr, 0, k),
    ensures xor_range(arr, i, j) == (pref[j] ^ pref[i])
    decreases j - i
{
    if i >= j {
        assert(xor_range(arr, i, j) == 0i32);
        assert(pref[j] == pref[i]);
        assert(pref[i] ^ pref[i] == 0i32) by(bit_vector);
    } else {
        xor_range_split(arr, pref, i, j - 1);
        
        
        
        
        let a = pref[j - 1];
        let b = pref[i];
        let c = arr[j - 1];
        assert((a ^ b) ^ c == (a ^ c) ^ b) by(bit_vector);
    }
}

proof fn xor_zero_iff_equal(a: i32, b: i32)
    ensures (a ^ b == 0i32) <==> (a == b)
{
    assert((a ^ b == 0i32) <==> (a == b)) by(bit_vector);
}


proof fn count_k_equals_row(arr: Seq<i32>, pref: Seq<i32>, i: int, k: int)
    requires
        0 <= i, i < k,
        k <= arr.len(),
        arr.len() <= 300,
        pref.len() == arr.len() + 1,
        forall |j: int| 0 <= j <= arr.len() as int ==> pref[j] == xor_range(arr, 0, j),
    ensures count_k(arr, i, k) == row_sum(pref, i, arr.len() as int + 1) - row_sum(pref, i, k + 1)
    decreases arr.len() - k
{
    let n = arr.len() as int;
    if k >= arr.len() {
    } else {
        count_k_equals_row(arr, pref, i, k + 1);
        xor_range_split(arr, pref, i, k + 1);
        let pk1 = pref[k + 1];
        let pi = pref[i];
        xor_zero_iff_equal(pk1, pi);
        assert(pk1 ^ pi == pi ^ pk1) by(bit_vector);
        row_sum_unfold(pref, i, k + 2);
        assert(k + 2 - 2 - i == k - i);
    }
}

proof fn count_all_equals_total_rows(arr: Seq<i32>, pref: Seq<i32>, i: int)
    requires
        0 <= i,
        i <= arr.len(),
        arr.len() <= 300,
        pref.len() == arr.len() + 1,
        forall |j: int| 0 <= j <= arr.len() as int ==> pref[j] == xor_range(arr, 0, j),
    ensures count_all(arr, i) == total_rows(pref, arr.len() as int, arr.len() as int + 1) - total_rows(pref, i, arr.len() as int + 1)
    decreases arr.len() - i
{
    let n = arr.len() as int;
    if i >= arr.len() {
        
        
        
        
    } else {
        count_all_equals_total_rows(arr, pref, i + 1);
        count_k_equals_row(arr, pref, i, i + 1);
        
        row_sum_unfold(pref, i, i + 2);
        
        assert(i + 2 - 2 - i == 0int);
    }
}


proof fn total_contrib_equals_count_all(arr: Seq<i32>, pref: Seq<i32>)
    requires
        1 <= arr.len() <= 300,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000_000,
        pref.len() == arr.len() + 1,
        forall |j: int| 0 <= j <= arr.len() as int ==> pref[j] == xor_range(arr, 0, j),
    ensures
        total_contrib(pref, arr.len() as int + 1) == count_all(arr, 0),
{
    let n = arr.len() as int;
    double_sum_reorder(pref, n + 1);
    
    
    
    
    count_all_equals_total_rows(arr, pref, 0);
    
    
    
}

proof fn total_contrib_nonneg(arr: Seq<i32>, pref: Seq<i32>, end: int)
    requires
        1 <= arr.len() <= 300,
        forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000_000,
        pref.len() == arr.len() + 1,
        forall |j: int| 0 <= j <= arr.len() as int ==> pref[j] == xor_range(arr, 0, j),
        0 <= end <= arr.len() + 1,
    ensures
        total_contrib(pref, end) >= 0,
        total_contrib(pref, end) <= 300 * 90_000,
{
    total_contrib_bounds(pref, end);
    let tc = total_contrib(pref, end);
    assert(tc * 2 <= end * end * (end - 1));
    assert(end * end * (end - 1) <= 301 * 301 * 300) by(nonlinear_arith)
        requires 0 <= end <= 301;
    assert(301 * 301 * 300 <= 2 * 300 * 90_000) by(nonlinear_arith);
}

impl Solution {
    pub fn count_triplets(arr: Vec<i32>) -> (res: i32)
        requires
            1 <= arr.len() <= 300,
            forall |i: int| 0 <= i < arr.len() ==> 1 <= #[trigger] arr[i] <= 100_000_000,
        ensures
            res as int == count_all(arr@, 0),
    {
        let n = arr.len();

        let mut prefix: Vec<i32> = Vec::new();
        prefix.push(0);
        let mut i: usize = 0;

        proof { xor_identity(0i32); }

        while i < n
            invariant
                0 <= i <= n,
                n == arr.len(),
                1 <= n <= 300,
                prefix.len() == i + 1,
                forall |j: int| 0 <= j <= i as int ==> prefix@[j] == xor_range(arr@, 0, j),
                forall |j: int| 0 <= j <= i as int ==> prefix@[j] >= 0,
                forall |idx: int| 0 <= idx < n ==> 1 <= #[trigger] arr@[idx] <= 100_000_000,
            decreases n - i
        {
            let prev = prefix[i];
            proof {
                lemma_xor_nonneg(prev, arr@[i as int]);
                assert(prev == xor_range(arr@, 0, i as int));
                assert(xor_range(arr@, 0, (i + 1) as int) ==
                    xor_range(arr@, 0, i as int) ^ arr@[i as int]);
            }
            prefix.push(prev ^ arr[i]);
            i = i + 1;
        }

        proof {
            count_all_upper(arr@, 0);
            count_all_nonneg(arr@, 0);
            total_contrib_equals_count_all(arr@, prefix@);
        }

        let mut keys: Vec<i32> = Vec::new();
        let mut cnts: Vec<i32> = Vec::new();
        let mut sums: Vec<i32> = Vec::new();
        let mut count: i32 = 0;
        let mut m: usize = 0;

        while m <= n
            invariant
                0 <= m <= n + 1,
                n == arr.len(),
                1 <= n <= 300,
                prefix.len() == n + 1,
                forall |j: int| 0 <= j <= n as int ==> prefix@[j] == xor_range(arr@, 0, j),
                forall |j: int| 0 <= j <= n as int ==> prefix@[j] >= 0,
                forall |idx: int| 0 <= idx < n ==> 1 <= #[trigger] arr@[idx] <= 100_000_000,
                keys.len() == cnts.len(),
                keys.len() == sums.len(),
                keys.len() <= m,
                forall |a: int, b: int| 0 <= a < b < keys.len() as int
                    ==> keys@[a] != keys@[b],
                forall |idx: int| 0 <= idx < keys.len() as int ==> (
                    #[trigger] cnts@[idx] == count_val(prefix@, keys@[idx], 0, m as int)
                    && sums@[idx] == sum_val(prefix@, keys@[idx], 0, m as int)
                ),
                forall |j: int| 0 <= j < m as int ==>
                    exists |idx: int| 0 <= idx < keys.len() as int
                        && keys@[idx] == #[trigger] prefix@[j],
                forall |idx: int| 0 <= idx < keys.len() as int ==> cnts@[idx] >= 1,
                forall |idx: int| 0 <= idx < keys.len() as int ==> sums@[idx] >= 0,
                forall |idx: int| 0 <= idx < keys.len() as int ==> cnts@[idx] <= 301,
                forall |idx: int| 0 <= idx < keys.len() as int ==> sums@[idx] <= 45_150,
                count as int == total_contrib(prefix@, m as int),
                0 <= count as int,
                count as int <= 300 * 90_000,
            decreases n + 1 - m
        {
            let pv = prefix[m];
            let mut found: bool = false;
            let mut idx: usize = 0;
            let keys_len = keys.len();

            let ghost old_count = count as int;
            let ghost old_keys = keys@;
            let ghost old_cnts = cnts@;
            let ghost old_sums = sums@;
            let ghost old_keys_len = keys_len as int;
            let ghost mut found_at: int = 0;

            while idx < keys_len
                invariant
                    0 <= idx <= keys_len,
                    keys_len == keys.len(),
                    keys.len() == cnts.len(),
                    keys.len() == sums.len(),
                    keys_len == old_keys_len,
                    found ==> idx == keys_len,
                    !found ==> (
                        keys@ == old_keys
                        && cnts@ == old_cnts
                        && sums@ == old_sums
                        && count as int == old_count
                        && forall |j: int| 0 <= j < idx as int ==> old_keys[j] != pv
                    ),
                    found ==> (
                        0 <= found_at < old_keys_len
                        && old_keys[found_at] == pv
                        && keys@ == old_keys
                        && cnts@ == old_cnts.update(found_at, (old_cnts[found_at] + 1) as i32)
                        && sums@ == old_sums.update(found_at, (old_sums[found_at] + m as int) as i32)
                        && (m > 0 ==> count as int == old_count
                            + old_cnts[found_at] as int * (m as int - 1) - old_sums[found_at] as int)
                        && (m == 0 ==> count as int == old_count)
                    ),
                    0 <= m <= n,
                    n == arr.len(),
                    1 <= n <= 300,
                    prefix.len() == n + 1,
                    forall |j: int| 0 <= j <= n as int ==> prefix@[j] == xor_range(arr@, 0, j),
                    forall |j: int| 0 <= j <= n as int ==> prefix@[j] >= 0,
                    forall |idx_a: int| 0 <= idx_a < n ==> 1 <= #[trigger] arr@[idx_a] <= 100_000_000,
                    old_count == total_contrib(prefix@, m as int),
                    pv == prefix@[m as int],
                    forall |idx2: int| 0 <= idx2 < old_keys_len ==> (
                        old_cnts[idx2] == count_val(prefix@, old_keys[idx2], 0, m as int)
                        && old_sums[idx2] == sum_val(prefix@, old_keys[idx2], 0, m as int)
                    ),
                    forall |a_i: int, b_i: int| 0 <= a_i < b_i < old_keys_len ==> old_keys[a_i] != old_keys[b_i],
                    forall |j: int| 0 <= j < m as int ==>
                        exists |idx2: int| 0 <= idx2 < old_keys_len
                            && old_keys[idx2] == #[trigger] prefix@[j],
                    forall |idx2: int| 0 <= idx2 < keys.len() as int ==> old_cnts[idx2] >= 1,
                    forall |idx2: int| 0 <= idx2 < keys.len() as int ==> old_sums[idx2] >= 0,
                    forall |idx2: int| 0 <= idx2 < keys.len() as int ==> old_cnts[idx2] <= 301,
                    forall |idx2: int| 0 <= idx2 < keys.len() as int ==> old_sums[idx2] <= 45_150,
                    old_keys_len <= m as int,
                    count as int <= 300 * 90_000,
                    0 <= count as int,
                    old_count <= 300 * 90_000,
                    0 <= old_count,
                decreases keys_len - idx
            {
                if keys[idx] == pv {
                    found = true;
                    proof { found_at = idx as int; }
                    if m > 0 {
                        proof {
                            let cv = old_cnts[idx as int] as int;
                            let mv = m as int;
                            assert(cv * (mv - 1) <= 301 * 299) by(nonlinear_arith)
                                requires 1 <= cv <= 301, 1 <= mv <= 300;
                        }
                        count = count + cnts[idx] * ((m as i32) - 1) - sums[idx];
                        proof {
                            
                            
                            
                            
                            contrib_at_split(prefix@, m as int, 0);
                            total_contrib_nonneg(arr@, prefix@, (m + 1) as int);
                        }
                    }
                    cnts.set(idx, cnts[idx] + 1);
                    sums.set(idx, sums[idx] + m as i32);
                    proof {
                        assert(cnts@ =~= old_cnts.update(idx as int, (old_cnts[idx as int] + 1) as i32));
                        assert(sums@ =~= old_sums.update(idx as int, (old_sums[idx as int] + m as int) as i32));
                    }
                    idx = keys_len;
                } else {
                    idx = idx + 1;
                }
            }

            if !found {
                keys.push(pv);
                cnts.push(1);
                sums.push(m as i32);
            }

            proof {
                
                let tc_m = total_contrib(prefix@, m as int);
                let ca_m = contrib_at(prefix@, m as int, 0);
                
                assert(total_contrib(prefix@, (m + 1) as int) == tc_m + ca_m);
                assert(old_count == tc_m);
                if found {
                    if m > 0 {
                        contrib_at_split(prefix@, m as int, 0);
                        let the_val = prefix@[m as int];
                        assert(old_keys[found_at] == the_val);
                        let cv_old = count_val(prefix@, the_val, 0, m as int);
                        let sv_old = sum_val(prefix@, the_val, 0, m as int);
                        assert(old_cnts[found_at] as int == cv_old);
                        assert(old_sums[found_at] as int == sv_old);
                        assert(ca_m == cv_old * (m as int - 1) - sv_old);
                        assert(count as int == old_count + cv_old * (m as int - 1) - sv_old);
                    }
                } else {
                    if m > 0 {
                        assert forall |j: int| 0 <= j < m as int implies prefix@[j] != pv by {
                            let wit = choose |idx2: int| 0 <= idx2 < old_keys_len
                                && old_keys[idx2] == prefix@[j];
                        };
                        count_val_zero(prefix@, pv, 0, m as int);
                        sum_val_zero(prefix@, pv, 0, m as int);
                        contrib_at_split(prefix@, m as int, 0);
                        assert(ca_m == 0int);
                    }
                }
                assert(count as int == tc_m + ca_m);
                assert(count as int == total_contrib(prefix@, (m + 1) as int));

                
                assert forall |idx2: int| 0 <= idx2 < keys.len() as int implies (
                    #[trigger] cnts@[idx2] == count_val(prefix@, keys@[idx2], 0, (m + 1) as int)
                    && sums@[idx2] == sum_val(prefix@, keys@[idx2], 0, (m + 1) as int)
                ) by {
                    count_val_extend(prefix@, keys@[idx2], 0, m as int);
                    sum_val_extend(prefix@, keys@[idx2], 0, m as int);
                    if found {
                        if idx2 == found_at {
                            
                            
                        } else {
                            
                            
                        }
                    } else {
                        if idx2 < old_keys_len as int {
                            
                            
                        } else {
                            
                            count_val_zero(prefix@, pv, 0, m as int);
                            sum_val_zero(prefix@, pv, 0, m as int);
                        }
                    }
                };

                
                assert forall |j: int| 0 <= j < (m + 1) as int implies
                    exists |idx2: int| 0 <= idx2 < keys.len() as int
                        && keys@[idx2] == #[trigger] prefix@[j]
                by {
                    if j < m as int {
                        
                        let wit = choose |idx2: int| 0 <= idx2 < old_keys_len
                            && old_keys[idx2] == prefix@[j];
                        assert(keys@[wit] == prefix@[j]);
                    } else {
                        
                        if found {
                            assert(keys@[found_at] == pv);
                        } else {
                            assert(keys@[old_keys_len] == pv);
                        }
                    }
                };

                
                if found {
                    
                } else {
                    assert forall |a: int, b: int| 0 <= a < b < keys.len() as int
                        implies keys@[a] != keys@[b]
                    by {
                        if b < old_keys_len as int {
                            
                        } else {
                            
                            
                        }
                    };
                }

                
                assert forall |idx2: int| 0 <= idx2 < keys.len() as int implies cnts@[idx2] >= 1 by {
                    if found {
                        if idx2 == found_at {
                        } else {
                        }
                    } else {
                        if idx2 < old_keys_len as int {
                        } else {
                        }
                    }
                };

                
                assert forall |idx2: int| 0 <= idx2 < keys.len() as int implies sums@[idx2] >= 0 by {
                    if found {
                        if idx2 == found_at {
                        } else {
                        }
                    } else {
                        if idx2 < old_keys_len as int {
                        } else {
                        }
                    }
                };

                
                assert forall |idx2: int| 0 <= idx2 < keys.len() as int implies cnts@[idx2] <= 301 by {
                    count_val_extend(prefix@, keys@[idx2], 0, m as int);
                    count_val_upper(prefix@, keys@[idx2], 0, (m + 1) as int);
                };

                
                assert forall |idx2: int| 0 <= idx2 < keys.len() as int implies sums@[idx2] <= 45_150 by {
                    
                    assert(#[trigger] cnts@[idx2] == count_val(prefix@, keys@[idx2], 0, (m + 1) as int));
                    let sv = sum_val(prefix@, keys@[idx2], 0, (m + 1) as int);
                    assert(sums@[idx2] as int == sv);
                    sum_val_nonneg(prefix@, keys@[idx2], 0, (m + 1) as int);
                    sum_val_from0_mul2_upper(prefix@, keys@[idx2], (m + 1) as int);
                    assert(sv * 2 <= (m + 1) as int * m as int);
                    assert((m + 1) as int * m as int <= 90_300) by(nonlinear_arith)
                        requires 0 <= m as int <= 300;
                };

                total_contrib_nonneg(arr@, prefix@, (m + 1) as int);
            }

            let ghost target_m: int = (m + 1) as int;
            m = m + 1;
            proof {
                assert(m as int == target_m);
            }
        }

        proof {
            total_contrib_equals_count_all(arr@, prefix@);
        }

        count
    }
}

}
