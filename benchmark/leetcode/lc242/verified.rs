use vstd::prelude::*;

fn main() {}

verus! {

pub struct Solution;

pub open spec fn count_char(s: Seq<char>, c: char) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.last() == c {
        count_char(s.drop_last(), c) + 1
    } else {
        count_char(s.drop_last(), c)
    }
}

pub open spec fn is_lowercase_word(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
}

pub open spec fn letter(j: int) -> char {
    (j + 97) as u8 as char
}

pub open spec fn is_anagram_spec(s: Seq<char>, t: Seq<char>) -> bool {
    s.len() == t.len() && forall |j: int| 0 <= j < 26 ==>
        #[trigger] count_char(s, letter(j)) == count_char(t, letter(j))
}

proof fn lemma_count_char_bounds(s: Seq<char>, c: char)
    ensures count_char(s, c) <= s.len(),
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_char_bounds(s.drop_last(), c);
    }
}

proof fn lemma_count_char_nonneg(s: Seq<char>, c: char)
    ensures count_char(s, c) >= 0,
    decreases s.len(),
{
    if s.len() > 0 {
        lemma_count_char_nonneg(s.drop_last(), c);
    }
}

proof fn lemma_anagram_one(s: Seq<char>, t: Seq<char>, j: int, cnt_j: i32)
    requires
        0 <= j < 26,
        cnt_j == 0,
        cnt_j as int == count_char(s, letter(j)) - count_char(t, letter(j)),
    ensures
        count_char(s, letter(j)) == count_char(t, letter(j)),
{
}

impl Solution {
    pub fn is_anagram(s: String, t: String) -> (res: bool)
        requires
            1 <= s@.len() <= 50_000,
            1 <= t@.len() <= 50_000,
            is_lowercase_word(s@),
            is_lowercase_word(t@),
        ensures
            res == is_anagram_spec(s@, t@),
    {
        let s_len = s.as_str().unicode_len();
        let t_len = t.as_str().unicode_len();
        if s_len != t_len {
            proof {
                assert(!is_anagram_spec(s@, t@));
            }
            return false;
        }
        let mut cnt: Vec<i32> = Vec::new();
        let mut i: usize = 0;
        while i < 26
            invariant
                0 <= i <= 26,
                cnt.len() == i,
                forall |k: int| 0 <= k < i ==> #[trigger] cnt[k] == 0,
            decreases 26 - i
        {
            cnt.push(0);
            i += 1;
        }
        i = 0;
        while i < s_len
            invariant
                is_lowercase_word(s@),
                0 <= i <= s_len,
                s_len <= 50_000,
                s_len as int == s@.len(),
                cnt.len() == 26,
                forall |k: int| 0 <= k < 26 ==> #[trigger] cnt[k] == count_char(s@.take(i as int), letter(k)),
                forall |k: int| 0 <= k < 26 ==> 0 <= #[trigger] cnt[k] <= i as int,
                forall |k: int| 0 <= k < 26 ==> cnt[k] <= 50_000,
            decreases s_len - i
        {
            let c = s.as_str().get_char(i);
            proof {
                assert(s@.index(i as int) == c);
                assert(97 <= c as u32 && c as u32 <= 122);
            }
            let idx = (c as u32 - 97) as usize;
            proof {
                assert(idx < 26);
                let s_take_i = s@.take(i as int);
                let s_take_i1 = s@.take((i + 1) as int);
                assert(s_take_i1.drop_last() =~= s_take_i);
                assert(s_take_i1.last() == c);
                assert(count_char(s_take_i1, letter(idx as int)) == count_char(s_take_i, letter(idx as int)) + 1);
                assert(forall |k: int| 0 <= k < 26 && k != idx ==>
                    #[trigger] count_char(s_take_i1, letter(k)) == count_char(s_take_i, letter(k)));
            }
            cnt.set(idx, cnt[idx] + 1);
            i += 1;
        }
        proof {
            assert(s@.take(s_len as int) =~= s@);
        }
        i = 0;
        while i < t_len
            invariant
                is_lowercase_word(s@),
                is_lowercase_word(t@),
                s_len == t_len,
                0 <= i <= t_len,
                t_len <= 50_000,
                t_len as int == t@.len(),
                cnt.len() == 26,
                forall |k: int| 0 <= k < 26 ==> #[trigger] cnt[k] == count_char(s@, letter(k)) - count_char(t@.take(i as int), letter(k)),
            decreases t_len - i
        {
            let c = t.as_str().get_char(i);
            proof {
                assert(t@.index(i as int) == c);
                assert(97 <= c as u32 && c as u32 <= 122);
            }
            let idx = (c as u32 - 97) as usize;
            proof {
                assert(idx < 26);
                lemma_count_char_nonneg(s@, letter(idx as int));
                lemma_count_char_bounds(t@.take(i as int), letter(idx as int));
                assert(count_char(t@.take(i as int), letter(idx as int)) <= i as int);
                assert(cnt[idx as int] == count_char(s@, letter(idx as int)) - count_char(t@.take(i as int), letter(idx as int)));
                assert(cnt[idx as int] >= -(i as int));
                assert(i <= 50_000);
                assert(cnt[idx as int] >= -50_000);
            }
            proof {
                let t_take_i = t@.take(i as int);
                let t_take_i1 = t@.take((i + 1) as int);
                assert(t_take_i1.drop_last() =~= t_take_i);
                assert(t_take_i1.last() == c);
                assert(count_char(t_take_i1, letter(idx as int)) == count_char(t_take_i, letter(idx as int)) + 1);
                assert(forall |k: int| 0 <= k < 26 && k != idx ==>
                    #[trigger] count_char(t_take_i1, letter(k)) == count_char(t_take_i, letter(k)));
            }
            cnt.set(idx, cnt[idx] - 1);
            i += 1;
        }
        proof {
            assert(t@.take(t_len as int) =~= t@);
        }
        let mut k: usize = 0;
        let mut all_zero = true;
        while k < 26
            invariant
                s_len == t_len,
                s_len as int == s@.len(),
                t_len as int == t@.len(),
                0 <= k <= 26,
                cnt.len() == 26,
                forall |j: int| 0 <= j < 26 ==> cnt[j] == count_char(s@, letter(j)) - count_char(t@, letter(j)),
                all_zero == (forall |j: int| 0 <= j < k as int ==> cnt[j] == 0),
            decreases 26 - k
        {
            if cnt[k] != 0 {
                all_zero = false;
            }
            k += 1;
        }
        proof {
            assert(s@.len() == t_len as int);
            assert(t@.len() == t_len as int);
            assert(s_len == t_len);
            if all_zero {
                lemma_anagram_one(s@, t@, 0, cnt[0]);
                lemma_anagram_one(s@, t@, 1, cnt[1]);
                lemma_anagram_one(s@, t@, 2, cnt[2]);
                lemma_anagram_one(s@, t@, 3, cnt[3]);
                lemma_anagram_one(s@, t@, 4, cnt[4]);
                lemma_anagram_one(s@, t@, 5, cnt[5]);
                lemma_anagram_one(s@, t@, 6, cnt[6]);
                lemma_anagram_one(s@, t@, 7, cnt[7]);
                lemma_anagram_one(s@, t@, 8, cnt[8]);
                lemma_anagram_one(s@, t@, 9, cnt[9]);
                lemma_anagram_one(s@, t@, 10, cnt[10]);
                lemma_anagram_one(s@, t@, 11, cnt[11]);
                lemma_anagram_one(s@, t@, 12, cnt[12]);
                lemma_anagram_one(s@, t@, 13, cnt[13]);
                lemma_anagram_one(s@, t@, 14, cnt[14]);
                lemma_anagram_one(s@, t@, 15, cnt[15]);
                lemma_anagram_one(s@, t@, 16, cnt[16]);
                lemma_anagram_one(s@, t@, 17, cnt[17]);
                lemma_anagram_one(s@, t@, 18, cnt[18]);
                lemma_anagram_one(s@, t@, 19, cnt[19]);
                lemma_anagram_one(s@, t@, 20, cnt[20]);
                lemma_anagram_one(s@, t@, 21, cnt[21]);
                lemma_anagram_one(s@, t@, 22, cnt[22]);
                lemma_anagram_one(s@, t@, 23, cnt[23]);
                lemma_anagram_one(s@, t@, 24, cnt[24]);
                lemma_anagram_one(s@, t@, 25, cnt[25]);
                assert(forall |j: int| 0 <= j < 26 ==> count_char(s@, letter(j)) == count_char(t@, letter(j)));
                assert(is_anagram_spec(s@, t@));
            } else {
                assert(!is_anagram_spec(s@, t@));
            }
        }
        all_zero
    }
}

}
