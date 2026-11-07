use vstd::prelude::*;
use vstd::string::*;

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

pub open spec fn can_form(word: Seq<char>, chars: Seq<char>) -> bool {
    forall |c: u8| 97 <= c && c <= 122 ==> #[trigger] count_char(word, c as char) <= count_char(chars, c as char)
}

pub open spec fn is_lowercase_word(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
}

pub open spec fn good_sum(words: Seq<String>, chars: Seq<char>, k: int) -> int
    decreases k
{
    if k <= 0 {
        0
    } else {
        let word = words[k-1]@;
        let current = if can_form(word, chars) { word.len() as int } else { 0 };
        good_sum(words, chars, k - 1) + current
    }
}

impl Solution {
    pub fn count_characters(words: Vec<String>, chars: String) -> (result: i32)
        requires
            1 <= words.len() <= 1000,
            1 <= chars@.len() <= 100,
            is_lowercase_word(chars@),
            forall |i: int| 0 <= i < words.len() ==> 1 <= #[trigger] words[i]@.len() <= 100 && is_lowercase_word(words[i]@),
        ensures 
            result == good_sum(words@, chars@, words.len() as int),
    {
        let chars_str = chars.as_str();
        let chars_len = chars_str.unicode_len();
        let mut chars_count: Vec<i32> = Vec::new();
        let mut i = 0;
        
        while i < 26 {
            chars_count.push(0);
            i += 1;
        }

        i = 0;
        while i < chars_len {
            let c = chars_str.get_char(i);
            let idx = (c as u32 - 97) as usize;
            chars_count.set(idx, chars_count[idx] + 1);
            i += 1;
        }

        let mut sum: i32 = 0;
        let mut k = 0;
        while k < words.len() {
            let word_str = words[k].as_str();
            let word_len = word_str.unicode_len();
            
            let mut word_count: Vec<i32> = Vec::new();
            let mut j = 0;
            while j < 26 {
                word_count.push(0);
                j += 1;
            }

            j = 0;
            while j < word_len {
                let c = word_str.get_char(j);
                let idx = (c as u32 - 97) as usize;
                word_count.set(idx, word_count[idx] + 1);
                j += 1;
            }

            let mut can = true;
            j = 0;
            while j < 26 {
                if word_count[j] > chars_count[j] {
                    can = false;
                }
                j += 1;
            }

            if can {
                sum += word_len as i32;
            }
            
            k += 1;
        }

        sum
    }
}
}
