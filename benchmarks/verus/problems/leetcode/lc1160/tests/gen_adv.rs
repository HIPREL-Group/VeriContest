use vstd::prelude::*;

verus! {

pub open spec fn is_lowercase_word(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> 97 <= (#[trigger] s[i] as u32) && (s[i] as u32) <= 122
}

pub open spec fn valid_words(words: Seq<Seq<char>>) -> bool {
    forall |i: int| 0 <= i < words.len() ==> 1 <= #[trigger] words[i].len() <= 100 && is_lowercase_word(words[i])
}

pub fn generate_test_case(
    chars_len: usize,
    word_count: usize,
    word_len: usize,
    chars_fill: char,
    word_fill: char,
) -> (out: (Vec<Vec<char>>, Vec<char>))
    requires
        1 <= chars_len <= 100,
        1 <= word_count <= 1000,
        1 <= word_len <= 100,
        chars_fill == 'a' || chars_fill == 'b' || chars_fill == 'c' || chars_fill == 'd' || chars_fill == 'z',
        word_fill == 'a' || word_fill == 'b' || word_fill == 'c' || word_fill == 'd' || word_fill == 'z',
    ensures
        1 <= out.1@.len() <= 100,
        is_lowercase_word(out.1@),
        1 <= out.0@.len() <= 1000,
        forall |i: int| 0 <= i < out.0@.len() ==> 1 <= #[trigger] out.0@[i].len() <= 100,
        forall |i: int, j: int| 0 <= i < out.0@.len() && 0 <= j < out.0@[i].len() ==>
            97 <= (#[trigger] out.0@[i][j] as u32) && (out.0@[i][j] as u32) <= 122,
{
    let mut chars: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < chars_len
        invariant
            1 <= chars_len <= 100,
            chars.len() == i,
            0 <= i <= chars_len,
            chars_fill == 'a' || chars_fill == 'b' || chars_fill == 'c' || chars_fill == 'd' || chars_fill == 'z',
            forall |k: int| 0 <= k < chars.len() ==> #[trigger] chars[k] == chars_fill,
            forall |k: int| 0 <= k < chars.len() ==> 97 <= (#[trigger] chars[k] as u32) && (chars[k] as u32) <= 122,
        decreases chars_len - i,
    {
        chars.push(chars_fill);
        i += 1;
    }

    let mut words: Vec<Vec<char>> = Vec::new();
    let mut wi: usize = 0;
    while wi < word_count
        invariant
            1 <= word_count <= 1000,
            1 <= word_len <= 100,
            words.len() == wi,
            0 <= wi <= word_count,
            word_fill == 'a' || word_fill == 'b' || word_fill == 'c' || word_fill == 'd' || word_fill == 'z',
            forall |k: int| 0 <= k < words.len() ==> 1 <= #[trigger] words[k].len() <= 100,
            forall |k: int, j: int| 0 <= k < words.len() && 0 <= j < words[k].len() ==>
                words[k][j] == word_fill,
            forall |k: int, j: int| 0 <= k < words.len() && 0 <= j < words[k].len() ==>
                97 <= (#[trigger] words[k][j] as u32) && (words[k][j] as u32) <= 122,
        decreases word_count - wi,
    {
        let mut w: Vec<char> = Vec::new();
        let mut j: usize = 0;
        while j < word_len
            invariant
                1 <= word_len <= 100,
                w.len() == j,
                0 <= j <= word_len,
                word_fill == 'a' || word_fill == 'b' || word_fill == 'c' || word_fill == 'd' || word_fill == 'z',
                forall |k: int| 0 <= k < w.len() ==> #[trigger] w[k] == word_fill,
                forall |k: int| 0 <= k < w.len() ==> 97 <= (#[trigger] w[k] as u32) && (w[k] as u32) <= 122,
            decreases word_len - j,
        {
            w.push(word_fill);
            j += 1;
        }
        words.push(w);
        wi += 1;
    }

    (words, chars)
}

} // verus!

struct Rng {
    state: u64,
}

impl Rng {
    fn new(seed: u64) -> Self {
        Self { state: seed }
    }

    fn next_u64(&mut self) -> u64 {
        self.state = self
            .state
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        self.state
    }

    fn gen_range_usize(&mut self, lo: usize, hi: usize) -> usize {
        assert!(lo <= hi);
        let span = hi - lo + 1;
        lo + (self.next_u64() as usize % span)
    }
}

fn vec_chars_to_json(v: &[char]) -> String {
    let mut s = String::new();
    s.push('"');
    for &c in v {
        s.push(c);
    }
    s.push('"');
    s
}

fn words_to_json(words: &[Vec<char>]) -> String {
    let mut s = String::new();
    s.push('[');
    for i in 0..words.len() {
        if i > 0 {
            s.push(',');
        }
        s.push_str(&vec_chars_to_json(&words[i]));
    }
    s.push(']');
    s
}

fn choose_mode_params(rng: &mut Rng, mode: usize, t: usize) -> (usize, usize, usize, char, char) {
    match mode {
        0 => (1, 1, 1, 'a', 'a'),
        1 => (100, 1000, 100, 'z', 'z'),
        2 => (100, 1000, 1, 'a', 'z'),
        3 => (1, 1000, 100, 'b', 'a'),
        4 => (100, 1, 100, 'c', 'c'),
        5 => (2 + (t % 99), 2 + (t % 999), 2 + (t % 99), 'd', 'b'),
        6 => (100, 37, 100, 'a', 'a'),
        7 => (1, 37, 1, 'z', 'a'),
        8 => (
            rng.gen_range_usize(1, 100),
            rng.gen_range_usize(1, 1000),
            rng.gen_range_usize(1, 100),
            ['a', 'b', 'c', 'd', 'z'][rng.gen_range_usize(0, 4)],
            ['a', 'b', 'c', 'd', 'z'][rng.gen_range_usize(0, 4)],
        ),
        9 => (99, 999, 99, 'b', 'z'),
        _ => (50, 500, 50, 'c', 'a'),
    }
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let seed = if args.len() > 1 {
        args[1].parse::<u64>().unwrap_or(1)
    } else {
        1
    };

    let mut rng = Rng::new(seed);
    let total = 200usize;
    let modes = 11usize;

    for t in 0..total {
        let mode = t % modes;
        let (chars_len, word_count, word_len, chars_fill, word_fill) =
            choose_mode_params(&mut rng, mode, t);

        let (words, chars) =
            generate_test_case(chars_len, word_count, word_len, chars_fill, word_fill);

        let words_json = words_to_json(&words);
        let chars_json = vec_chars_to_json(&chars);
        println!("{{\"words\":{},\"chars\":{}}}", words_json, chars_json);
    }
}