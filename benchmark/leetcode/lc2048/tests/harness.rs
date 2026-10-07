pub struct Solution;

impl Solution {
    pub fn next_beautiful_number(n: i32) -> i32 {
        if n < 1 {
            1
        }
        else if n < 22 {
            22
        }
        else if n < 122 {
            122
        }
        else if n < 212 {
            212
        }
        else if n < 221 {
            221
        }
        else if n < 333 {
            333
        }
        else if n < 1333 {
            1333
        }
        else if n < 3133 {
            3133
        }
        else if n < 3313 {
            3313
        }
        else if n < 3331 {
            3331
        }
        else if n < 4444 {
            4444
        }
        else if n < 14444 {
            14444
        }
        else if n < 22333 {
            22333
        }
        else if n < 23233 {
            23233
        }
        else if n < 23323 {
            23323
        }
        else if n < 23332 {
            23332
        }
        else if n < 32233 {
            32233
        }
        else if n < 32323 {
            32323
        }
        else if n < 32332 {
            32332
        }
        else if n < 33223 {
            33223
        }
        else if n < 33232 {
            33232
        }
        else if n < 33322 {
            33322
        }
        else if n < 41444 {
            41444
        }
        else if n < 44144 {
            44144
        }
        else if n < 44414 {
            44414
        }
        else if n < 44441 {
            44441
        }
        else if n < 55555 {
            55555
        }
        else if n < 122333 {
            122333
        }
        else if n < 123233 {
            123233
        }
        else if n < 123323 {
            123323
        }
        else if n < 123332 {
            123332
        }
        else if n < 132233 {
            132233
        }
        else if n < 132323 {
            132323
        }
        else if n < 132332 {
            132332
        }
        else if n < 133223 {
            133223
        }
        else if n < 133232 {
            133232
        }
        else if n < 133322 {
            133322
        }
        else if n < 155555 {
            155555
        }
        else if n < 212333 {
            212333
        }
        else if n < 213233 {
            213233
        }
        else if n < 213323 {
            213323
        }
        else if n < 213332 {
            213332
        }
        else if n < 221333 {
            221333
        }
        else if n < 223133 {
            223133
        }
        else if n < 223313 {
            223313
        }
        else if n < 223331 {
            223331
        }
        else if n < 224444 {
            224444
        }
        else if n < 231233 {
            231233
        }
        else if n < 231323 {
            231323
        }
        else if n < 231332 {
            231332
        }
        else if n < 232133 {
            232133
        }
        else if n < 232313 {
            232313
        }
        else if n < 232331 {
            232331
        }
        else if n < 233123 {
            233123
        }
        else if n < 233132 {
            233132
        }
        else if n < 233213 {
            233213
        }
        else if n < 233231 {
            233231
        }
        else if n < 233312 {
            233312
        }
        else if n < 233321 {
            233321
        }
        else if n < 242444 {
            242444
        }
        else if n < 244244 {
            244244
        }
        else if n < 244424 {
            244424
        }
        else if n < 244442 {
            244442
        }
        else if n < 312233 {
            312233
        }
        else if n < 312323 {
            312323
        }
        else if n < 312332 {
            312332
        }
        else if n < 313223 {
            313223
        }
        else if n < 313232 {
            313232
        }
        else if n < 313322 {
            313322
        }
        else if n < 321233 {
            321233
        }
        else if n < 321323 {
            321323
        }
        else if n < 321332 {
            321332
        }
        else if n < 322133 {
            322133
        }
        else if n < 322313 {
            322313
        }
        else if n < 322331 {
            322331
        }
        else if n < 323123 {
            323123
        }
        else if n < 323132 {
            323132
        }
        else if n < 323213 {
            323213
        }
        else if n < 323231 {
            323231
        }
        else if n < 323312 {
            323312
        }
        else if n < 323321 {
            323321
        }
        else if n < 331223 {
            331223
        }
        else if n < 331232 {
            331232
        }
        else if n < 331322 {
            331322
        }
        else if n < 332123 {
            332123
        }
        else if n < 332132 {
            332132
        }
        else if n < 332213 {
            332213
        }
        else if n < 332231 {
            332231
        }
        else if n < 332312 {
            332312
        }
        else if n < 332321 {
            332321
        }
        else if n < 333122 {
            333122
        }
        else if n < 333212 {
            333212
        }
        else if n < 333221 {
            333221
        }
        else if n < 422444 {
            422444
        }
        else if n < 424244 {
            424244
        }
        else if n < 424424 {
            424424
        }
        else if n < 424442 {
            424442
        }
        else if n < 442244 {
            442244
        }
        else if n < 442424 {
            442424
        }
        else if n < 442442 {
            442442
        }
        else if n < 444224 {
            444224
        }
        else if n < 444242 {
            444242
        }
        else if n < 444422 {
            444422
        }
        else if n < 515555 {
            515555
        }
        else if n < 551555 {
            551555
        }
        else if n < 555155 {
            555155
        }
        else if n < 555515 {
            555515
        }
        else if n < 555551 {
            555551
        }
        else if n < 666666 {
            666666
        }
        else {
            1224444
        }
    }
}

use std::io::{self, BufRead, Write, BufWriter};

trait StrExt {
    fn unicode_len(&self) -> usize;
    fn get_char(&self, i: usize) -> char;
}
impl StrExt for str {
    fn unicode_len(&self) -> usize { self.chars().count() }
    fn get_char(&self, i: usize) -> char { self.chars().nth(i).unwrap() }
}

trait VecExt<T> {
    fn set(&mut self, i: usize, val: T);
}
impl<T> VecExt<T> for Vec<T> {
    fn set(&mut self, i: usize, val: T) { self[i] = val; }
}

fn find_key<'a>(line: &'a str, key: &str) -> &'a str {
    let pat = format!("\"{}\"", key);
    let start = line.find(&pat).expect(&format!("key '{}' not found", key));
    let after_key = &line[start + pat.len()..];
    let colon = after_key.find(':').expect("no colon after key") + 1;
    let rest = after_key[colon..].trim_start();
    rest
}

fn extract_value<'a>(s: &'a str) -> &'a str {
    let s = s.trim_start();
    if s.starts_with('"') {
        let end = s[1..].find('"').expect("unterminated string") + 2;
        let after = s[end..].trim_start();
        if after.starts_with(',') || after.starts_with('}') || after.is_empty() {
            return &s[..end];
        }
        &s[..end]
    } else if s.starts_with('[') {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '[' => depth += 1,
                ']' => { depth -= 1; if depth == 0 { return &s[..i+1]; } }
                _ => {}
            }
        }
        s
    } else if s.starts_with('{') {
        let mut depth = 0;
        for (i, c) in s.char_indices() {
            match c {
                '{' => depth += 1,
                '}' => { depth -= 1; if depth == 0 { return &s[..i+1]; } }
                _ => {}
            }
        }
        s
    } else {
        let end = s.find(|c: char| c == ',' || c == '}' || c == ']').unwrap_or(s.len());
        s[..end].trim_end()
    }
}

fn get_field<'a>(line: &'a str, key: &str) -> &'a str {
    let rest = find_key(line, key);
    extract_value(rest)
}

trait ParseNum: Sized {
    fn parse_from(s: &str) -> Self;
}
macro_rules! impl_parse_num {
    ($($t:ty),*) => { $(
        impl ParseNum for $t {
            fn parse_from(s: &str) -> Self { s.trim().parse().expect(&format!("bad number: {}", s)) }
        }
    )* }
}
impl_parse_num!(i32, i64, i128, u32, u64, u128, usize, isize, u8);

fn parse_number<T: ParseNum>(s: &str) -> T {
    let s = s.trim();
    if s == "null" || s == "true" {
        T::parse_from("1")
    } else if s == "false" {
        T::parse_from("0")
    } else {
        T::parse_from(s)
    }
}

fn parse_bool(s: &str) -> bool {
    let s = s.trim();
    s == "true" || s == "1"
}

fn parse_string(s: &str) -> String {
    let s = s.trim();
    if s.starts_with('"') && s.ends_with('"') {
        s[1..s.len()-1].to_string()
    } else {
        s.to_string()
    }
}

fn parse_num_array<T: ParseNum>(s: &str) -> Vec<T> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let inner = &s[1..s.len()-1];
    inner.split(',').map(|x| T::parse_from(x.trim())).collect()
}

fn parse_bool_array(s: &str) -> Vec<bool> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let inner = &s[1..s.len()-1];
    inner.split(',').map(|x| parse_bool(x.trim())).collect()
}

fn parse_string_array(s: &str) -> Vec<String> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut in_str = false;
    let mut cur = String::new();
    let mut chars = inner.chars();
    while let Some(c) = chars.next() {
        if c == '"' {
            if in_str {
                result.push(cur.clone());
                cur.clear();
                in_str = false;
            } else {
                in_str = true;
            }
        } else if in_str {
            cur.push(c);
        }
    }
    result
}

fn parse_2d_num_array<T: ParseNum>(s: &str) -> Vec<Vec<T>> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_num_array(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn parse_2d_bool_array(s: &str) -> Vec<Vec<bool>> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_bool_array(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn parse_2d_string_array(s: &str) -> Vec<Vec<String>> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_string_array(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn parse_tuple2<A: ParseNum, B: ParseNum>(s: &str) -> (A, B) {
    let s = s.trim();
    let inner = &s[1..s.len()-1];
    let parts: Vec<&str> = inner.splitn(2, ',').collect();
    (A::parse_from(parts[0].trim()), B::parse_from(parts[1].trim()))
}

fn parse_tuple2_array<A: ParseNum, B: ParseNum>(s: &str) -> Vec<(A, B)> {
    let s = s.trim();
    if s == "[]" { return Vec::new(); }
    let mut result = Vec::new();
    let inner = &s[1..s.len()-1];
    let mut depth = 0;
    let mut start = 0;
    for (i, c) in inner.char_indices() {
        match c {
            '[' => { if depth == 0 { start = i; } depth += 1; }
            ']' => { depth -= 1; if depth == 0 { result.push(parse_tuple2(&inner[start..i+1])); } }
            _ => {}
        }
    }
    result
}

fn format_json_string(s: &str) -> String {
    format!("\"{}\"", s.replace('\\', "\\\\").replace('"', "\\\""))
}

fn format_num_array<T: std::fmt::Display>(v: &[T]) -> String {
    let parts: Vec<String> = v.iter().map(|x| x.to_string()).collect();
    format!("[{}]", parts.join(","))
}

fn format_bool_array(v: &[bool]) -> String {
    let parts: Vec<&str> = v.iter().map(|b| if *b { "true" } else { "false" }).collect();
    format!("[{}]", parts.join(","))
}

fn format_string_array(v: &[String]) -> String {
    let parts: Vec<String> = v.iter().map(|s| format_json_string(s)).collect();
    format!("[{}]", parts.join(","))
}

fn format_2d_num_array<T: std::fmt::Display>(v: &[Vec<T>]) -> String {
    let parts: Vec<String> = v.iter().map(|row| format_num_array(row)).collect();
    format!("[{}]", parts.join(","))
}

fn format_2d_bool_array(v: &[Vec<bool>]) -> String {
    let parts: Vec<String> = v.iter().map(|row| format_bool_array(row)).collect();
    format!("[{}]", parts.join(","))
}

fn main() {
    let stdin = io::stdin();
    let stdout = io::stdout();
    let mut out = BufWriter::new(stdout.lock());
    for line in stdin.lock().lines() {
        let line = line.expect("read line");
        let line = line.trim();
        if line.is_empty() || !line.starts_with('{') { continue; }
        let n: i32 = parse_number::<i32>(get_field(line, "n"));
        let _f0 = format!("\"n\": {}", n);
        let result = Solution::next_beautiful_number(n);
        let _out = format!("\"output\": {}", result);
        let _all = vec![_f0, _out];
        write!(out, "{{").unwrap();
        for (i, part) in _all.iter().enumerate() {
            if i > 0 { write!(out, ", ").unwrap(); }
            write!(out, "{}", part).unwrap();
        }
        writeln!(out, "}}").unwrap();
    }
}
