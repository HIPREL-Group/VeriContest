pub struct Solution;

impl Solution {
    pub fn max_operations(nums: Vec<i32>) -> i32 {
        let n = nums.len();
        if n <= 3 {
            return 1;
        }
        let s1 = nums[0] + nums[1];
        let s2 = nums[0] + nums[n - 1];
        let s3 = nums[n - 2] + nums[n - 1];
        let dp1 = Self::solve_fixed(&nums, s1);
        let dp2 = Self::solve_fixed(&nums, s2);
        let dp3 = Self::solve_fixed(&nums, s3);
        let a = 1 + dp1[2][n - 1];
        let b = 1 + dp2[1][n - 2];
        let c = 1 + dp3[0][n - 3];
        let ans = Self::best3_exec(a, b, c);
        ans
    }

    fn solve_fixed(nums: &Vec<i32>, target: i32) -> Vec<Vec<i32>> {
        let n = nums.len();
        let mut dp: Vec<Vec<i32>> = Vec::new();
        let mut i: usize = 0;
        while i < n {
            let mut row: Vec<i32> = Vec::new();
            let mut j: usize = 0;
            while j < n {
                row.push(0);
                j = j + 1;
            }
            dp.push(row);
            i = i + 1;
        }

        let mut len: usize = 2;
        while len <= n {
            let mut l: usize = 0;
            while l + len <= n {
                let r = l + len - 1;
                let mut a: i32 = 0;
                if nums[l] + nums[l + 1] == target {
                    let child: i32;
                    if len > 3 {
                        child = dp[l + 2][r];
                    } else {
                        child = 0;
                    }
                    a = 1 + child;
                }
                let mut b: i32 = 0;
                if nums[l] + nums[r] == target {
                    let child: i32;
                    if len > 3 {
                        child = dp[l + 1][r - 1];
                    } else {
                        child = 0;
                    }
                    b = 1 + child;
                }
                let mut c: i32 = 0;
                if nums[r - 1] + nums[r] == target {
                    let child: i32;
                    if len > 3 {
                        child = dp[l][r - 2];
                    } else {
                        child = 0;
                    }
                    c = 1 + child;
                }
                let val = Self::best3_exec(a, b, c);
                let mut row = dp[l].clone();
                row[r] = val;
                dp[l] = row;
                l = l + 1;
            }
            len = len + 1;
        }
        dp
    }

    fn best_exec(a: i32, b: i32) -> i32 {
        if a >= b { a } else { b }
    }

    fn best3_exec(a: i32, b: i32, c: i32) -> i32 {
        Self::best_exec(a, Self::best_exec(b, c))
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
        let nums: Vec<i32> = parse_num_array::<i32>(get_field(line, "nums"));
        let _f0 = format!("\"nums\": {}", format_num_array(&nums));
        let result = Solution::max_operations(nums);
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
