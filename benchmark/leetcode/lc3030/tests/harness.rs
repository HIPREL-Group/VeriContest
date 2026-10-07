pub struct Solution;

impl Solution {
    fn abs_diff_exec(a: i32, b: i32) -> i32 {
        if a >= b { a - b } else { b - a }
    }

    fn region_valid_exec(image: &Vec<Vec<i32>>, threshold: i32, i: usize, j: usize) -> bool {
        Self::abs_diff_exec(image[i][j], image[i][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i][j + 1], image[i][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j], image[i + 1][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j + 1], image[i + 1][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i + 2][j], image[i + 2][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i + 2][j + 1], image[i + 2][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i][j], image[i + 1][j]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j], image[i + 2][j]) <= threshold
            && Self::abs_diff_exec(image[i][j + 1], image[i + 1][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j + 1], image[i + 2][j + 1]) <= threshold
            && Self::abs_diff_exec(image[i][j + 2], image[i + 1][j + 2]) <= threshold
            && Self::abs_diff_exec(image[i + 1][j + 2], image[i + 2][j + 2]) <= threshold
    }

    fn region_avg_exec(image: &Vec<Vec<i32>>, i: usize, j: usize) -> i32 {
        (
            image[i][j] + image[i][j + 1] + image[i][j + 2]
            + image[i + 1][j] + image[i + 1][j + 1] + image[i + 1][j + 2]
            + image[i + 2][j] + image[i + 2][j + 1] + image[i + 2][j + 2]
        ) / 9
    }

    pub fn result_grid(image: Vec<Vec<i32>>, threshold: i32) -> Vec<Vec<i32>> {
        let rows = image.len();
        let cols = image[0].len();

        let mut result: Vec<Vec<i32>> = Vec::new();
        let mut r: usize = 0;
        while r < rows {
            let mut row: Vec<i32> = Vec::new();
            let mut c: usize = 0;
            while c < cols {
                let row_lo = if r >= 2 { r - 2 } else { 0 };
                let row_hi = if r + 2 < rows { r } else { rows - 3 };
                let col_lo = if c >= 2 { c - 2 } else { 0 };
                let col_hi = if c + 2 < cols { c } else { cols - 3 };

                let mut sum_avg: i32 = 0;
                let mut cnt: i32 = 0;

                let mut si = row_lo;
                while si <= row_hi {
                    let mut sj = col_lo;
                    while sj <= col_hi {
                        let ok = Self::region_valid_exec(&image, threshold, si, sj);
                        if ok {
                            let avg = Self::region_avg_exec(&image, si, sj);
                            sum_avg = sum_avg + avg;
                            cnt = cnt + 1;
                        }
                        sj = sj + 1;
                    }
                    si = si + 1;
                }

                let cell: i32;
                if cnt == 0 {
                    cell = image[r][c];
                } else {
                    cell = sum_avg / cnt;
                }

                row.push(cell);
                c = c + 1;
            }
            result.push(row);
            r = r + 1;
        }
        result
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
        let image: Vec<Vec<i32>> = parse_2d_num_array::<i32>(get_field(line, "image"));
        let threshold: i32 = parse_number::<i32>(get_field(line, "threshold"));
        let _f0 = format!("\"image\": {}", format_2d_num_array(&image));
        let _f1 = format!("\"threshold\": {}", threshold);
        let result = Solution::result_grid(image, threshold);
        let _out = format!("\"output\": {}", format_2d_num_array(&result));
        let _all = vec![_f0, _f1, _out];
        write!(out, "{{").unwrap();
        for (i, part) in _all.iter().enumerate() {
            if i > 0 { write!(out, ", ").unwrap(); }
            write!(out, "{}", part).unwrap();
        }
        writeln!(out, "}}").unwrap();
    }
}
