pub struct Solution;

fn merge_exec(a: &Vec<i64>, b: &Vec<i64>) -> Vec<i64> {
    let mut result: Vec<i64> = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    while i < a.len() || j < b.len() {
        if j >= b.len() || (i < a.len() && a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    result
}

fn merge_sort_exec(v: &Vec<i64>) -> Vec<i64> {
    if v.len() <= 1 {
        let mut result: Vec<i64> = Vec::new();
        let mut k: usize = 0;
        while k < v.len() {
            result.push(v[k]);
            k += 1;
        }
        result
    } else {
        let mid = v.len() / 2;
        let mut left: Vec<i64> = Vec::new();
        let mut i: usize = 0;
        while i < mid {
            left.push(v[i]);
            i += 1;
        }
        let mut right: Vec<i64> = Vec::new();
        let mut i2: usize = mid;
        while i2 < v.len() {
            right.push(v[i2]);
            i2 += 1;
        }
        let sorted_left = merge_sort_exec(&left);
        let sorted_right = merge_sort_exec(&right);
        let result = merge_exec(&sorted_left, &sorted_right);
        result
    }
}

fn encode_exec(v: i32, i: usize) -> i64 {
    (v as i64) * 200000 + (i as i64)
}

fn decode_idx_exec(e: i64) -> i64 {
    e % 200000
}

impl Solution {
    pub fn unmarked_sum_array(nums: Vec<i32>, queries: Vec<Vec<i32>>) -> Vec<i64> {
        let n = nums.len();

        let mut enc: Vec<i64> = Vec::new();
        let mut ii: usize = 0;
        while ii < n {
            let e = encode_exec(nums[ii], ii);
            enc.push(e);
            ii += 1;
        }
        let sorted = merge_sort_exec(&enc);

        let mut marked: Vec<bool> = Vec::new();
        let mut jj: usize = 0;
        while jj < n {
            marked.push(false);
            jj += 1;
        }

        let mut total: i64 = 0;
        let mut pp: usize = 0;
        while pp < n {
            total = total + nums[pp] as i64;
            pp += 1;
        }
        let mut unmarked_sum: i64 = total;

        let mut ptr: usize = 0;
        let mut result: Vec<i64> = Vec::new();
        let mut q: usize = 0;
        while q < queries.len() {
            let idx = queries[q][0] as usize;
            let k = queries[q][1];
            if !marked[idx] {
                marked[idx] = true;
                unmarked_sum = unmarked_sum - nums[idx] as i64;
            }

            let mut t: i32 = 0;
            while t < k && ptr < n {
                let mut cont: bool = false;
                if ptr < n {
                    let sp = sorted[ptr];
                    let di = decode_idx_exec(sp);
                    cont = marked[di as usize];
                }
                while cont {
                    ptr += 1;
                    cont = false;
                    if ptr < n {
                        let sp = sorted[ptr];
                        let di = decode_idx_exec(sp);
                        cont = marked[di as usize];
                    }
                }
                if ptr < n {
                    let sp2 = sorted[ptr];
                    let di2 = decode_idx_exec(sp2);
                    let target = di2 as usize;
                    marked[target] = true;
                    unmarked_sum = unmarked_sum - nums[target] as i64;
                    ptr += 1;
                }
                t += 1;
            }

            result.push(unmarked_sum);
            q += 1;
        }

        result
    }
}

use std::io::{self, BufRead, Write, BufWriter};

// Stand-ins for vstd's exec helpers when code.rs is compiled with rustc. Under
// Verus (cfg verus_keep_ghost) vstd provides them and these would be ambiguous.
#[cfg(not(verus_keep_ghost))]
trait StrExt {
    fn unicode_len(&self) -> usize;
    fn get_char(&self, i: usize) -> char;
}
#[cfg(not(verus_keep_ghost))]
impl StrExt for str {
    fn unicode_len(&self) -> usize { self.chars().count() }
    fn get_char(&self, i: usize) -> char { self.chars().nth(i).unwrap() }
}

#[cfg(not(verus_keep_ghost))]
trait VecExt<T> {
    fn set(&mut self, i: usize, val: T);
}
#[cfg(not(verus_keep_ghost))]
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

fn parse_char_vec(s: &str) -> Vec<char> {
    parse_string(s).chars().collect()
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

fn format_char_vec(v: &[char]) -> String {
    format_json_string(&v.iter().collect::<String>())
}

fn format_2d_num_array<T: std::fmt::Display>(v: &[Vec<T>]) -> String {
    let parts: Vec<String> = v.iter().map(|row| format_num_array(row)).collect();
    format!("[{}]", parts.join(","))
}

fn format_2d_bool_array(v: &[Vec<bool>]) -> String {
    let parts: Vec<String> = v.iter().map(|row| format_bool_array(row)).collect();
    format!("[{}]", parts.join(","))
}

fn format_tuple2_array_json<T: std::fmt::Display, U: std::fmt::Display>(v: &[(T, U)]) -> String {
    let parts: Vec<String> = v.iter().map(|(a, b)| format!("[{},{}]", a, b)).collect();
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
        let queries: Vec<Vec<i32>> = parse_2d_num_array::<i32>(get_field(line, "queries"));
        let _f0 = format!("\"nums\": {}", format_num_array(&nums));
        let _f1 = format!("\"queries\": {}", format_2d_num_array(&queries));
        let result = Solution::unmarked_sum_array(nums, queries);
        let _out = format!("\"output\": {}", format_num_array(&result));
        let _all = vec![_f0, _f1, _out];
        write!(out, "{{").unwrap();
        for (i, part) in _all.iter().enumerate() {
            if i > 0 { write!(out, ", ").unwrap(); }
            write!(out, "{}", part).unwrap();
        }
        writeln!(out, "}}").unwrap();
    }
}
